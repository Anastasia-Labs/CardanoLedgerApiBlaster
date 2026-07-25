/-
WSC/Shaped/MintingDelegateShapedR.lean — **SHAPES DT1R and DS1R: the
NODE-REALIZABLE re-cuts of SHAPE DT1 and SHAPE DS1**, the issuance policy's two
DELEGATING custody arms (task C2).

════════════════════════════════════════════════════════════════════════════
WHY THESE TWO CANNOT SHRINK TO ONE WITHDRAWAL — the validator says so
════════════════════════════════════════════════════════════════════════════
SHAPE M1R and SHAPE L1R shrink to a SINGLE script withdrawal because the
`BurnOnly` and `Local` arms read the withdrawal map exactly once (C1). The two
delegating arms are different, and this is where the task's instruction "make
withdrawal entries PUBKEY wherever the validator does not dereference a script"
gets its answer from the source rather than from taste:

* **`DelegateTransfer`** (Issuance.hs:200-219) has TWO withdrawal reads —
  `mintingLogicInvokedAt # wdrlIdx` (:216, defined :150-151 against
  `PScriptCredential mintingLogicHash'` at :136) **and** `globalInvoked` (:210-211),
  `(pfstBuiltin # (phead # (pcheckedDrop # pfromData globalWdrlIdx #
  withdrawalEntries))) #== pglobalLogicCred`, where `pglobalLogicCred` comes from
  the params datum and is a `PScriptCredential`. So **two SCRIPT withdrawals are
  the floor**: `wdrl[0]` = the minting-logic credential, `wdrl[1]` = the global
  transfer validator's credential. Neither can be a pubkey entry without making
  the arm unsatisfiable.
* **`DelegateSeize`** (Issuance.hs:221-245) reads the withdrawal map once (C1,
  :242) but ALSO reads the REDEEMER MAP: `seizeEntry = phead # (pcheckedDrop #
  pfromData seizeRedeemerIdx # pto (pfromData ptxInfo'redeemers))` (:235), and
  requires that entry to be `PRewarding seizeCred` with
  `pdata seizeCred #== pseizeLogicCred` (:238-240). A `Rewarding` redeemer entry
  whose reward account is NOT withdrawn from is an EXTRA redeemer (the other half
  of the Conway rule), so a realizable DS1 must ALSO carry the seize credential in
  the withdrawal map. Two script withdrawals again — and now the seize credential
  is `w1`, not a free-floating `sCred`.

  **THIS IS A STRENGTHENING, NOT A CONCESSION.** SHAPE DS1 let `sCred` float free
  of the withdrawal map, which is precisely what made its two-entry redeemer map
  still short of coverage (`ShapeRealizability.ds1_uncovered_wdrl_exists`). Tying
  the seize credential to a withdrawal is what a real seize-delegating mint looks
  like.

════════════════════════════════════════════════════════════════════════════
THE RE-CUT, IN ONE TABLE
════════════════════════════════════════════════════════════════════════════
| | DT1 | **DT1R** | DS1 | **DS1R** |
|---|---|---|---|---|
| script inputs | 0 | **0** | 0 | **0** |
| mint policies | 1 | **1** | 1 | **1** |
| script withdrawals | 2 | **2** | 2 | **2** |
| redeemer entries | 1 | **3** | 2 | **3** |
| covered? | 1 ≠ 3 ✗ | **3 = 3 ✓** | 2 ≠ 3 ✗ | **3 = 3 ✓** |

Both are one entry short of `mint-delegate-transfer-topup`'s 5, because that
golden spends a SCRIPT input and carries a third withdrawal; the shapes here keep
SHAPE L1's single PUBKEY input, so their exact-coverage count is 3.

════════════════════════════════════════════════════════════════════════════
WHAT STAYS FREE — the two facts each arm has to earn
════════════════════════════════════════════════════════════════════════════
* DT1R: `w0`, `w1` are free and `validWithdrawals` constrains them only to be
  sorted, while the params datum's `glc` is a THIRD free variable and the applied
  parameter `mlh` a FOURTH. So "the minting-logic credential is at index 0" and
  "the GLOBAL credential is at index 1" are both earned.
* DS1R: **`sIdx`, the `SeizeAct`'s own `plgrDirectoryNodeIdx`, is FREE** — the arm's
  whole job is to bind the seize's scope to `ownCS`'s directory node by requiring
  `pdirectoryNodeIdx #== pfromData nodeRefIdx` (:238), and pinning `sIdx = 1` would
  make that conjunct `rfl`-true and the theorem empty. It stays free here exactly as
  in SHAPE DS1. The seize credential is `w1`, free, compared against the params
  datum's `slc`, a different free variable — so `pdata seizeCred #== pseizeLogicCred`
  is earned too.
* Both: registration by REFERENCE INPUT ONLY (F-1, :204-206 / :227-229) with the
  node's `nCS`/`nTn`/`nQty` free and `dirCS` a different free variable, and the
  params node's `pCS` different from the script parameter `ppCS`.

REDEEMER INDEX. SHAPE DS1 pinned `mrSeizeRedeemerIdx = 1`; SHAPE DS1R pins it to
**2**, because coverage puts the minting-logic `Rewarding` entry at index 1 and the
seize `Rewarding` entry at index 2. The index is a self-validating hint (the branch
re-checks the entry it selects, :238-240), so this is inside the shaping doctrine.

REDEEMER-MAP ORDER. `[Minting ownCS, Rewarding (SC w0), Rewarding (SC w1)]` is
sorted under CLAB's corrected `ltScriptPurpose` iff `w0 < w1`, which
`validWithdrawals` already forces on the withdrawal map — so `validRedeemerMap`
adds NO new side condition beyond the one SHAPE DT1/DS1 already carried.
-/
import WSC.Shaped.MintingLocalShapedR
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals ScriptPurpose mintingInputs findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- The two-entry, both-SCRIPT withdrawal map the delegating arms require. Same
as SHAPE L1's `localShapedWdrl`; named separately so the R-shapes are readable
standalone. -/
def delegateRWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-! ## SHAPE DT1R — the `DelegateTransfer` arm, redeemer-covered -/

/-- SHAPE DT1R's own redeemer: `DelegateTransfer 0 0 1 1` — unchanged from DT1. -/
def dtRRedeemer : Data := IsData.toData (MintRedeemer.DelegateTransfer 0 0 1 1)

theorem dtRRedeemer_eq : dtRRedeemer = Data.Constr 1 [Data.I 0, Data.I 0, Data.I 1, Data.I 1] := by
  native_decide

/-- **SHAPE DT1R's redeemer map**: the own `Minting` entry plus ONE `Rewarding`
entry per script withdrawal — the minting-logic script at index 1 and the global
transfer validator at index 2. Both payloads are free leaves; the issuance policy
decodes neither on this arm. -/
def dtRRedeemerMap (ownCS : CurrencySymbol) (w0 w1 : ScriptHash) (mlRed glRed : ByteString)
    : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, dtRRedeemer)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed)
  , (.Rewarding (.ScriptCredential w1), Data.B glRed) ]

/-- **SHAPE DT1R.** SHAPE L1's reference inputs / outputs / input / mint verbatim. -/
def dtRCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaPlusOne inAda ownCS tn qIn
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨⟨ByteString.mk "", 0⟩, resolved⟩]
      , txInfoReferenceInputs :=
          [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1
      , txInfoFee := fee
      , txInfoMint := mintOne ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := delegateRWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := dtRRedeemerMap ownCS w0 w1 mlRed glRed
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := dtRRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

def dtRInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)

#prep_uplc appliedMintDTRShaped2500 programmableTokenMinting900 dtRInputs 2500

/-! ## SHAPE DS1R — the `DelegateSeize` arm, redeemer-covered -/

/-- SHAPE DS1R's own redeemer: `DelegateSeize 0 0 1 2`. The last field is
`mrSeizeRedeemerIdx`, moved from 1 (SHAPE DS1) to **2** because coverage inserts
the minting-logic `Rewarding` entry at index 1. -/
def dsRRedeemer : Data := IsData.toData (MintRedeemer.DelegateSeize 0 0 1 2)

theorem dsRRedeemer_eq : dsRRedeemer = Data.Constr 2 [Data.I 0, Data.I 0, Data.I 1, Data.I 2] := by
  native_decide

/-- The `SeizeAct` carried by the seize validator's own redeemer entry. Its
`plgrDirectoryNodeIdx` is the FREE leaf `sIdx` — see the module header for why
freeing it is the point of this shape. -/
def dsRSeizeRedeemer (sIdx : Integer) : Data :=
  IsData.toData (PLGRedeemer.SeizeAct sIdx [] 0 0 0 0)

theorem dsRSeizeRedeemer_eq (sIdx : Integer) :
    dsRSeizeRedeemer sIdx
      = Data.Constr 1 [Data.I sIdx, Data.List [], Data.I 0, Data.I 0, Data.I 0, Data.I 0] := rfl

/-- **SHAPE DS1R's redeemer map**: `Minting ownCS` at index 0, the minting-logic
script's `Rewarding w0` at index 1, and the SEIZE validator's `Rewarding w1`
carrying the `SeizeAct` at index 2 — which is what `mrSeizeRedeemerIdx = 2`
names. -/
def dsRRedeemerMap (ownCS : CurrencySymbol) (w0 w1 : ScriptHash) (mlRed : ByteString)
    (sIdx : Integer) : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, dsRRedeemer)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed)
  , (.Rewarding (.ScriptCredential w1), dsRSeizeRedeemer sIdx) ]

/-- **SHAPE DS1R.** -/
def dsRCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaPlusOne inAda ownCS tn qIn
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨⟨ByteString.mk "", 0⟩, resolved⟩]
      , txInfoReferenceInputs :=
          [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1
      , txInfoFee := fee
      , txInfoMint := mintOne ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := delegateRWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := dsRRedeemerMap ownCS w0 w1 mlRed sIdx
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := dsRRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

def dsRInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)

#prep_uplc appliedMintDSRShaped2500 programmableTokenMinting900 dsRInputs 2500

/-! ## REDEEMER COVERAGE AT SHAPES DT1R AND DS1R — for every leaf assignment -/

section Find
variable (ownCS : CurrencySymbol) (w0 w1 : ScriptHash) (mlRed glRed : ByteString) (sIdx : Integer)

theorem dtR_findMinting :
    findRedeemer (.Minting ownCS) (dtRRedeemerMap ownCS w0 w1 mlRed glRed)
      = some dtRRedeemer := by
  rw [dtRRedeemerMap, Realizability.findRedeemer_cons_hit]

theorem dtR_findRewarding0 :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (dtRRedeemerMap ownCS w0 w1 mlRed glRed)
      = some (Data.B mlRed) := by
  rw [dtRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

theorem dsR_findMinting :
    findRedeemer (.Minting ownCS) (dsRRedeemerMap ownCS w0 w1 mlRed sIdx)
      = some dsRRedeemer := by
  rw [dsRRedeemerMap, Realizability.findRedeemer_cons_hit]

theorem dsR_findRewarding0 :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (dsRRedeemerMap ownCS w0 w1 mlRed sIdx)
      = some (Data.B mlRed) := by
  rw [dsRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

end Find

/-- `Rewarding w1` resolves to entry 2 of a delegate redeemer map — under the
side condition `w0 ≠ w1`, which `validWithdrawals` (a conjunct of
`validMintingContext`) forces on every member of the class. -/
theorem dtR_findRewarding1 (ownCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (mlRed glRed : ByteString) (hne : w0 ≠ w1) :
    findRedeemer (.Rewarding (.ScriptCredential w1)) (dtRRedeemerMap ownCS w0 w1 mlRed glRed)
      = some (Data.B glRed) := by
  rw [dtRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_miss _ _ _ _
      (Realizability.rewarding_beq_rewarding_of_ne w0 w1 (Ne.symm hne)),
    Realizability.findRedeemer_cons_hit]

theorem dsR_findRewarding1 (ownCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (mlRed : ByteString) (sIdx : Integer) (hne : w0 ≠ w1) :
    findRedeemer (.Rewarding (.ScriptCredential w1)) (dsRRedeemerMap ownCS w0 w1 mlRed sIdx)
      = some (dsRSeizeRedeemer sIdx) := by
  rw [dsRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_miss _ _ _ _
      (Realizability.rewarding_beq_rewarding_of_ne w0 w1 (Ne.symm hne)),
    Realizability.findRedeemer_cons_hit]

/-- Unconditional form of `dtR_findRewarding1`: when `w0 = w1` entry 1 already
covers the lookup, so no side condition is needed. -/
theorem dtR_findRewarding1_ne (ownCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (mlRed glRed : ByteString) :
    findRedeemer (.Rewarding (.ScriptCredential w1)) (dtRRedeemerMap ownCS w0 w1 mlRed glRed)
      ≠ none := by
  by_cases h : w0 = w1
  · subst h; rw [dtR_findRewarding0]; exact Option.noConfusion
  · rw [dtR_findRewarding1 _ _ _ _ _ h]; exact Option.noConfusion

/-- Same, for SHAPE DS1R. -/
theorem dsR_findRewarding1_ne (ownCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (mlRed : ByteString) (sIdx : Integer) :
    findRedeemer (.Rewarding (.ScriptCredential w1)) (dsRRedeemerMap ownCS w0 w1 mlRed sIdx)
      ≠ none := by
  by_cases h : w0 = w1
  · subst h; rw [dsR_findRewarding0]; exact Option.noConfusion
  · rw [dsR_findRewarding1 _ _ _ _ _ h]; exact Option.noConfusion

section Cover
variable (ownCS tn : ByteString) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
         (o1h : ByteString) (outAda1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
         (sIdx : Integer) (fee : Integer)

/-- **SHAPE DT1R's BOTH script withdrawals are covered**, under the `w0 ≠ w1` that
`validWithdrawals` already forces. -/
theorem dtR_wdrl_covered (hne : w0 ≠ w1) :
    Realizability.WdrlCovered
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) := by
  intro h n hmem
  simp [dtRCtx, delegateRWdrl] at hmem
  show findRedeemer (.Rewarding (.ScriptCredential h)) (dtRRedeemerMap ownCS w0 w1 mlRed glRed)
        ≠ none
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [dtR_findRewarding0]; exact Option.noConfusion
  · rw [dtR_findRewarding1 _ _ _ _ _ hne]; exact Option.noConfusion

/-- **SHAPE DS1R's BOTH script withdrawals are covered** — entry 1 is the
minting-logic script's, entry 2 is the SEIZE validator's, and the latter is the
very entry `mrSeizeRedeemerIdx = 2` names. -/
theorem dsR_wdrl_covered (hne : w0 ≠ w1) :
    Realizability.WdrlCovered
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) := by
  intro h n hmem
  simp [dsRCtx, delegateRWdrl] at hmem
  show findRedeemer (.Rewarding (.ScriptCredential h)) (dsRRedeemerMap ownCS w0 w1 mlRed sIdx)
        ≠ none
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [dsR_findRewarding0]; exact Option.noConfusion
  · rw [dsR_findRewarding1 _ _ _ _ _ hne]; exact Option.noConfusion

theorem dtR_spend_covered :
    Realizability.SpendCovered
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) := by
  intro i hin hscript
  simp [dtRCtx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

theorem dsR_spend_covered :
    Realizability.SpendCovered
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) := by
  intro i hin hscript
  simp [dsRCtx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

theorem dtR_mint_covered :
    Realizability.MintCovered
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) := by
  intro cs m hmem
  simp [dtRCtx, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  show findRedeemer (.Minting _) (dtRRedeemerMap _ w0 w1 mlRed glRed) ≠ none
  rw [dtR_findMinting]; exact Option.noConfusion

theorem dsR_mint_covered :
    Realizability.MintCovered
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) := by
  intro cs m hmem
  simp [dsRCtx, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  show findRedeemer (.Minting _) (dsRRedeemerMap _ w0 w1 mlRed sIdx) ≠ none
  rw [dsR_findMinting]; exact Option.noConfusion

end Cover

end WSC
