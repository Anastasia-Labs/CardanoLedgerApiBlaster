/-
WSC/Shaped/MintingLocalShapedR.lean — **SHAPE L1R: the NODE-REALIZABLE re-cut of
SHAPE L1**, the issuance policy's `Local` custody arm (task C2).

════════════════════════════════════════════════════════════════════════════
THE RE-CUT, IN ONE TABLE
════════════════════════════════════════════════════════════════════════════
SHAPE L1 (`WSC/Shaped/MintingLocalShaped.lean`) is proved EMPTY as a class of
ledger transactions by `WSC/Props/Shaped/ShapeRealizability.lean`'s
`l1_class_is_empty_under_coverage`: two SCRIPT withdrawals, one redeemer entry.

| | SHAPE L1 | **SHAPE L1R** | golden `mint-local-registered-by-ref` |
|---|---|---|---|
| inputs (script / total) | 0 / 1 | **0 / 1** | 0 / 1 |
| reference inputs | 2 | **2** | 2 |
| outputs | 2 | **2** | — |
| mint policies | 1 | **1** | 1 |
| withdrawals (script / total) | 2 / 2 | **1 / 1** | 1 / 1 |
| redeemer entries | 1 | **2** | 2 |
| coverage `#red = #scriptIn + #mintPol + #scriptWdrl` | 1 ≠ 3 ✗ | **2 = 2 ✓** | 2 = 2 ✓ |

SHAPE L1R IS THE `mint-local-registered-by-ref` GOLDEN'S EXACT REDEEMER /
WITHDRAWAL SHAPE. That golden is the `Local` arm's production transaction and the
one whose measured `K = 1681` SHAPE L1's witness reproduces to the step.

════════════════════════════════════════════════════════════════════════════
WHAT THE `Local` ARM REQUIRES OF THE WITHDRAWAL MAP — and nothing more
════════════════════════════════════════════════════════════════════════════
Issuance.hs:159-198. The arm's three `pvalidateConditions` conjuncts (:194-198):

1. `mintingLogicInvokedAt # wdrlIdx` (:195) — the ONLY read of `ptxInfo'wdrl` on
   this arm, and it demands that the entry at `mrMintingLogicWdrlIdx` carry
   `PScriptCredential mintingLogicHash'` (:136, :150-151). So **exactly one
   withdrawal entry must be a SCRIPT credential**, and it must be the one the
   redeemer indexes. A PUBKEY entry there makes the arm unsatisfiable, i.e. the
   class accept-UNSAT; one script withdrawal is the FLOOR, not a choice.
2. `registrationOk` (:196) — reads `referenceInputs` only.
3. `noEscape` (:197, defined :179-193) — reads `outputs` and the params datum's
   `pprogLogicCred` only.

Neither the redeemer map nor a second withdrawal entry is read anywhere on this
arm. SHAPE L1's `w1` was generality that cost the whole class its inhabitants.

WHAT THE SHRINK DOES *NOT* TOUCH — every "NOT TRUE BY CONSTRUCTION" fact of
SHAPE L1 survives verbatim (`WSC/Shaped/MintingLocalShaped.lean`'s stanza), and
the two that involve the withdrawal map are unaffected because `w0` is still a
FREE variable and `validWithdrawals` is vacuous on a singleton:

* C1 is still earned — `w0` vs the applied parameter `mlh`, two independent
  universally quantified variables;
* registration is still earned — `nCS`/`nTn`/`nQty` free and distinct from
  `dirCS`/`ownCS`; `pCS` distinct from the script parameter `ppCS`;
* `noEscape` is still earned, and this is the load-bearing one — `o0h` vs `plc`
  are different free variables, `c0` vs `ownCS` are different free variables, and
  **there are still exactly TWO outputs**, so the `pall` scan still traverses a
  list whose two elements take DIFFERENT branches of the per-output disjunction
  (output 1 ada-only ⟹ value branch; output 0 ⟹ credential branch). The
  non-degeneracy argument of `WSC/Props/Shaped/P4LocalShaped.lean` Bound 2b is
  preserved exactly: with one output the balance rule forces that output to carry
  `ownCS` and the scan collapses. **Two outputs is a REQUIREMENT of the re-cut,
  not an inheritance.**

FIXED / SYMBOLIC: as `WSC/Shaped/MintingLocalShaped.lean`'s header, with the two
withdrawal/redeemer rows above replaced, plus one new symbolic leaf `mlRed` — the
minting-logic script's own redeemer payload, carried as `Data.B mlRed`, which the
issuance policy never decodes on any arm.

REDEEMER-MAP ORDER: `[Minting ownCS, Rewarding (ScriptCredential w0)]` is sorted
under CLAB's corrected `ltScriptPurpose` for every leaf assignment
(`CardanoLedgerApi/V3/Contexts.lean:101-120`), so `validRedeemerMap` costs no side
condition.
-/
import WSC.Prep.Minting900
import WSC.Shaped.Shape
import WSC.Shaped.MintingLocalShaped
import WSC.Redeemer
import WSC.Realizability
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

/-- SHAPE L1R's withdrawal map: **one** script entry — the C1 floor. -/
def localRWdrl (w0 : ScriptHash) (a0 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0)]

/-- SHAPE L1R's own redeemer — unchanged from SHAPE L1:
`Local 0 0 (RegisteredByReferenceInput 1)`. -/
def localRRedeemer : Data :=
  IsData.toData (MintRedeemer.Local 0 0 (RegWitness.RegisteredByReferenceInput 1))

/-- AUDIT: `Constr 0 [I 0, I 0, Constr 0 [I 1]]`, i.e. byte-identical to
SHAPE L1's `localShapedRedeemer`. -/
theorem localRRedeemer_eq : localRRedeemer = localShapedRedeemer := rfl

/-- **SHAPE L1R's redeemer map.** The own `Minting` entry plus the `Rewarding`
entry that covers the single script withdrawal. -/
def localRRedeemerMap (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, localRRedeemer)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed) ]

/-- **SHAPE L1R.** SHAPE L1's reference inputs, outputs, input and mint verbatim
(they are re-used from `WSC/Shaped/MintingLocalShaped.lean`, so the two shapes
differ in EXACTLY the withdrawal and redeemer maps and nothing else). -/
def localRCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
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
      , txInfoWdrl := localRWdrl w0 a0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := localRRedeemerMap ownCS w0 mlRed
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := localRRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

/-! ### AUDIT LINKS -/

section Audit
variable (ownCS tn : ByteString) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
         (o1h : ByteString) (outAda1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 : ByteString) (a0 : Integer) (mlRed : ByteString) (fee : Integer)

theorem localRCtx_outputs :
    (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
      fee).scriptContextTxInfo.txInfoOutputs
      = localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1 := rfl

theorem localRCtx_wdrl :
    (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
      fee).scriptContextTxInfo.txInfoWdrl = localRWdrl w0 a0 := rfl

theorem localRCtx_refInputs :
    (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
      fee).scriptContextTxInfo.txInfoReferenceInputs
      = [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
        , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] := rfl

theorem localRCtx_mint :
    (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
      fee).scriptContextTxInfo.txInfoMint = mintOne ownCS tn q := rfl

theorem localRCtx_redeemers :
    (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
      fee).scriptContextTxInfo.txInfoRedeemers = localRRedeemerMap ownCS w0 mlRed := rfl

end Audit

/-! ### REDEEMER COVERAGE AT SHAPE L1R — for every leaf assignment -/

theorem localR_findRewarding (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString) :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (localRRedeemerMap ownCS w0 mlRed)
      = some (Data.B mlRed) := by
  rw [localRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

theorem localR_findMinting (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString) :
    findRedeemer (.Minting ownCS) (localRRedeemerMap ownCS w0 mlRed) = some localRRedeemer := by
  rw [localRRedeemerMap, Realizability.findRedeemer_cons_hit]

section Cover
variable (ownCS tn : ByteString) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
         (o1h : ByteString) (outAda1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 : ByteString) (a0 : Integer) (mlRed : ByteString) (fee : Integer)

/-- SHAPE L1R's single script withdrawal is covered. -/
theorem localR_wdrl_covered :
    Realizability.WdrlCovered
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) := by
  intro h n hmem
  simp [localRCtx, localRWdrl] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [localRCtx_redeemers, localR_findRewarding]
  exact Option.noConfusion

/-- SHAPE L1R spends nothing from a script credential. -/
theorem localR_spend_covered :
    Realizability.SpendCovered
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) := by
  intro i hin hscript
  simp [localRCtx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

/-- SHAPE L1R's single minted policy is its own. -/
theorem localR_mint_covered :
    Realizability.MintCovered
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) := by
  intro cs m hmem
  simp [localRCtx, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [localRCtx_redeemers, localR_findMinting]
  exact Option.noConfusion

end Cover

/-- Parameter evidence unchanged from WSC/Prep/Minting900.lean. -/
def localRInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)

#prep_uplc appliedMintLocalRShaped2500 programmableTokenMinting900 localRInputs 2500

end WSC
