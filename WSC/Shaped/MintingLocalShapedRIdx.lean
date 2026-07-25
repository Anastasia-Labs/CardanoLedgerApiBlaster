/-
WSC/Shaped/MintingLocalShapedRIdx.lean — **SHAPE L2R: the NODE-REALIZABLE re-cut of
SHAPE L2**, i.e. SHAPE L1R with the `Local` arm's REGISTRATION reference-input index
left SYMBOLIC (audit finding **F19**).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
SHAPE L2 (`WSC/Shaped/MintingLocalShapedIdx.lean`) carries
`P4_local_noEscape_shapedIdx`, the loosening rung that MEASURED the `Local` arm's
no-escape property to be registration-index-INDEPENDENT. But SHAPE L2 inherits
SHAPE L1's withdrawal/redeemer maps — TWO script withdrawals against ONE redeemer
entry — and `WSC/Props/Shaped/ShapeRealizability.lean`'s
`l1_class_is_empty_under_coverage` proves that class EMPTY as a class of ledger
transactions (Conway `MissingRedeemers`). So the strongest `Local`-arm statement in
the library ranged over a class with no inhabitants, which is why `WSC/README.md`
and `WSC/STATUS.md` both instruct the reader NOT to quote it. This module re-cuts
that rung the way `WSC/Shaped/MintingLocalShapedR.lean` re-cut SHAPE L1, so the
measurement survives over a class that has a certified member.

════════════════════════════════════════════════════════════════════════════
THE RE-CUT, IN ONE TABLE
════════════════════════════════════════════════════════════════════════════
| | SHAPE L2 | **SHAPE L2R** | SHAPE L1R |
|---|---|---|---|
| inputs (script / total) | 0 / 1 | **0 / 1** | 0 / 1 |
| reference inputs | 2 | **2** | 2 |
| outputs | 2 | **2** | 2 |
| mint policies | 1 | **1** | 1 |
| withdrawals (script / total) | 2 / 2 | **1 / 1** | 1 / 1 |
| redeemer entries | 1 | **2** | 2 |
| coverage `#red = #scriptIn + #mintPol + #scriptWdrl` | 1 ≠ 3 ✗ | **2 = 2 ✓** | 2 = 2 ✓ |
| registration index | SYMBOLIC | **SYMBOLIC** | concrete `1` |

So SHAPE L2R is to SHAPE L1R exactly what SHAPE L2 is to SHAPE L1, and it is
SHAPE L1R's withdrawal/redeemer shape — the `mint-local-registered-by-ref` golden's
own shape — verbatim. **`localRCtxIdx … 1 = localRCtx …` definitionally**
(`localRCtxIdx_at_one`, proved by `rfl` below), so the two shapes agree at the
concrete index and SHAPE L2R strictly contains SHAPE L1R.

════════════════════════════════════════════════════════════════════════════
THE ONE SCRIPT WITHDRAWAL IS THE C1 FLOOR, NOT A CHOICE
════════════════════════════════════════════════════════════════════════════
Issuance.hs at wsc-poc `7ae0024` (the commit whose export the `.flat` is byte-
identical to — AUDIT §6):

* `:136` `mintingLogicCred <- plet $ pdata $ pcon $ PScriptCredential mintingLogicHash'`
* `:150-151` `mintingLogicInvokedAt <- plet $ plam $ \wdrlIdx ->
   (pfstBuiltin # (phead # (pcheckedDrop # pfromData wdrlIdx # withdrawalEntries)))
   #== mintingLogicCred`
* `:194-198` the `Local` arm's `pvalidateConditions [ mintingLogicInvokedAt # wdrlIdx
   , registrationOk , noEscape ]`

C1 (`:195`) is the ONLY read of `ptxInfo'wdrl` on this arm and it demands that the
entry at `mrMintingLogicWdrlIdx` (pinned to 0 here) carry a SCRIPT credential. One
script withdrawal is therefore the FLOOR: a PUBKEY entry at index 0 makes the arm
accept-UNSAT, and a second withdrawal buys nothing the arm ever reads. Dropping
SHAPE L2's `w1` is what makes the redeemer count come out exact — 2 entries against
0 script inputs + 1 mint policy + 1 script withdrawal — and that is the whole
content of the re-cut.

**THE REDEEMER MAP COVERS EVERY SCRIPT WITNESS.** `localRIdx_{wdrl,spend,mint}_covered`
below prove it at EVERY leaf assignment, not merely at the witness, in the three
∀-forms `WSC/Realizability.lean` requires.

════════════════════════════════════════════════════════════════════════════
WHAT THE LOOSENING BUYS, AND WHAT `pcheckedDrop` MAKES OF IT
════════════════════════════════════════════════════════════════════════════
`regIdx` is a free `Integer` in the redeemer PAYLOAD, so the symbolic
`pcheckedDrop # regIdx # referenceInputs` (Issuance.hs:171-173) cannot be reduced at
prep time. With TWO reference inputs the theorem therefore covers:

* `regIdx = 0` — the params reference input, which carries no `DIRCS.OWNCS` NFT, so
  `registrationOk` is FALSE and the arm rejects;
* `regIdx = 1` — the directory node, the accepting value;
* every out-of-range value (`phead` on the emptied list errors); and
* every NEGATIVE value, which `pcheckedDrop` (Issuance.hs:126-130) rejects
  EXPLICITLY rather than by clamping or by budget exhaustion — `pdropList` treats a
  negative count as zero, and the source comment at `:128-129` says the guard is
  kept for exactly that reason.

NON-DEGENERACY IS PRESERVED, ITEM BY ITEM — every "NOT TRUE BY CONSTRUCTION" fact of
SHAPE L1R survives verbatim, because the loosening touches only the redeemer payload:

* **C1 is still earned** — `w0` (the shape's withdrawal credential) and `mlh` (the
  script's second APPLIED PARAMETER) are independent universally quantified
  variables, and `validWithdrawals` is vacuous on a singleton;
* **registration is still earned** — `nCS`/`nTn`/`nQty` are free and distinct from
  `dirCS`/`ownCS`; `pCS` is distinct from the script parameter `ppCS`;
* **`noEscape` is still earned, and this is the load-bearing one** — `o0h` vs `plc`
  are different free variables, `c0` vs `ownCS` are different free variables, and
  **there are still exactly TWO outputs**, so the `pall` scan (Issuance.hs:183-193)
  still traverses a list whose two elements take DIFFERENT branches of the
  per-output disjunction: output 1 is ada-only and discharges through the VALUE
  branch (`:192`), output 0 through the CREDENTIAL branch (`:190`). With ONE output
  the ledger balance rule forces that output to carry `ownCS`, the disjunction
  collapses to a credential comparison and the `¬hasCS` branch is never taken.
  **Two outputs is a REQUIREMENT of this shape, not an inheritance**
  (`WSC/Props/Shaped/P4LocalShapedR.lean` Bound 2b).

FIXED / SYMBOLIC: as `WSC/Shaped/MintingLocalShapedR.lean`, with the registration
index moved from FIXED to SYMBOLIC. The constructor TAGS stay concrete (`Local` = 0,
`RegisteredByReferenceInput` = 0), as do `mrMintingLogicWdrlIdx = 0` and
`mrParamsRefIdx = 0` — freeing those is a different rung and is not attempted here.

REDEEMER-MAP ORDER: `[Minting ownCS, Rewarding (ScriptCredential w0)]` is sorted
under CLAB's corrected `ltScriptPurpose` for every leaf assignment
(`CardanoLedgerApi/V3/Contexts.lean:101-120`), so `validRedeemerMap` costs no side
condition — the index lives in the redeemer's PAYLOAD, not in the map's KEYS, so
the loosening cannot disturb the ordering.
-/
import WSC.Prep.Minting900
import WSC.Shaped.Shape
import WSC.Shaped.MintingLocalShaped
import WSC.Shaped.MintingLocalShapedR
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

/-- SHAPE L2R's own redeemer: `Local 0 0 (RegisteredByReferenceInput regIdx)` with
`regIdx` SYMBOLIC. -/
def localRRedeemerIdx (regIdx : Integer) : Data :=
  IsData.toData (MintRedeemer.Local 0 0 (RegWitness.RegisteredByReferenceInput regIdx))

/-- AUDIT: `Constr 0 [I 0, I 0, Constr 0 [I regIdx]]`. This is SHAPE L2's
`localIdxShapedRedeemer` on the nose — compare
`WSC/Shaped/MintingLocalShapedIdx.lean`'s `localIdxShapedRedeemer_eq`, which states
the same normal form. (That module is deliberately NOT imported here: SHAPE L2R
must not depend on the proved-empty shape it replaces.) -/
theorem localRRedeemerIdx_eq (regIdx : Integer) :
    localRRedeemerIdx regIdx
      = Data.Constr 0 [Data.I 0, Data.I 0, Data.Constr 0 [Data.I regIdx]] := rfl

/-- AUDIT: at `regIdx = 1` it is SHAPE L1R's redeemer on the nose. -/
theorem localRRedeemerIdx_at_one : localRRedeemerIdx 1 = localRRedeemer := rfl

/-- **SHAPE L2R's redeemer map.** SHAPE L1R's, with the loosened own redeemer: the
`Minting` entry for the policy itself plus the `Rewarding` entry that covers the
single script withdrawal. -/
def localRRedeemerMapIdx (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    (regIdx : Integer) : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, localRRedeemerIdx regIdx)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed) ]

/-- **SHAPE L2R.** SHAPE L1R verbatim — same single input, same TWO reference
inputs, same TWO outputs, same mint, same SINGLE script withdrawal `localRWdrl` —
with the registration index symbolic in the redeemer and in the redeemer map. -/
def localRCtxIdx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer)
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
      , txInfoRedeemers := localRRedeemerMapIdx ownCS w0 mlRed regIdx
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := localRRedeemerIdx regIdx
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
         (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
         (regIdx : Integer) (fee : Integer)

/-- **SHAPE L2R CONTAINS SHAPE L1R, DEFINITIONALLY.** At `regIdx = 1` the two
contexts are the same term, so every theorem below is a strengthening of the
corresponding SHAPE L1R theorem and no separate containment argument is needed. -/
theorem localRCtxIdx_at_one :
    localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed 1 fee
      = localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee := rfl

/-- **THE TWO OUTPUTS ARE THE SAME TWO** — the non-degeneracy of the no-escape scan
is inherited verbatim, not re-argued. -/
theorem localRCtxIdx_outputs :
    (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx
      fee).scriptContextTxInfo.txInfoOutputs
      = localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1 := rfl

/-- **ONE SCRIPT WITHDRAWAL — the C1 floor** (Issuance.hs:150-151). -/
theorem localRCtxIdx_wdrl :
    (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx
      fee).scriptContextTxInfo.txInfoWdrl = localRWdrl w0 a0 := rfl

/-- **TWO reference inputs** — so a symbolic `regIdx` has two in-range values to
explore, only one of which carries the registration NFT. -/
theorem localRCtxIdx_refInputs :
    (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx
      fee).scriptContextTxInfo.txInfoReferenceInputs
      = [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
        , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] := rfl

theorem localRCtxIdx_mint :
    (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx
      fee).scriptContextTxInfo.txInfoMint = mintOne ownCS tn q := rfl

theorem localRCtxIdx_redeemers :
    (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx
      fee).scriptContextTxInfo.txInfoRedeemers
      = localRRedeemerMapIdx ownCS w0 mlRed regIdx := rfl

end Audit

/-! ### REDEEMER COVERAGE AT SHAPE L2R — for every leaf assignment

The loosened index lives in the redeemer PAYLOAD, so none of the three coverage
obligations moves: the map's KEYS are SHAPE L1R's keys. -/

theorem localRIdx_findRewarding (ownCS : CurrencySymbol) (w0 : ScriptHash)
    (mlRed : ByteString) (regIdx : Integer) :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (localRRedeemerMapIdx ownCS w0 mlRed regIdx)
      = some (Data.B mlRed) := by
  rw [localRRedeemerMapIdx,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

theorem localRIdx_findMinting (ownCS : CurrencySymbol) (w0 : ScriptHash)
    (mlRed : ByteString) (regIdx : Integer) :
    findRedeemer (.Minting ownCS) (localRRedeemerMapIdx ownCS w0 mlRed regIdx)
      = some (localRRedeemerIdx regIdx) := by
  rw [localRRedeemerMapIdx, Realizability.findRedeemer_cons_hit]

section Cover
variable (ownCS tn : ByteString) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
         (o1h : ByteString) (outAda1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
         (regIdx : Integer) (fee : Integer)

/-- SHAPE L2R's single script withdrawal is covered — at every leaf assignment and
every value of the loosened index. -/
theorem localRIdx_wdrl_covered :
    Realizability.WdrlCovered
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) := by
  intro h n hmem
  simp [localRCtxIdx, localRWdrl] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [localRCtxIdx_redeemers, localRIdx_findRewarding]
  exact Option.noConfusion

/-- SHAPE L2R spends nothing from a script credential. -/
theorem localRIdx_spend_covered :
    Realizability.SpendCovered
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) := by
  intro i hin hscript
  simp [localRCtxIdx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

/-- SHAPE L2R's single minted policy is its own. -/
theorem localRIdx_mint_covered :
    Realizability.MintCovered
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) := by
  intro cs m hmem
  simp [localRCtxIdx, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [localRCtxIdx_redeemers, localRIdx_findMinting]
  exact Option.noConfusion

end Cover

/-- Parameter evidence unchanged from `WSC/Prep/Minting900.lean`; same flat, same
imported program object, same CEK budget 2500 as SHAPE L1R and SHAPE L2. -/
def localRInputsIdx
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
    (regIdx : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee)

#prep_uplc appliedMintLocalRShapedIdx2500 programmableTokenMinting900 localRInputsIdx 2500

end WSC
