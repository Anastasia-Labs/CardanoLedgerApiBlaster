/-
WSC/Props/Shaped/P2ShapedR.lean — **P2, BOTH conjuncts, re-proved over the
NODE-REALIZABLE SHAPE S1R** (task C2).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED FROM `WSC/Props/Shaped/P2Shaped.lean`
════════════════════════════════════════════════════════════════════════════
The redeemer map, and nothing else. SHAPE S1's map is the single entry
`[(Rewarding (ScriptCredential w0), SeizeAct 1 [] 0 0 0 1)]` while the shape
carries ONE script input, ONE minted policy and TWO script withdrawals —
`ShapeRealizability.s1_class_is_empty_under_coverage` proves the resulting class
EMPTY. SHAPE S1R carries the four entries Conway `scriptsNeeded` demands
(`WSC/Shaped/SeizeShapedR.lean`), exactly, and
`WSC.seizeR_{wdrl,spend,mint}_covered` prove the coverage at EVERY leaf
assignment.

Everything a P2 reader cares about is untouched, and untouched *by construction*
rather than by inspection: SHAPE S1R reuses `seizeShapedIn0`, `seizeShapedIn1`,
`seizeShapedParamsIn`, `seizeShapedNode`, `seizeShapedOut0`, `seizeShapedOut1`,
`seizeShapedWdrl`, `seizeShapedRedeemer` and `Shape.mintOne` BY NAME from
`WSC/Shaped/SeizeShaped.lean`. Same flat, same budget 3800, same postconditions.

════════════════════════════════════════════════════════════════════════════
WHICH STRUCTURAL FACTS THE PROOF CONSUMES — task C2 asks this explicitly
════════════════════════════════════════════════════════════════════════════
P2b (containment of the seized delta) is **FALSE in general on the source model**:
`WSC/Props/P2_Seize.lean` §5 records two machine-checked counterexamples to
obligation B1, one with DUPLICATE token names in a `Value`'s token map and one
with an UNSORTED token map. It closes at SHAPE S1 — and at SHAPE S1R — because of
exactly two canonicity facts, both properties of the SHAPE and not of the ledger
predicate:

1. **Every `Value` in the shape is `Shape.adaPlusOne`**, i.e. `[(B "", Map [(B "",
   I n)]), (B cs, Map [(B tn, I q)])]`. A one-entry token map is trivially
   duplicate-free and trivially sorted, so NEITHER counterexample can be
   instantiated inside the class. This is the fact P2b consumes.
2. **The mint field is `Shape.mintOne`**, one policy and one token name, so the
   `tokensForCS key txInfoMint` walk (ProgrammableLogicBase.hs:1318-1319) sees a
   list of length ≤ 1 and `WSC.mintOf` is a single lookup.

The re-cut changes NEITHER — the values and the mint field are the same terms —
so P2b's ground is the same at S1R as at S1. Anyone quoting P2b must quote both
facts: the theorem is about one-policy-one-token-name canonical values.

P2a (structure preservation) consumes, in addition, the three by-construction
equalities DEFECT D4 forces on SHAPE S1 (`WSC/Shaped/SeizeShaped.lean`'s header):
input 0 and output 0 share one payment-credential variable `mlH`, one non-ada
policy variable `mlCS` and one token-name variable `mlTn`, and both carry
`txOutReferenceScript := none`. Those are honest scope losses, they are inherited
verbatim, and D4 is still open.

════════════════════════════════════════════════════════════════════════════
SCOPE
════════════════════════════════════════════════════════════════════════════
Budget 3800 (ADDENDUM E1, bridged by `LR_BUDGET_seize`); SHAPE S1R as published;
realizability at CLAB level only (see `WSC/Realizability.lean`'s `Realizable`).
-/
import WSC.Shaped.SeizeShapedR
import WSC.Props.P2_Seize
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)
open WSC.SeizeModel (seizedPolicyOf pairedOutputsOf progLogicCredDataOf)

/-! ## §Projection audit — SHAPE S1R instantiates P2's own projections

Same three lemmas as `WSC/Props/Shaped/P2Shaped.lean`'s, over the re-cut shape.
They are what licenses reading the theorems below as
"`P2a_seizeModel_preserves_structure` / `P2b_seized_delta_contained`, specialized
to SHAPE S1R and proved against the bytecode instead of the model". -/

section Leaves
variable (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
         (dIn : ByteString)
         (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
         (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
         (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
         (mCS mTn : ByteString) (mQ : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer)
         (spRed mtRed ilRed : ByteString)
         (fee : Integer)

private abbrev rCtx : ScriptContext :=
  seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
    oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
    pHash pCS pTn pAda pQty dirCS plc glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee

/-- The seized policy at SHAPE S1R is `key`, position 0 of the datum of the
reference input the redeemer's `directoryNodeIdx = 1` selects. -/
theorem shapeR_seizedPolicy :
    seizedPolicyOf
      (rCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some key := rfl

/-- The paired-output cursor at SHAPE S1R is the WHOLE output list
(`outputsStartIdx = 0`). -/
theorem shapeR_pairedOutputs :
    pairedOutputsOf
      (rCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some
        (rCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
          oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs := rfl

/-- The mini-ledger base credential at SHAPE S1R is `ScriptCredential plc`,
position 1 of the params datum — PROVIDED the params UTxO authenticates
(`pCS = ppCS`, `phasCSH`, ProgrammableLogicBase.hs:832), which
`P2_R_gates_are_earned` proves the accept path forces. -/
theorem shapeR_progLogicCred (ppCS : CurrencySymbol) (hpc : pCS = ppCS) :
    progLogicCredDataOf ppCS
      (rCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some (IsData.toData (Credential.ScriptCredential plc)) := by
  subst hpc
  simp [progLogicCredDataOf, rCtx, seizeRCtx, seizeShapedRedeemer,
        SeizeModel.seizeFieldsOf, SeizeModel.paramsAtRefIdx, SeizeModel.dropL,
        SeizeModel.headM, seizeShapedParamsIn, Shape.adaPlusOne, SeizeModel.hasCSH,
        SeizeModel.paramsDirCSAndProgCred]

end Leaves

/-! ## The bytecode obligations — BOTH PROVED, over a REALIZABLE class -/

/-- **P2 (a) — STRUCTURE PRESERVATION, over SHAPE S1R, PROVED AT UPLC.**

*If the real compiled `programmableSeize` bytecode accepts a shape-S1R
transaction, then walking the transaction's inputs in order, each input at the
mini-ledger base credential is paired with the next output, and that pair has the
same address — STAKING CREDENTIAL INCLUDED — the same datum, the same reference
script, and identical holdings of every policy other than the seized one and
other than ada; ada may only be TOPPED UP, never reduced. Inputs outside the
mini-ledger consume no output.*

Postcondition is `WSC.seizeStructurePreservedAdaTopUp` verbatim (WSC/Spec.lean).

⚠️ **CHANGED BY PR #112 — the postcondition is WEAKER than it was, because the
bytecode is.** Until #112 this theorem carried `WSC.seizeStructurePreserved`,
whose per-pair rule demands every non-seized policy equal **ada included**. That
statement is now ❌ FALSIFIED against production (task N5, measured): the
counterexample's sole defect is `i0Ada = 23101` against `o0Ada = 36307`, an ada
top-up. #112 legalised it on purpose — see the `adaToppedUp` rationale quoted in
`WSC/Spec.lean`. The clause that replaces equality is an INEQUALITY IN ONE
DIRECTION, `in ≤ out`, and `P2a_R_ada_only_tops_up` below proves that direction
is real and not an artefact of a weaker predicate. -/
theorem P2a_R_structure :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.seizeStructurePreservedAdaTopUp (Credential.ScriptCredential plc) key
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs = true
      := by blaster

/-- **P2 (a′) — THE ADA RELAXATION IS ONE-DIRECTIONAL.**

*If the bytecode accepts, the continuing output's lovelace is at least the
lovelace of the mini-ledger input it continues.*

This is the theorem that stops the #112 weakening from being a hole. Replacing
`pairPreserved`'s ada EQUALITY by an inequality would be worthless if the
inequality could point either way — a seizure that also drained the victim's
lovelace would satisfy a two-sided relaxation. It cannot: `adaToppedUp` tests
`pasInt … #<= pconstantInteger 0` on the ada entry of the delta, and the delta
is `input - output`.

Stated on the raw ledger leaves rather than through
`seizeStructurePreservedAdaTopUp`, deliberately: `i0Ada` and `o0Ada` ARE the
lovelace quantities the shape puts in input 0's and output 0's `txOutValue`
(`Shape.adaPlusOne`), so this postcondition cannot be satisfied by a weakness in
the predicate — there is no predicate.

BOTH hypotheses were forced by measured counterexamples, neither was guessed:
* `mlH = plc` — without it the solver picks `mlH ≠ plc`, so input 0 is not a
  mini-ledger input at all, the pair is never examined and its ada is free
  (counterexample: `mlH = "\u{0}"`, `plc = "A"`, `i0Ada = 2`, `o0Ada = 1`);
* `key ≠ adaSymbol` — without it the solver seizes ADA ITSELF, and then the ada
  decrease IS the seizure (counterexample: `key = ""`, `i0Ada = 26783`,
  `o0Ada = 21540`, every other policy equal). -/
theorem P2a_R_ada_only_tops_up :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      mlH = plc → key ≠ CardanoLedgerApi.V1.adaSymbol → i0Ada ≤ o0Ada
      := by blaster

/-- **P2 (b) — CONTAINMENT OF THE SEIZED DELTA, over SHAPE S1R, PROVED AT UPLC.**
The conjunct the source-model route could NOT close.

*For EVERY token name, the total holding of the seized policy at outputs sitting
on the mini-ledger base credential is at least the total holding at inputs spent
from it, plus the (signed) net mint of that asset.*

Read the module header's "WHICH STRUCTURAL FACTS THE PROOF CONSUMES" before
quoting this: it closes because SHAPE S1R's values are one-policy /
one-token-name canonical, which is what makes the two machine-checked
counterexamples to the general statement uninstantiable inside the class. -/
theorem P2b_R_containment :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
            spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
                spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint
      := by blaster

/-- **The shape does not pre-satisfy the validator's three authentication gates.**
`pCS = ppCS` (`phasCSH` on the params UTxO, :832), `nCS = dirCS` (condition 4,
:1329), `w1 = ilsH` (condition 3, :1323-1328). Each pair is two DIFFERENT free
variables, so none is true by construction — and the third is exactly why SHAPE
S1R's withdrawal entry 1 has to be a SCRIPT credential with its own redeemer
entry. -/
theorem P2_R_gates_are_earned :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      pCS = ppCS ∧ nCS = dirCS ∧ w1 = ilsH
      := by blaster

/-! ## Polarity controls (ADDENDUM E9) — the full control set at SHAPE S1R -/

/-- Negative control for conjunct 1. -/
theorem P2a_R_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬(WSC.seizeStructurePreservedAdaTopUp (Credential.ScriptCredential plc) key
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs = true) →
    isUnsuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      := by blaster

/-- Negative control for conjunct 2: a shape-S1R context in which the seized
policy ESCAPES the mini-ledger for some token name is REJECTED. -/
theorem P2b_R_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬(WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
            spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
                spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint) →
    isUnsuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      := by blaster

/-- Tightness stanza for conjunct 1 at SHAPE S1R. Expected: `Falsified`. -/
def P2a_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬(WSC.seizeStructurePreservedAdaTopUp (Credential.ScriptCredential plc) key
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs = true)

#blaster (gen-cex: 0) (solve-result: 1) [P2a_R_tightness]

/-- Tightness stanza for conjunct 2 at SHAPE S1R. Expected: `Falsified`. -/
def P2b_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬(WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
            spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
                spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint)

#blaster (gen-cex: 0) (solve-result: 1) [P2b_R_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND THE NEW SHAPE.** "No accepting
shape-S1R context exists within 3800 CEK steps" must be FALSIFIED. -/
def P2_R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬ isSuccessful
      (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)

#blaster (gen-cex: 0) (solve-result: 1) [P2_R_vacuity_probe]

/-! ## CONCRETE instances OF EXACTLY SHAPE S1R, and their REALIZABILITY

The same four leaf assignments as `WSC.P2ShapedWitness`, with the three new
redeemer-payload leaves filled in:

* `ctxAccept`   — accepting, "nothing moves": the pair keeps all 10 seized tokens
                  and output 1 sits outside the mini-ledger holding an unrelated
                  policy;
* `ctxResidual` — accepting, "residual output": 5 of the 9 seized tokens plus the
                  +2 mint land in output 1, which IS at the base credential — the
                  real goldens' shape;
* `ctxEscape`   — ledger-legal, REDEEMER-COVERED ESCAPE of the seized tokens past
                  the mini-ledger. Must be rejected;
* `ctxStolen`   — ledger-legal, REDEEMER-COVERED, tokens stay at the base payment
                  credential but the continuing output's STAKING credential is
                  changed. Must be rejected. -/

namespace P2RWitness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1R at a leaf assignment. -/
def mk (i0Qty o0Qty : Integer) (escH : ByteString) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (i1CS i1Tn : ByteString) (i1Qty : Integer) (mQ : Integer) (oStk : ByteString)
    : ScriptContext :=
  seizeRCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") i0Qty (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 i1CS i1Tn i1Qty
    oStk 300 o0Qty (ByteString.mk "DTM")
    escH 50 o1CS o1Tn o1Qty
    (ByteString.mk "MMM") (ByteString.mk "TOK") mQ
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    (ByteString.mk "SPRED") (ByteString.mk "MTRED") (ByteString.mk "ILRED")
    50

def ctxAccept : ScriptContext :=
  mk 10 12 (ByteString.mk "CHANGE") (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
     (ByteString.mk "ZZZP") (ByteString.mk "WT") 1 2 (ByteString.mk "USERSTK")

def ctxResidual : ScriptContext :=
  mk 9 4 (ByteString.mk "PROGLOGIC") (ByteString.mk "MMM") (ByteString.mk "TOK") 8
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2 (ByteString.mk "USERSTK")

def ctxEscape : ScriptContext :=
  mk 10 4 (ByteString.mk "CHANGE") (ByteString.mk "MMM") (ByteString.mk "TOK") 9
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2 (ByteString.mk "USERSTK")

/-- The staking-credential theft instance: `ctxAccept` with the continuing
output's STAKING credential changed from `USERSTK` to `THIEFSTK`. -/
def ctxStolen : ScriptContext :=
  mk 10 12 (ByteString.mk "CHANGE") (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
     (ByteString.mk "ZZZP") (ByteString.mk "WT") 1 2 (ByteString.mk "THIEFSTK")

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- All four instances satisfy the theorems' ledger-normalization hypothesis. -/
theorem all_four_valid :
    validRewardingContext ctxAccept = true ∧
    validRewardingContext ctxResidual = true ∧
    validRewardingContext ctxEscape = true ∧
    validRewardingContext ctxStolen = true := by native_decide

/-- **AND ALL FOUR ARE REDEEMER-COVERED** — the conjunct no instance of SHAPE S1
can satisfy. This is what makes the two REJECTED instances evidence about
transactions an attacker could really build. -/
theorem all_four_covered :
    Realizability.redeemerCovered ctxAccept = true ∧
    Realizability.redeemerCovered ctxResidual = true ∧
    Realizability.redeemerCovered ctxEscape = true ∧
    Realizability.redeemerCovered ctxStolen = true := by native_decide

/-- **REALIZABILITY OF SHAPE S1R — the acceptance criterion.** -/
theorem ctxAccept_realizable : Realizability.Realizable ctxAccept := by
  refine ⟨by native_decide, all_four_covered.1, ?_, ?_, ?_⟩
  · apply seizeR_wdrl_covered; decide
  · apply seizeR_spend_covered
  · apply seizeR_mint_covered

/-- The residual-output instance — the shape every real accepting seize golden
has — is realizable too. -/
theorem ctxResidual_realizable : Realizability.Realizable ctxResidual := by
  refine ⟨by native_decide, all_four_covered.2.1, ?_, ?_, ?_⟩
  · apply seizeR_wdrl_covered; decide
  · apply seizeR_spend_covered
  · apply seizeR_mint_covered

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS `ctxAccept`
at budget 3800 through the SHAPED applied term the theorems quantify over. -/
theorem exec_accepts_at_3800 :
    isSuccessful
      (appliedSeizeRShaped3800.exec ppCS
        (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
          (ByteString.mk "MMM") (ByteString.mk "TOK") 10 (ByteString.mk "DTM")
        (ByteString.mk "WALLET") 100 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
        (ByteString.mk "USERSTK") 300 12 (ByteString.mk "DTM")
        (ByteString.mk "CHANGE") 50 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
        (ByteString.mk "MMM") (ByteString.mk "TOK") 2
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
          (ByteString.mk "SEIZELOGIC")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
          (ByteString.mk "ZZILS") (ByteString.mk "GS")
        (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
        (ByteString.mk "SPRED") (ByteString.mk "MTRED") (ByteString.mk "ILRED")
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED CASES, executed.** Both the ESCAPE and the STAKING-CREDENTIAL
THEFT are rejected by the real CEK machine — and at **20000** steps, not merely at
3800, so the rejections are genuine and not budget exhaustion. -/
theorem exec_rejects_escape_and_theft :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxEscape) 20000) = false
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxStolen) 20000) = false := by native_decide

/-- **EXACT WITNESS Ks — `2301` (accepting) and `2412` (residual)**, re-measured
against the PR #112 bytecode (task N5). Both pinned TWO-SIDED: the machine halts
at K and budget-errors at K−1.

PRE-#112 these were `3004` and `3328`, so the optimisation is worth **−23.4 %**
and **−27.5 %** of the CEK step count on these two witnesses — the same order as
the −23.2 % / −42.8 % measured on the two accepting seize goldens
(`WSC/goldens/K-MEASUREMENTS.md` §3). Both remain below the 3800 prep budget, so
the budget did NOT have to move and the shape is unchanged; and the accepting
witness's 2301 now sits just under the cheapest accepting seize golden's 2305,
where before it sat just above 2,570. -/
theorem K_is_2301_and_2412 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxAccept) 2301) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxAccept) 2300) = false
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual) 2412) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual) 2411) = false := by native_decide

end P2RWitness

end WSC

/-! ## §Axiom census (task N5)

`WSC.SeizeModel.seizeModel_faithful` is REFUTED at wsc-poc `2306678`
(`WSC/Model/SeizeModelRefuted.lean`). This module imports `WSC/Props/P2_Seize.lean`,
which USES that axiom, so it is worth demonstrating rather than asserting that
NONE of the results above travels through it. The shaped route talks to the
bytecode directly and cites no model.

`blaster` closes its goals with `admit`, so `sorryAx` is expected on every
theorem it proves and is not a defect; what matters is that
`WSC.SeizeModel.seizeModel_faithful` does NOT appear. -/

#print axioms WSC.P2a_R_structure
#print axioms WSC.P2a_R_ada_only_tops_up
#print axioms WSC.P2b_R_containment
#print axioms WSC.P2_R_gates_are_earned
#print axioms WSC.P2a_R_negative_control
#print axioms WSC.P2b_R_negative_control
#print axioms WSC.P2RWitness.K_is_2301_and_2412
#print axioms WSC.P2RWitness.exec_accepts_at_3800
#print axioms WSC.P2RWitness.exec_rejects_escape_and_theft
