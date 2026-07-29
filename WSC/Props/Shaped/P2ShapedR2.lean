/-
WSC/Props/Shaped/P2ShapedR2.lean — **P2's containment conjunct, re-proved over
SHAPE S1R2: values with MORE THAN ONE TOKEN NAME.**

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P2ShapedR.lean` used to say that `P2b_R_containment` closes
"because SHAPE S1R's values are one-policy / one-token-name canonical", and that
this was what made the two `tokensContain` counterexamples in
`WSC/Props/P2_Seize.lean` uninstantiable inside the class.  The first half of
that sentence was never measured.  It is now, and it is FALSE: the containment
conjunct did **not** need one token name per value.

SHAPE S1R2 is SHAPE S1R with exactly one change — every `Value` the containment
conjunct reads (mini-ledger input 0, continuing output 0, output 1) and the MINT
FIELD carry a non-ada policy with **TWO** token names and two independent
symbolic quantities, instead of one.  `validRewardingContext` forces the two
names to ascend strictly and the two output/input quantities to be positive, and
forces nothing else; the mint quantities keep their free sign.  Everything else
— addresses, staking credentials, datums, reference inputs, withdrawal map,
redeemer map, script info, budget — is S1R's, re-used by name.

`P2b_R2_containment` below is `✅ Valid` at the same budget 3800, and the
vacuity probe at the S1R2 term is `✅ Expected Falsified`, so the class is
non-empty within budget.  What P2b actually consumes is therefore LEDGER
CANONICITY, which `validRewardingContext` supplies, and not a shape restriction
— see `WSC.P2.tokensContain_sound` in `WSC/Props/P2_Seize.lean` §4b for the
kernel-checked reason.

════════════════════════════════════════════════════════════════════════════
WHAT IS STILL BOUNDED
════════════════════════════════════════════════════════════════════════════
This is a strengthening, not a removal of the shape bound.  S1R2 still fixes:
* TWO token names per value, not `n` — the skeleton is still closed;
* ONE non-ada policy per value, and ONE minted policy;
* the WALLET input (input 1) and the two reference inputs keep S1R's
  `Shape.adaPlusOne`, one token name.  Input 1 sits at a PUBKEY address, so
  `WSC.inAtBase` is false on it and it contributes nothing to either side of the
  containment inequality; the reference inputs are not summed at all.  Widening
  them would enlarge the class without touching what the conjunct reads;
* the input/output/reference-input list lengths, the redeemer map and the
  DEFECT-D4 sharing of `mlH`/`mlCS`/`mlTn`/`mlTn2` between input 0 and output 0,
  all inherited verbatim from S1R;
* budget 3800.
The honest statement is "P2b does not need one token name per value", not "P2b is
unbounded".

COST, measured: the S1R2 `#prep_uplc` takes ~2 min 46 s (S1R: 13 s) and this
module's two solver calls take ~17 min together (S1R's five: 22 s).
-/
import WSC.Shaped.SeizeShapedR2
import WSC.Props.P2_Seize
import WSC.Realizability
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)
open WSC.SeizeModel (seizedPolicyOf pairedOutputsOf progLogicCredDataOf)

/-! ## §Projection audit — SHAPE S1R2 instantiates P2's own projections -/

section Leaves
variable (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
         (i0Qty i0Qty2 : Integer) (dIn : ByteString)
         (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
         (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
         (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
         (o1Qty o1Qty2 : Integer)
         (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer)
         (spRed mtRed ilRed : ByteString)
         (fee : Integer)

private abbrev r2Ctx : ScriptContext :=
  seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
    wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
    escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
    pHash pCS pTn pAda pQty dirCS plc glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee

/-- The seized policy at SHAPE S1R2 is `key`, exactly as at S1R. -/
theorem shapeR2_seizedPolicy :
    seizedPolicyOf
      (r2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some key := rfl

/-- The paired-output cursor at SHAPE S1R2 is the WHOLE output list. -/
theorem shapeR2_pairedOutputs :
    pairedOutputsOf
      (r2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some
        (r2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
          escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
          spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs := rfl

end Leaves

/-! ## §Redeemer coverage at SHAPE S1R2 — for every leaf assignment -/

section Cover
variable (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
         (i0Qty i0Qty2 : Integer) (dIn : ByteString)
         (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
         (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
         (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
         (o1Qty o1Qty2 : Integer)
         (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer)
         (spRed mtRed ilRed : ByteString) (fee : Integer)

private abbrev s2Ctx : ScriptContext :=
  seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
    wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
    escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
    pHash pCS pTn pAda pQty dirCS plc glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee

theorem seizeR2_wdrl_covered (hne : w0 ≠ w1) :
    Realizability.WdrlCovered
      (s2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro h n hmem
  simp [s2Ctx, seizeR2Ctx, seizeShapedWdrl] at hmem
  show findRedeemer (.Rewarding (.ScriptCredential h))
        (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [seizeR_findRewarding0]; exact Option.noConfusion
  · rw [seizeR_findRewarding1 _ _ _ _ _ _ hne]; exact Option.noConfusion

theorem seizeR2_spend_covered :
    Realizability.SpendCovered
      (s2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro i hin hscript
  simp [s2Ctx, seizeR2Ctx] at hin
  rcases hin with rfl | rfl
  · show findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
          (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none
    rw [seizeR_findSpending]; exact Option.noConfusion
  · simp [seizeShapedIn1, CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

theorem seizeR2_mint_covered :
    Realizability.MintCovered
      (s2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro cs m hmem
  simp [s2Ctx, seizeR2Ctx, Shape.mintTwoTN] at hmem
  obtain ⟨rfl, -⟩ := hmem
  show findRedeemer (.Minting _) (seizeRRedeemerMap _ w0 w1 spRed mtRed ilRed) ≠ none
  rw [seizeR_findMinting]; exact Option.noConfusion

end Cover

/-! ## §The bytecode obligation and its mandatory vacuity probe -/

/-- **MANDATORY VACUITY PROBE, at the S1R2 TERM and the S1R2 SHAPE.**  "No
accepting shape-S1R2 context exists within 3800 CEK steps" must be FALSIFIED, or
`P2b_R2_containment` would be vacuously true.  Expected: `Falsified`. -/
def P2_R2_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    ¬ isSuccessful
      (appliedSeizeR2Shaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)

#blaster (timeout: 1800) (gen-cex: 0) (solve-result: 1) [P2_R2_vacuity_probe]

/-- **P2 (b) — CONTAINMENT OF THE SEIZED DELTA, OVER MULTI-TOKEN-NAME VALUES,
PROVED AT UPLC.**

*For EVERY token name, the total holding of the seized policy at outputs sitting
on the mini-ledger base credential is at least the total holding at inputs spent
from it, plus the (signed) net mint of that asset* — over a shape whose values
carry TWO token names under the non-ada policy and whose mint carries two token
names of free sign.

Same postcondition, same budget, same base credential as `P2b_R_containment`;
the shape is strictly larger in the dimension the old caveat named. -/
theorem P2b_R2_containment :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    isSuccessful
      (appliedSeizeR2Shaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
            escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
            spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
              escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
              pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
                escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
                pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
                spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint
      := by blaster (timeout: 1800)

/-! ## §CONCRETE instances OF EXACTLY SHAPE S1R2, and their REALIZABILITY -/

namespace P2R2Witness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1R2 at a leaf assignment.  `TOK < TOKZ`, so both values and the mint
field are `validTxOutValue` / `validMintValue`-canonical, and the transaction
balances in all three columns:
ada `300 + 100 = 300 + 50 + 50`; `MMM.TOK  9 + 1 + 2 = 4 + 8`;
`MMM.TOKZ  7 + 0 + 2 = 3 + 6`. -/
def mk2 (i0Qty i0Qty2 o0Qty o0Qty2 : Integer) (escH : ByteString)
    (o1Qty o1Qty2 i1Qty mQ mQ2 : Integer) (oStk : ByteString) : ScriptContext :=
  seizeR2Ctx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") (ByteString.mk "TOKZ") i0Qty i0Qty2
      (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 (ByteString.mk "MMM") (ByteString.mk "TOK") i1Qty
    oStk 300 o0Qty o0Qty2 (ByteString.mk "DTM")
    escH 50 (ByteString.mk "MMM") (ByteString.mk "TOK") (ByteString.mk "TOKZ") o1Qty o1Qty2
    (ByteString.mk "MMM") (ByteString.mk "TOK") (ByteString.mk "TOKZ") mQ mQ2
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    (ByteString.mk "SPRED") (ByteString.mk "MTRED") (ByteString.mk "ILRED")
    50

/-- ACCEPTING: the residual-output shape every real seize golden has, with BOTH
token names of the seized policy split between the continuing output and a
residual output that is itself at the mini-ledger base credential. -/
def ctxResidual2 : ScriptContext :=
  mk2 9 7 4 3 (ByteString.mk "PROGLOGIC") 8 6 1 2 2 (ByteString.mk "USERSTK")

/-- LEDGER-LEGAL, REDEEMER-COVERED ESCAPE: byte-identical to `ctxResidual2`
except that output 1 sits OUTSIDE the mini-ledger, so both token names of the
seized policy leave it.  Must be rejected. -/
def ctxEscape2 : ScriptContext :=
  mk2 9 7 4 3 (ByteString.mk "CHANGE") 8 6 1 2 2 (ByteString.mk "USERSTK")

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- Both instances satisfy the theorem's ledger-normalization hypothesis and are
redeemer-covered. -/
theorem both_valid_and_covered :
    validRewardingContext ctxResidual2 = true ∧
    Realizability.redeemerCovered ctxResidual2 = true ∧
    validRewardingContext ctxEscape2 = true ∧
    Realizability.redeemerCovered ctxEscape2 = true := by native_decide

/-- **REALIZABILITY OF SHAPE S1R2 — the acceptance criterion.** -/
theorem ctxResidual2_realizable : Realizability.Realizable ctxResidual2 := by
  refine ⟨by native_decide, both_valid_and_covered.2.1, ?_, ?_, ?_⟩
  · apply seizeR2_wdrl_covered; decide
  · apply seizeR2_spend_covered
  · apply seizeR2_mint_covered

/-- **NON-VACUITY, EXECUTABLE, TWO-SIDED.**  The real compiled `programmableSeize`
HALTS on `ctxResidual2` at **2739** CEK steps and BUDGET-ERRORS at 2738, so `K`
is pinned exactly and 2739 < 3800 puts the witness inside the prepped budget.
(S1R's residual witness needs 2412; the second token name costs 327 steps.) -/
theorem K_R2_is_2739 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual2) 2739) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual2) 2738) = false := by native_decide

theorem exec_accepts_residual2 :
    isSuccessful (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
      (WSC.seizeInputs ppCS ctxResidual2) 3800) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED CASE, executed.**  The multi-token escape is rejected by the
real CEK at **20000** steps, so the rejection is genuine and not budget
exhaustion. -/
theorem exec_rejects_escape2 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxEscape2) 20000) = false := by native_decide

end P2R2Witness

end WSC

/-! ## §Axiom census -/

#print axioms WSC.P2b_R2_containment
#print axioms WSC.P2R2Witness.K_R2_is_2739
#print axioms WSC.P2R2Witness.exec_accepts_residual2
#print axioms WSC.P2R2Witness.exec_rejects_escape2
