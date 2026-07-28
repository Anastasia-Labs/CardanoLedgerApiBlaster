/-
WSC/Shaped/Probe/D9Budget.lean — **SHAPE G6R IS ACCEPT-CAPABLE AT BUDGET 2400**,
and a historical bisection (task N4).

⚠ NAME. Written to bisect a supposed defect "D9". **THERE IS NO D9** — it was an
artifact of a bad workspace patch to Blaster, retracted in
`WSC/pr/05-blaster-issue-d9-bv-overflow.md`. What survives is the measurement:
SHAPE G6R accepts inside 2400 steps (new K = 2196), i.e. P6\'s shape does not
need the 3300 it is prepped at. The probe below is the evidence, and the trap
named at the end of this header is the reason it is a probe and not an
assertion.

FIRST BISECTION (WSC/Shaped/Probe/D9Probe.lean) REFUTED the obvious hypothesis.
D9 is NOT the CIP-153 mint merge: the SHAPE G1R vacuity probe has a nonzero mint,
goes through `punionValue`, and returns `✅ Expected Falsified` normally. So the
128-bit range guard is not what makes the SMT backend say "Overflow encountered
when expanding vector".

What is left that separates the two: G1R is prepped at budget **1600**, G6R at
**3300**. The remaining hypothesis is that D9 is a SIZE effect — the residual
term at 3300 is large enough for the backend to fail while the one at 1600 is
not. This module tests it by re-prepping the SAME SHAPE G6R at a LOWER budget
and running the SAME vacuity probe.

WHY 2400 IS THE BUDGET TO TRY. The G6R witness's exact step count was
RE-MEASURED against the PR #112 bytecode at **K = 2196** (it was 2837 before —
a 22.6 % drop, in line with the 6.5-14.7 % reductions unit N2 measured on the
global goldens). 2400 is therefore still accept-capable with 204 steps of
headroom, while cutting 900 steps of symbolic unrolling.

⚠ THE TRAP THIS IS WALKING TOWARDS, NAMED IN ADVANCE. Lowering a budget is
exactly how SHAPE G6 was once silently accept-UNSAT at 2500 — the theorem went
`✅ Valid` for the empty reason and only the vacuity probe caught it. So the
probe below is not a formality: if it returns `Valid` instead of `Falsified`,
budget 2400 is vacuous and NOTHING may be stated against this prep. The probe is
the deliverable of this module; a passing theorem here would mean nothing without
it.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.GlobalImport
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (CurrencySymbol validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

#prep_uplc appliedG6R2400 programmableLogicGlobal1600 memberRShapedInputs 2400

/-- **MANDATORY VACUITY PROBE, SHAPE G6R AT BUDGET 2400.** Expected
`Falsified`. If this says `Valid`, budget 2400 is vacuous — see the warning in
this module's header. -/
def D9_G6R_2400_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 qq0 : Integer)
    (ob1 : ByteString) (outAda1 qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer) (fee : Integer),
    validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    ¬ isSuccessful
      (appliedG6R2400.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [D9_G6R_2400_vacuity]

end WSC
