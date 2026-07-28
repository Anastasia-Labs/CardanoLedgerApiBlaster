-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/Probe/T3PrepFAILS.lean — **THIS MODULE DOES NOT BUILD. IT IS KEPT AS
THE REPRODUCTION OF AN UPSTREAM BLASTER DEFECT.** Nothing imports it; `lake build
WSC` does not reach it. Run it deliberately:

    lake build WSC.Shaped.Probe.T3PrepFAILS      # expected: kernel errors

WHAT IT TRIES TO DO (task V1 step 2, ARCHITECTURE.md Tier 3.1). SHAPE T3
(WSC/Shaped/GlobalShapedP1.lean) is SHAPE T1 with TWO token names per policy, so
`poutputsContainExpectedValueAtCred`'s dispatch (ProgrammableLogicBase.hs:676-699)
leaves the single-asset scan (PATH A, which SHAPES T1/T2/T6/T7 exercise) and takes
`checkWholesaleThenBuiltin` — PATH B (wholesale `Data` equality, :648-674) falling
through to PATH C (builtin `pvalueContains`, :619-647).

WHAT HAPPENS. `#prep_uplc` completes, and the residual it produces is CORRECT —
the error dump shows the intended condition
`containedInner [("",[("",outAda)]),(cs,[(tn0,qOut0),(tn1,qOut1)])] cs
[(tn0,qIn0),(tn1,qIn1)]`, i.e. exactly Path C's containment test. But the emitted
term is KERNEL-ILL-TYPED:

    (kernel) application type mismatch
      Blaster.dite' (true = PlutusCore.Value.containedInner … ) (fun x => Halt) (fun x => Error)
    argument has type    false = containedInner … → State
    but function has type (¬true = containedInner … → State) → State

i.e. the optimizer rewrote the ELSE branch's binder TYPE (`¬(true = b)` ⇝
`false = b`) without updating the `Blaster.dite'` motive. Semantically harmless,
kernel-fatal. Same root cause as WSC/Shaped/Probe/T4PrepFAILS.lean (there the
rewrite is De Morgan on `¬(A ∧ B)`).

CONSEQUENCE FOR THE CAMPAIGN: PATHS B and C of the containment dispatch are NOT
reachable at UPLC with this substrate, at any shape — the defect is in the
CIP-153 `pvalueContains` denotation's residual, not in this particular shape.
ARCHITECTURE.md Tier 3.1's "all three paths" therefore stands at 1 of 3 at UPLC
(Path A) plus Path C PROVED AT LEAN LEVEL in WSC/Props/P1_Transfer.lean
(`pathC_sound`, unconditional, no `sorry`). Recorded in
WSC/status-fragments/V1-P1-shaped.md.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT3 programmableLogicGlobal1600 p1ShapedTwoInputs 4400

end WSC
