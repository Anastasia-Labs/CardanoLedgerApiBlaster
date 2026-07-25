/-
WSC/Shaped/Probe/T4PrepFAILS.lean — **THIS MODULE DOES NOT BUILD. IT IS KEPT AS
THE REPRODUCTION OF AN UPSTREAM BLASTER DEFECT.** Nothing imports it. Run it
deliberately:

    lake build WSC.Shaped.Probe.T4PrepFAILS      # expected: kernel errors

WHAT IT TRIES TO DO (task V1 step 4, the task's preferred growth step). SHAPES
T4/T5 (WSC/Shaped/GlobalShapedP1Agg.lean) give SHAPE T1/T2 a SECOND mini-ledger
input, so containment has to aggregate on the INPUT side. Two contributing inputs
put `pvalueFromCred` into PHASE 3 `goBuiltin` (ProgrammableLogicBase.hs:446-458),
whose accumulator is the CIP-153 builtin `punionValue` and whose exit bridge is
`pinsertCoin # "" # "" # 0`.

WHAT HAPPENS. `#prep_uplc` completes with a CORRECT residual — the error dump
shows `Blaster.dite' (qOut < qIn0.add qIn1) (fun x => Error) (fun x => Halt)`,
i.e. the aggregated containment test, exactly as intended — but the term is
KERNEL-ILL-TYPED at the builtin's 128-bit range guard:

    (kernel) application type mismatch
      Blaster.dite' (¬ qIn0+qIn1 < -2^127 ∧ ¬ -1+2^127 < qIn0+qIn1) …
    argument has type    (qIn0+qIn1 < -2^127 ∨ -1+2^127 < qIn0+qIn1) → State
    but function has type (¬(¬ qIn0+qIn1 < -2^127 ∧ ¬ -1+2^127 < qIn0+qIn1) → State) → State

i.e. the optimizer De-Morgan-normalized the ELSE branch's binder TYPE without
updating the `Blaster.dite'` motive. Same root cause as
WSC/Shaped/Probe/T3PrepFAILS.lean (there the rewrite is Bool polarity
`¬(true = b)` ⇝ `false = b`).

SCOPE OF THE BLOCKAGE — WIDER THAN THIS SHAPE. `punionValue` sums the LOVELACE
entry of the two canonical values it merges, so the guard fires on
`inAda0 + inAda1` for EVERY two-contributing-input shape, whatever the policies
are. Phase 3 of `pvalueFromCred` is therefore unreachable at UPLC with this
substrate, and with it ARCHITECTURE.md §3-P1's lemma L1.3 on shapes with more
than one mini-ledger input. The OUTPUT-side aggregation dimension does not go
through any builtin (Path A adds with plain Integer addition) and IS proved —
SHAPES T6/T7, `WSC/Props/Shaped/P1Shaped.lean` §5.

The shape definitions themselves are fine and are still used: the K measurements
and the source-model cross-check in WSC/Shaped/Probe/T4Probe.lean build and pass
(SHAPE T4 K = 3001, SHAPE T5 burn K = 3970, model accepts/rejects as expected).
Recorded in WSC/status-fragments/V1-P1-shaped.md.
-/
import WSC.Shaped.GlobalShapedP1Agg
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT4 programmableLogicGlobal1600 p1ShapedAggInputs 4400
#prep_uplc appliedGlobalShapedT5 programmableLogicGlobal1600 p1ShapedAggMintInputs 4400

end WSC
