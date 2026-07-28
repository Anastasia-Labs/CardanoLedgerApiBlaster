/-
WSC/Shaped/GlobalShapedP1BCPrep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over the NODE-REALIZABLE re-cuts **SHAPE T3R** (containment
dispatch PATHS B/C) and **SHAPE T4R** (input-side builtin accumulation), at CEK
step budget **4400** (task H2).

The shapes and the reason they exist: `WSC/Shaped/GlobalShapedP1BC.lean`'s
header. The budget is SHAPE T1R's, so the before/after comparison is at equal
budget; the witness K is pinned two-sided in
`WSC/Props/Shaped/P1ShapedBC.lean`.

⚠ THESE TWO PREPS EXIST ONLY BECAUSE UPSTREAM BLASTER DEFECT **D6** IS FIXED
(`Lean-blaster-wsc` @ `4d320dd`, `Blaster/Optimize/Rewriting/OptimizeITE.lean`).
Before that fix `#prep_uplc` emitted a kernel-ill-typed `Blaster.dite'` whenever
a CIP-153 `Value` builtin's result stayed symbolic — which is precisely what
`pvalueContains` (PATH C) and `punionValue` (PHASE 3) do on these shapes. The two
reproductions, now regression tests, are `WSC/Shaped/Probe/T3PrepFAILS.lean` and
`WSC/Shaped/Probe/T4PrepFAILS.lean`.
-/
import WSC.Shaped.GlobalShapedP1BC
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT3R programmableLogicGlobal1600 p1BCShapedInputs 4400
#prep_uplc appliedGlobalShapedT4R programmableLogicGlobal1600 p1AggRInputs 4400

end WSC
