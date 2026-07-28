-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Shaped/GlobalShapedP1Prep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over **SHAPE T1** (pure transfer, one registered policy, one
token name, PATH A) at CEK step budget **4400** (task V1).

Same flat and same validator as WSC/Prep/Global1600.lean; the only differences
are the context argument (a shape instead of a universally quantified
`ScriptContext`) and the budget.

WHY 4400 (measured, `WSC/Shaped/Probe/T1Probe.lean`):
* the concrete accepting SHAPE-T1 witness halts in **K = 2603** CEK steps;
* the SHAPE-T2 witnesses (nonzero mint / burn) halt in **K = 3572**;
* the SHAPE-T3 witness (two token names, wholesale arm) halts in **K = 2083**.
4400 is one round budget above all three, so the same number can be quoted for
every P1 shape, and it leaves ≈820 steps of headroom over the most expensive.

WHY THIS BUDGET IS NOW AFFORDABLE. `WSC/Prep/Global1600.lean` records symbolic
prep of this validator at 1600 as 2143 s and extrapolates the containment-carrying
budgets (K = 3262 / 3726) at 7-182 YEARS. Shaped prep is budget-independent
(WSC/SHAPING-RESULTS.md §2.5): measured here at **0.97 s @ 2700 and 1.00 s
@ 4400**. That is the whole reason P1-at-UPLC is reachable at all.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT1 programmableLogicGlobal1600 p1ShapedInputs 4400

end WSC
