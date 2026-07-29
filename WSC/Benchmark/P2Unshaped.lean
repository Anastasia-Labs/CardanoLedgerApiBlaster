/-
╔══════════════════════════════════════════════════════════════════════════════╗
║  WSC/Benchmark/P2Unshaped.lean                                               ║
║                                                                              ║
║  ⛔ THIS MODULE DOES NOT BUILD, ON PURPOSE. IT IS A BENCHMARK, NOT A RESULT.  ║
║                                                                              ║
║  It is IMPORTED BY NOTHING — not by `WSC.lean`, not by `WSC/ShapeBridge.lean`,║
║  not by any probe. `lake build WSC WSC.ShapeBridge` does not see it and CI    ║
║  does not build it. To run it deliberately:                                   ║
║                                                                              ║
║      lake build WSC.Benchmark.P2Unshaped                                     ║
║                                                                              ║
║  MEASURED 2026-07-29 (`timeout -s KILL 900`): the `#prep_uplc` below was      ║
║  still inside elaboration when the 15-minute cap fired — **887.1 s, killed,   ║
║  no output, no error**. Neither `blaster` call under it is reached. Budget     ║
║  2000 fails the same way (>892.9 s) against **1.75 s** at 600, and the         ║
║  library's earlier runs recorded 2000 unfinished at 77 min and 9000 at 62 min. ║
║                                                                              ║
║  ⚠️ NOTHING IN THIS FILE IS CLAIMED AS A RESULT. Both obligations are OPEN.   ║
║  P2 against production is PROVED, over SHAPED contexts, in                    ║
║  `WSC/Props/Shaped/P2ShapedR.lean` (`P2a_R_structure`, `P2a_R_ada_only_tops_up`,║
║  `P2b_R_containment`) and `WSC/Props/Shaped/P2ShapedR2.lean`                  ║
║  (`P2b_R2_containment`) — that is the result; this is the wish.               ║
╚══════════════════════════════════════════════════════════════════════════════╝

════════════════════════════════════════════════════════════════════════════
WHAT THE ARTIFACT IS
════════════════════════════════════════════════════════════════════════════
The **UNSHAPED** UPLC-level statement of P2 (seize), BOTH conjuncts — structure
preservation and containment of the seized delta — over a FULLY SYMBOLIC
`ScriptContext`. Same two purposes as its transfer-side sibling
`WSC/Benchmark/P1Unshaped.lean`: it puts on record what we actually want to prove,
and it hands the Blaster team a REAL production `#prep_uplc` workload with a REAL
proof obligation on top of it. Corroborates upstream
`input-output-hk/Lean-blaster#138`.

Why this one is the more interesting benchmark of the two: `programmableSeize`
carries the `pvalueEqualsDeltaCurrencySymbol` delta walk and the CIP-153
`ScaleValue` builtin, its accept path is the most expensive of the four
validators, and it is the validator on which the unshaped unroller has failed by
the widest margin.

════════════════════════════════════════════════════════════════════════════
WHY THE BUDGET IS 3800 AND MUST NOT BE LOWERED TO MAKE IT BUILD
════════════════════════════════════════════════════════════════════════════
Below the minimal accepting step count the `isSuccessful` hypothesis is
UNSATISFIABLE and both statements are VACUOUS — true and worthless. The ONLY
unshaped seize prep that exists is `WSC.appliedSeize` at budget 600
(`WSC/Prep/Seize.lean`, measured **1.75 s**), and the E2 spike PROVED there is no
accepting context inside 600 steps, which is why that module's own header forbids
stating any P-theorem against it. Re-measured for THESE statements: both
`P2a_unshaped_stmt` and `P2b_unshaped_stmt` instantiated at `appliedSeize.prop`
come back `✅ Valid` **inside the optimization phase, in 0.245 s / 0.243 s**,
before any SMT translation — the signature of a refuted accept hypothesis, i.e.
VACUOUS.

Measured minimal accepting K on this bytecode, each pinned TWO-SIDED (`Halt` at K,
budget-`Error` at K−1) and measured on the SAME unshaped
`programmableSeize.script` + `WSC.seizeInputs` pair this module preps:

* **2301** and **2412** — `WSC.P2RWitness.K_is_2301_and_2412` (SHAPE S1R's
  accepting and residual-output witnesses);
* **2739** — `WSC.P2R2Witness.K_R2_is_2739` (SHAPE S1R2, two token names).

Real off-chain accepting seize goldens cost 2,305 and 2,905 steps
(`WSC/goldens/K-MEASUREMENTS.md` §3, re-measured at task N5). 3800 is the budget
the four shaped P2 theorems already use, so the benchmark and the proved results
are at the SAME budget and the only difference is the shape.
`WSC.Benchmark.P2_unshaped_nonvacuous_at_3800_and_vacuous_at_600`
(`WSC/Benchmark/P2UnshapedStatement.lean` §5) certifies non-vacuity at 3800 and
vacuity at 600 executably.

**So: do not lower the budget. A vacuous benchmark is worse than none.**

════════════════════════════════════════════════════════════════════════════
WHERE TO READ THE STATEMENTS — THEY ARE NOT IN THIS FILE
════════════════════════════════════════════════════════════════════════════
`WSC/Benchmark/P2UnshapedStatement.lean` carries `P2aUnshapedForm` and
`P2bUnshapedForm`, the THREE hypotheses that separate them from
`P2a_R_structure` / `P2b_R_containment` and why none of the three is optional,
FIVE `rfl` audits that those hypotheses hold of SHAPES S1R and S1R2 for all
leaves, THREE kernel-checked specialisation theorems (to `P2a_R_structure`,
`P2b_R_containment` and `P2b_R2_containment` at the same `accept`), and the
executable non-vacuity certificate. **That module BUILDS** (`lake build
WSC.Benchmark.P2UnshapedStatement`, ≈1.4 s warm, 0 errors, no `sorryAx`).

All this module adds is the prep and the instantiation of `accept`.
-/
import WSC.Benchmark.P2UnshapedStatement
import WSC.Prep.Seize
import Blaster

-- `#prep_uplc` dies on `maxHeartbeats` long before it dies on wall clock
-- (SPIKE-FINDINGS), and the point of this module is to reach the wall clock.
set_option maxHeartbeats 0

namespace WSC
namespace Benchmark

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## The unshaped prep at the shaped theorems' own budget

`programmableSeize` is the DECODED production flat (`WSC/Prep/Seize.lean`; sha256
in `WSC/flats/PROVENANCE.md`; it decodes only against the CIP-153-capable
PlutusCoreBlaster pinned in `lakefile.lean` — without `ScaleValue`, flat tag 100,
it does not decode at all) and `WSC.seizeInputs` is its audited
parameter/context application order: `toTerm ppCS :: rewardingInputs ctx`, a
PURPOSE DISCRIMINATOR in the same class as upstream CLAB's `proposingInputs`,
freezing no list length, no constructor tag and no `Option` presence.

Contrast `WSC/Shaped/SeizeShapedR.lean`, which preps the SAME flat at the SAME
budget 3800 over SHAPE S1R and completes in **7.22 s** (measured, shape
definitions included); `WSC/Shaped/SeizeShapedR2.lean` — the two-token-name shape,
the most expensive shaped prep in the library — takes **84.11 s**. So shaped preps
are not uniformly ≈1 s; the cheapness comes from the CLOSED `Data` SKELETON, not
from the shape being small. -/
#prep_uplc appliedSeizeU3800 programmableSeize seizeInputs 3800

/-! ## The obligations — both conjuncts -/

/-- **P2 (a), UNSHAPED, at budget 3800 — BENCHMARK OBLIGATION.**

`P2aUnshapedForm` with `accept` instantiated to the real bytecode's prepped
residual. Spelled out:

    ∀ ppCS ctx key plc pairedOuts,
      validRewardingContext ctx →
      SeizeModel.seizedPolicyOf ctx = some key →
      progLogicCredPublishedBySeize ctx = some (toData (ScriptCredential plc)) →
      SeizeModel.pairedOutputsOf ctx = some pairedOuts →
      isSuccessful (appliedSeizeU3800.prop ppCS ctx) →
        WSC.seizeStructurePreservedAdaTopUp (ScriptCredential plc) key
          ctx.…txInfoInputs pairedOuts = true

The ada clause of the postcondition is an INEQUALITY IN ONE DIRECTION
(`in ≤ out`). Restoring the pre-#112 EQUALITY gives `WSC.pairPreserved`, which is
❌ FALSIFIED against this bytecode; dropping the clause entirely would let a
seizure drain the victim's lovelace, which the bytecode also refuses
(`WSC.P2a_R_negative_control`). Do not touch it. -/
def P2a_unshaped_stmt : Prop :=
  P2aUnshapedForm (fun (ppCS : CurrencySymbol) (ctx : ScriptContext) =>
    isSuccessful (appliedSeizeU3800.prop ppCS ctx))

/-- **P2 (b), UNSHAPED, at budget 3800 — BENCHMARK OBLIGATION.**

    ∀ ppCS ctx key plc tn,
      validRewardingContext ctx →
      SeizeModel.seizedPolicyOf ctx = some key →
      progLogicCredPublishedBySeize ctx = some (toData (ScriptCredential plc)) →
      isSuccessful (appliedSeizeU3800.prop ppCS ctx) →
        WSC.P2.sumOutAtBase (ScriptCredential plc) key tn ctx.…txInfoOutputs
          ≥ WSC.P2.sumInAtBase (ScriptCredential plc) key tn ctx.…txInfoInputs
            + WSC.mintOf key tn ctx.…txInfoMint

The mint is SIGNED (`WSC.mintOf = valueOf`): a legitimate burn of the seized
policy lowers the requirement. -/
def P2b_unshaped_stmt : Prop :=
  P2bUnshapedForm (fun (ppCS : CurrencySymbol) (ctx : ScriptContext) =>
    isSuccessful (appliedSeizeU3800.prop ppCS ctx))

/-- **OPEN.** Not reached — the `#prep_uplc` above does not terminate. Kept as a
`theorem` so the artifact is a real proof obligation the moment the prep
completes. Cap is explicit: `blaster`'s default solver timeout is INFINITE. -/
theorem P2a_unshaped : P2a_unshaped_stmt := by blaster (timeout: 1800)

/-- **OPEN.** Same. -/
theorem P2b_unshaped : P2b_unshaped_stmt := by blaster (timeout: 1800)

end Benchmark
end WSC
