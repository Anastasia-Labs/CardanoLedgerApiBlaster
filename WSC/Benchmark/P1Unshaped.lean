/-
╔══════════════════════════════════════════════════════════════════════════════╗
║  WSC/Benchmark/P1Unshaped.lean                                               ║
║                                                                              ║
║  ⛔ THIS MODULE DOES NOT BUILD, ON PURPOSE. IT IS A BENCHMARK, NOT A RESULT.  ║
║                                                                              ║
║  It is IMPORTED BY NOTHING — not by `WSC.lean`, not by `WSC/ShapeBridge.lean`,║
║  not by any probe. `lake build WSC WSC.ShapeBridge` does not see it and CI    ║
║  does not build it. To run it deliberately:                                   ║
║                                                                              ║
║      lake build WSC.Benchmark.P1Unshaped                                     ║
║                                                                              ║
║  MEASURED 2026-07-29 (`timeout -s KILL 900`): the `#prep_uplc` below was      ║
║  still inside elaboration when the 15-minute cap fired — **894.6 s, killed,   ║
║  no output, no error**, RSS climbing monotonically to 8.88 GB at 12.5 min     ║
║  with no plateau. The `blaster` call under it is never reached.               ║
║  Budget 2600 also fails (>894 s), so the wall is BELOW even the smallest      ║
║  non-vacuous rung, let alone the mainnet-ceiling budget this module asks for. ║
║                                                                              ║
║  ⚠️ NOTHING IN THIS FILE IS CLAIMED AS A RESULT. `P1_unshaped` is an OPEN     ║
║  obligation. P1 against production bytecode is PROVED, over SHAPED contexts,  ║
║  in `WSC/Props/Shaped/P1ShapedR.lean` (`P1R_T1` / `P1R_T2` / `P1R_T6` /       ║
║  `P1R_T7`, all `✅ Valid`) — that is the result; this is the wish.            ║
╚══════════════════════════════════════════════════════════════════════════════╝

════════════════════════════════════════════════════════════════════════════
WHAT THE ARTIFACT IS, AND WHO IT IS FOR
════════════════════════════════════════════════════════════════════════════
The **UNSHAPED** UPLC-level statement of P1 (transfer containment): the property
we actually want to prove, over a FULLY SYMBOLIC `ScriptContext` rather than over
a shape. Two purposes, in this order:

1. **It is on record as what we want.** Every P1 result this library publishes is
   bounded by a SHAPE — a `ScriptContext` whose whole `Data` skeleton is closed
   (docs/METHOD.md §2/§3). That bound is the largest single caveat on the
   campaign. This module says, in machine-checkable form, what the unbounded
   claim is, so nobody has to reconstruct it from prose.

2. **It is a BENCHMARK for the Blaster team.** `#prep_uplc` is the
   elaboration-time symbolic unroller, and on a fully symbolic context its cost
   explodes in the CEK budget: on this exact validator, measured 2026-07-29,
   600 → **2.42 s**, 1600 → **217 s**, and 2600 / 3300 / 4400 all **killed at a
   15-minute cap**. (An earlier run of the 1600 module took 37.8 s and another
   594 s — the variance on that one module is 16×; see WSC/BENCHMARK-PREP.md §5.4
   before quoting any single figure.) This module asks for 300000 — the mainnet ex-unit ceiling (derivation below), i.e. the budget at which a verdict covers EVERY mainnet-payable transfer. It is a REAL
   production workload — the compiled `programmableLogicGlobal` from wsc-poc
   `main` @ 2306678, 3444 term nodes, 282 builtin occurrences including 46
   CIP-153 `Value` builtins — with a REAL proof obligation on top of it, not a
   synthetic stressor. If `#prep_uplc`
   is optimised until this module builds and returns a verdict, the caveat above
   is gone.

Corroborates upstream `input-output-hk/Lean-blaster#138`.

════════════════════════════════════════════════════════════════════════════
WHY THE BUDGET IS 300000: IT IS THE MAINNET EX-UNIT CEILING
════════════════════════════════════════════════════════════════════════════
The budget is not a tuning knob — it is the point of the artifact. A verdict at
budget N proves the property for every accepting run that fits in N CEK steps.
For the benchmark to mean "P1 holds for EVERY transfer mainnet can carry", N must
be at least the largest step count a mainnet transaction can pay for.

DERIVATION (from `maxTxExecutionUnits` and the measured per-step rates in
`WSC/goldens/K-MEASUREMENTS.md` **§2, the post-#112 table** — nine accepting
goldens, all four validators, PCB's metered CEK reproducing the ledger's ExBudget
TO THE UNIT):

    CPU  ceiling:  10,000,000,000 / 18,129 CPU-per-step ≈ 551,594 steps
    MEM  ceiling:      14,000,000 /  54.46 mem-per-step ≈ 257,081 steps  ← BINDS

So the MEMORY budget, not the CPU budget, is the binding constraint, and no
accepting run of this validator inside mainnet limits exceeds ≈257k CEK steps.
**300000** is that ceiling rounded up with ≈16.7% margin, so that a step mix
cheaper than any measured golden is still covered.

Caveat, stated because it bounds the claim: 54.46 is the CHEAPEST memory-per-step
observed on THIS validator family (the band is 54.46–55.38, tight across all nine
post-#112 goldens). A hypothetical accepting run built from cheaper steps than any
measured one would raise the step ceiling; the margin absorbs a 16.7% drop and no
more.
Re-derive if `maxTxExecutionUnits` or the cost model changes.

NON-VACUITY IS PRESERVED, A FORTIORI. Raising the budget only ADMITS more
accepting runs, so every witness that certified the old rung still certifies this
one: the cheapest measured accepting registered transfer is 2288
(`WSC.P1RShapedWitness.K_T8R_is_2288`), P1's own four shapes cost 2343 / 2567 /
2777 / 2567, each pinned TWO-SIDED (`Halt` at K, budget-`Error` at K−1), and a
real off-chain golden costs 2782. All are ≤ 300000.
`WSC.Benchmark.P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600`
(`WSC/Benchmark/P1UnshapedStatement.lean` §4) certifies executably that an
accepting context exists at 4400 and that NONE exists at 1600 — the lower pin is
what rules out a vacuous statement, and it is unaffected by the raise.

THE RUNGS, ALL EXPRESSED AS COVERAGE OF THE CEILING (edit the one literal on the
`#prep_uplc` line; each is a real proof obligation, not a smoke test):

    budget   4,400  =  1.7% of ceiling — smallest NON-VACUOUS rung; the budget
                       the four shaped P1 theorems use. Prep already does not
                       terminate here.
    budget  25,700  =   10% of ceiling — intermediate progress marker.
    budget  64,300  =   25% of ceiling
    budget 128,500  =   50% of ceiling
    budget 300,000  =  100% + margin — THIS MODULE. A verdict here IS P1 for
                       every transfer a mainnet transaction can carry: no shape
                       family, no residual, no budget caveat.

Below 4,400 the statement is still true but the SMALLEST rung is where vacuity
starts to bite: at 1600 no accepting context exists at all
(`WSC.global_vacuity_probe_600` proves the same for 600, `✅ Valid`), so a
verdict there proves nothing. Do not go below 4,400.

════════════════════════════════════════════════════════════════════════════
WHERE TO READ THE STATEMENT — IT IS NOT IN THIS FILE
════════════════════════════════════════════════════════════════════════════
`WSC/Benchmark/P1UnshapedStatement.lean` carries the statement (`P1UnshapedForm`),
the ONE hypothesis that separates it from `P1R_T1_stmt` and why that hypothesis
is not optional, FOUR kernel-checked specialisation theorems showing
`P1UnshapedForm accept` implies the bodies of `P1R_T1_stmt` / `P1R_T2_stmt` /
`P1R_T6_stmt` / `P1R_T7_stmt` at the same `accept`, and the executable
non-vacuity certificate. **That module BUILDS** (`lake build
WSC.Benchmark.P1UnshapedStatement`, ≈1.3 s warm, 0 errors, no `sorryAx`), which
is the point of the split: the intractable prep must not take the reviewable
statement down with it.

All this module adds is the prep and the instantiation of `accept`.
-/
import WSC.Benchmark.P1UnshapedStatement
import WSC.Prep.GlobalImport
import Blaster

-- `#prep_uplc` dies on `maxHeartbeats` long before it dies on wall clock
-- (SPIKE-FINDINGS), and the whole point of this module is to reach the wall
-- clock. Also: `blaster`'s default solver timeout is INFINITE, so the call below
-- carries an explicit cap — house rule, CONTRIBUTING.md.
set_option maxHeartbeats 0

namespace WSC
namespace Benchmark

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## The unshaped prep at the mainnet ex-unit ceiling

`programmableLogicGlobal1600` is the DECODED production flat
(`WSC/Prep/GlobalImport.lean`; sha256 in `WSC/flats/PROVENANCE.md`) and
`globalInputs1600` is its audited parameter/context application order — a PURPOSE
DISCRIMINATOR (`toTerm ppCS :: rewardingInputs ctx`), the same class of inputs
function as upstream CLAB's `proposingInputs`/`spendingInputs`, freezing no list
length, no constructor tag and no `Option` presence. This is the unshaped
baseline; contrast `WSC/Shaped/GlobalShapedP1RPrep.lean`, which preps the same
flat at the same budget over a shape and completes in **1.51 s** (measured).

The `1600` in the name is the module the DECODE lives in, not a budget. -/
#prep_uplc appliedGlobalUCeiling programmableLogicGlobal1600 globalInputs1600 300000

/-! ## The obligation -/

/-- **P1, UNSHAPED, AT THE MAINNET EX-UNIT CEILING — THE BENCHMARK OBLIGATION.**

`P1UnshapedForm` (`WSC/Benchmark/P1UnshapedStatement.lean` §2) with the accept
predicate instantiated to the real bytecode's prepped residual. Spelled out, this
is:

    ∀ ppCS ctx cs tn dirCS plc,
      validRewardingContext ctx →
      paramsPublishedBy ctx = some (dirCS, toData (ScriptCredential plc)) →
      Model.coveringNodeExists dirCS cs ctx.…txInfoReferenceInputs = false →
      isSuccessful (appliedGlobalUCeiling.prop ppCS ctx) →
        Model.outSum (.ScriptCredential plc) cs tn ctx.…txInfoOutputs
          ≥ Model.inSum (.ScriptCredential plc) cs tn ctx.…txInfoInputs
            + Model.mintSigned cs tn ctx.…txInfoMint

The mint is SIGNED. The `max(mint, 0)` variant is machine-refuted on a burn
(`WSC.P1RShapedWitness.mintPos_form_REFUTED`); do not "repair" it. -/
def P1_unshaped_stmt : Prop :=
  P1UnshapedForm (fun (ppCS : CurrencySymbol) (ctx : ScriptContext) =>
    isSuccessful (appliedGlobalUCeiling.prop ppCS ctx))

/-- **OPEN.** Not reached: the `#prep_uplc` above does not terminate, so this
declaration is never elaborated. Kept as a `theorem` and not a comment so that
the artifact is a real proof obligation the moment the prep completes.

The cap is deliberate and is the house rule: `blaster`'s default solver timeout
is INFINITE. 1800 s is chosen to match the shaped P1 theorems' own
`(timeout: 1500)` with margin, not because it is expected to be enough — if the
prep is ever fixed, the FIRST measurement to take is whether the solve is
tractable at all, and `⚠️ Undetermined` hard-fails the build rather than
admitting (docs/METHOD.md §2.2: an unshaped goal at 300 s and 3,000 s returns the
same `Undetermined`, so give it one honest attempt with an explicit cap). -/
theorem P1_unshaped : P1_unshaped_stmt := by blaster (timeout: 1800)

end Benchmark
end WSC
