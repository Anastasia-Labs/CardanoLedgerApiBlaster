/-
WSC/Benchmark/CostG2300.lean — PREP-COST MEASUREMENT (2026-08-02).

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT. Build deliberately:

    lake build WSC.Benchmark.CostG2300

Same class of temporary module as the CostG2600/CostG3300 rows of
WSC/BENCHMARK-PREP.md §5.1. Purpose: locate the unshaped `#prep_uplc` wall of
the global (transfer) validator BETWEEN the two existing measured points —
1600 (completes: 37.8–594 s, 16× variance) and 2600 (killed at the 15-min cap,
7.18 GB RSS still climbing).

WHY 2300: it is the smallest round budget STRICTLY ABOVE K_T8R = 2288
(`WSC.P1RShapedWitness.K_T8R_is_2288`, the cheapest measured accepting
REGISTERED transfer), i.e. the smallest budget at which an unshaped P1-class
statement stops being vacuous. BENCHMARK-PREP §5.4's slope (marginal cost
doubling every ≈150 budget steps, and steepening) extrapolates 1600→2300 at
≈25× ≈ 90 min from the 217 s sample — treat as a LOWER bound.

A completion here, at ANY cost, changes the P1-unshaped picture qualitatively:
it would be the first accept-capable unshaped prep of this validator, the
prerequisite for transplanting the P4 destructure technique to a P1-class
claim. A kill at the cap moves the known wall interval to (1600, 2300].

MEASURED (2026-08-02, 32-core / 61 GB box, warm deps, `ulimit -v` 34 GiB):
**`INTERNAL PANIC: out of memory` — 783 s wall, MaxRSS 27,385,380 kB ≈ 27.4 GB.**
The RSS trajectory is the finding: ≈6.7 GB at minute 10 (gentle, ≈0.6 GB/min,
tracking the killed @2600 row of BENCHMARK-PREP §5.5), then an EXPLOSIVE phase
gaining ≈7 GB/min until the allocator fails. An uncapped run of this same
module earlier that day reached **46 GB anon-RSS, was OOM-killed by the kernel
(`Killed process … (lean) … anon-rss:46047640kB`), and took the whole WSL VM
down** — which is why the cap is now mandatory (run ONLY under `ulimit -v`).

So the 2300 rung is not "slow": it is MEMORY-infeasible on a 61 GB box, and
the wall is a cliff inside (1600, 2300], not a smooth doubling. See
WSC/Benchmark/CostG2200.lean for the bracketing point against the 2288 floor.
-/
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC
namespace Benchmark

#prep_uplc appliedGlobal2300 programmableLogicGlobal1600 globalInputs1600 2300

end Benchmark
end WSC
