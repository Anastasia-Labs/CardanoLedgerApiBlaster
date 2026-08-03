/-
WSC/Benchmark/CostG2200.lean — PREP-COST MEASUREMENT (2026-08-02).

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT. Build deliberately:

    lake build WSC.Benchmark.CostG2200

Companion to WSC/Benchmark/CostG2300.lean (read its header). MEASURED SAME DAY:
the 2300 rung dies in `INTERNAL PANIC: out of memory` at **783 s wall,
27.4 GB MaxRSS** under a 34 GiB `ulimit -v` — RSS ≈6.7 GB at minute 10, then an
explosive phase gaining ≈7 GB/min. (Uncapped, the same run earlier that day
reached 46 GB, was OOM-killed by the kernel, and took the whole WSL VM down —
run these ONLY under `ulimit -v`.)

This module brackets the attainable ceiling against P1's non-vacuity floor
(K_T8R = 2288, `WSC.P1RShapedWitness.K_T8R_is_2288`):

  * 1600 completes (37.8–594 s, ≤4.35 GB — BENCHMARK-PREP §5.1/§5.4);
  * 2300 = out-of-memory panic (above);
  * 2200 = THIS MODULE. If it also dies, the unshaped-prep ceiling of this
    validator is strictly below 2200 < 2288, i.e. **below the smallest budget
    at which an unshaped P1-class statement is non-vacuous** — and the
    "first target" of BENCHMARK-PREP §5.4 ("make anything at or above 2288
    work at all") is confirmed out of reach on a 61 GB box, pending upstream
    unroller work (Lean-blaster#138). If it completes, move the probe to 2288.

MEASURED (2026-08-02, same box/method as CostG2300, `ulimit -v` 32 GiB):
**`INTERNAL PANIC: out of memory` — 2828.5 s wall ≈ 47 min, MaxRSS
21,581,296 kB ≈ 21.6 GB.** Trajectory: a STABLE ≈5.2–5.3 GB grind for ~44
minutes (well below 2300's curve at every age), then the same explosive
endgame, gaining >15 GB in the final ~3 minutes until the allocator failed.

CONSEQUENCE, with the 2300 row and cost monotonicity in the budget: the
attainable unshaped-prep ceiling of this validator on a 61 GB box lies
STRICTLY BELOW 2200, hence strictly below the 2288 non-vacuity floor of P1.
There is no budget at which an unshaped P1-class statement can currently be
STATED against a real prep of this validator on this class of hardware. The
memory explosion, not wall time, is the binding wall — 2200 spends 94% of its
run flat at 5 GB before detonating, so no wall-clock patience helps.
-/
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC
namespace Benchmark

#prep_uplc appliedGlobal2200 programmableLogicGlobal1600 globalInputs1600 2200

end Benchmark
end WSC
