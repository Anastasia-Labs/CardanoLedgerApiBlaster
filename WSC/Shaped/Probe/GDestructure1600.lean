/-
WSC/Shaped/Probe/GDestructure1600.lean — PROBE (P4-technique transfer), v2.

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT MODULE. Build deliberately:

    lake build WSC.Shaped.Probe.GDestructure1600

════════════════════════════════════════════════════════════════════════════
WHAT THIS MEASURES, AND WHAT v1 ALREADY MEASURED THE HARD WAY
════════════════════════════════════════════════════════════════════════════
P4a was closed OVER THE UNSHAPED PREP by proof-time destructuring: `match` the
`ScriptContext`/redeemer `Data` skeleton apart in the PROOF and hand each
constructor-concrete leaf to `blaster` (`WSC/Props/P4_MintingIdx.lean` is the
literal-index rung of the same move). This probe asks whether that move
survives contact with the GLOBAL (transfer) validator against the UNSHAPED
`appliedGlobal1600` prep — the only accept-capable unshaped prep of this
validator that exists (accepting runs exist at K = 1402 post-#112, pinned by
`P5ShapedWitness.K_is_1402`; `WSC.NonVacuity.globalNonVacuous_at_1600`).

MEASURED, v1 (2026-08-02, tactic-level form): a first cut of this probe
destructured IN TACTIC MODE — `match ctx`, then `cases red` (5 `Data`
constructors) with the hypothesis `redTag red = some 1` — so every branch goal
carried its own instance of the 1600-step residual. The single stanza-A leaf
was still inside Blaster's Lean-side per-goal processing after ≥15 min at
≥4.2 GB RSS (never reached Z3; the fully-symbolic control on this same prep
needs 10–13 s of per-goal optimization, WSC/BENCHMARK-PREP.md §6.2), and the
session ended in a box-level OOM: the kernel killed a 46 GB `lean`
(`Out of memory: Killed process … (lean) … anon-rss:46047640kB`) and the WSL VM
restarted. A concurrent `#prep_uplc … 2300` run (WSC/Benchmark/CostG2300.lean)
was live at 6.6 GB when last sampled, so the 46 GB victim's identity is not
recoverable from the logs the reboot destroyed — but EITHER attribution is a
wall: tactic-level destructure multiplies a residual whose single instance
costs GBs to re-optimize. Hence v2:

v2 (this file) states the destructured skeleton IN THE THEOREM — the concrete
constructor sits inside the `prop` application from the start, there is no
`cases`, no motive instantiation, ONE goal per stanza, and `blaster` runs
exactly once per stanza. The quantified class is unchanged (the v1 hypothesis
`redTag red = some 1` is the same class as quantifying `flds` under
`Data.Constr 1 flds`, by trivial repackaging).

Stanza A — `seize_arm_rejected_at_1600`: redeemer `Constr 1 flds`, `flds`
symbolic, EVERYTHING else symbolic. The `PSeizeAct` arm of this validator is a
hard error — verified at the flat's exact revision (wsc-poc 2306678):
`PSeizeAct{} -> ptraceInfoError "global validator does not handle SeizeAct
(use the seize validator)"`. Expected if the technique transfers: ✅ Valid.
The cheapest possible destructured claim: no list, no index, no recursive
postcondition.

MEASURED, v2 (2026-08-02, this file): **✅ Valid — module 4.7 s, whole build
5.11 s wall, 1.16 GB MaxRSS** (`lake build`, warm deps, `ulimit -v` 14 GiB).
Same prep, same class as the v1 tactic-level attempt that spent ≥15 min /
≥4.2 GB without reaching Z3. The regime change is entirely the move from
tactic-level `cases` (motive instantiation per branch over the 1600-step
residual) to statement-level skeleton concretization (one goal, the concrete
tag already inside the `prop` application when blaster starts).

Stanza B (separate module, WSC/Shaped/Probe/GDestructure1600B.lean, so that a
wall in A cannot mask B and vice versa) — the P4-analog with content.

House rules: explicit `timeout:` on every blaster call; `maxHeartbeats 0`;
`warn.sorry false` (blaster closes Valid via `admit`). Run v2 under a hard
`ulimit -v` — v1's lesson is that this workload can take a 61 GB box down.
-/
import WSC.Props.P5_NonMember
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC
namespace GDestructureProbe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext ScriptInfo TxInfo TxInInfo)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- **STANZA A.** Any invocation whose redeemer is a `Constr 1 _` — the
`SeizeAct` arm, dead code in this validator — is rejected by the real bytecode
within 1600 steps, with the fields, the whole `TxInfo`, the purpose and the
script parameter fully symbolic. Statement-level destructure: the concrete
constructor tag is inside the `prop` application; no tactic-side case split. -/
theorem seize_arm_rejected_at_1600 :
    ∀ (ppCS : CurrencySymbol) (tin : TxInfo) (sinfo : ScriptInfo)
      (flds : List Data),
      isUnsuccessful (appliedGlobal1600.prop ppCS ⟨tin, Data.Constr 1 flds, sinfo⟩) := by
  blaster (timeout: 600)

end GDestructureProbe
end WSC
