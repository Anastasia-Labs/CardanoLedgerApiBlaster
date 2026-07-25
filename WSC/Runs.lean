/-
WSC/Runs.lean — **THE LEDGER SIDE, OPTIMIZER-FREE** (task A1).

WHAT THIS MODULE IS.  Four definitions, and nothing else.  Each is *the imported
production validator running on a `ScriptContext` under a `K`-step CEK meter*:

    XRun K params ctx  :=  cekExecuteProgram <imported flat>.script
                             (<audited WSC/Prep inputs fn> params ctx) K

No `#prep_uplc`, no `Blaster.Optimize`, no solver, no elaboration cost, no
`Classical` embedding.  Plain, computable Lean functions.

WHY IT IS A SEPARATE LEAF MODULE (this is the whole point of task A1).  These
four definitions were introduced by task U1 inside `WSC/ShapeBridge.lean`, which
imports the shaped preps — so `WSC/Honest.lean` could not name them without an
import cycle (`ShapeBridge` → `Shaped/*` → `Honest`).  U1's own recommendation
(`WSC/SHAPE-BRIDGE.md` §9, audit finding **F3 HIGH**) was to restate the four
`LR_BUDGET_*` axioms against these terms; that requires `Honest.lean` to see
them.  This module depends only on `WSC/Prep/*`, which depend on nothing in
`WSC/`, so BOTH `Honest.lean` and `ShapeBridge.lean` import it and they name the
SAME four constants.

WHAT THIS BUYS, precisely (each claim is checkable in one command):

1. **The bridge from a shaped theorem to the ledger side becomes a kernel-checked
   `rfl` instead of a solver verdict.**  `WSC/ShapeBridge.lean`'s sixteen
   `exec_<SHAPE>` theorems are `appliedXShaped.exec <leaves> = Runs.XRun K
   <params> (σ <leaves>)`, all `rfl`, all
   `[propext, Classical.choice, Quot.sound]` with **no `sorryAx`**.  Since
   `LR_BUDGET_*` now lands on `Runs.XRun K`, that `rfl` is the connective.
2. **`PropExecFaithful` leaves the base/P3 path entirely.**  `WSC/Props/P3_BaseRun.lean`
   proves the keystone with its accept hypothesis on `Runs.baseRun K_base`
   directly, so `Composition.p3_lifted` never mentions `.prop`.  (It remains a
   dependency of the *shaped* Tier-B path — `WSC/ShapeBridge.lean` §RESIDUAL —
   because the shaped P-theorems are still stated on `.prop`.  See §FOLLOW-ON.)
3. **`GlobalPreppedAt` is no longer needed and is DELETED.**  It existed because
   `LR_BUDGET_global` was parametric over an *elaborator output* (`globalProp`)
   and nothing inside Lean could check that the output really was the prep of the
   right flat at the right budget.  `Runs.globalRun K` is a definition: the flat,
   the inputs function and the budget are all visible in it, so the side
   condition is discharged by reading the definition.
4. **The Tier-A / Tier-B split dissolves for the ledger bridge.**  An unshaped
   `#prep_uplc` exists only at 600 / 900 / 1600 (higher budgets are unaffordable
   — `WSC/goldens/K-MEASUREMENTS.md` §5).  `Runs.XRun K` exists at EVERY budget,
   so the axioms can be — and now are — stated at 2500 / 3300 / 3800 / 4400 too,
   which is where P1 / P2 / P4's custody arms / P6 actually live.

WHAT IT DOES **NOT** BUY.  Nothing here is a coverage argument and nothing here
removes the CEK step bound.  `XRun K` returns `State.Error` on budget exhaustion
exactly as the prepped term does (`PlutusCore/UPLC/CekMachine.lean:233`), so
every consumer is still bounded-transaction model checking (ADDENDUM E1).  The
`LR_BUDGET_*` axioms are still axioms: what they assert is "for a transaction
whose real, unmetered validator run halts within `K` steps, ledger acceptance
coincides with `isSuccessful (XRun K …)`" — the `runSteps` monotonicity
meta-theorem, which the substrate cannot state.  See `WSC/Honest.lean` §LR-BUDGET.

§FOLLOW-ON (identified, not done here).  The shaped P-theorems are still stated
on `appliedXShaped.prop`.  `WSC/Props/P3_BaseRun.lean` demonstrates by
measurement that `blaster` closes a keystone-grade goal stated directly on the
RUN form (3.7 s, `✅ Valid`, vacuity probe `✅ Expected Falsified` at the run term).
Restating the shaped P-theorems the same way would delete `PropExecFaithful` from
the campaign entirely.  That is real proving work (14 theorem groups + 14 vacuity
probes, each needing re-measurement), and it is NOT claimed here.

PROVENANCE: definitions moved verbatim from `WSC/ShapeBridge.lean:141-169`
(task U1); `prog.script` is the same projection `#prep_uplc` uses
(`mkProj PlutusScript 1`, `PlutusCore/UPLC/PreProcess.lean:148`), which is why the
`exec_*` theorems are `rfl`.
-/
import WSC.Prep.Base
import WSC.Prep.Minting900
import WSC.Prep.Global1600
import WSC.Prep.Seize

namespace WSC
namespace Runs

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

/-- `programmableLogicBase` at budget `K` on a ledger-supplied context.

Flat: `WSC/flats/programmableLogicBase.flat` (`WSC/Prep/Base.lean:16`).
Inputs fn: `WSC.baseInputs` (parameter-evidence audit in the same file's
docstring — 2 `PAsData PCredential` params, then the ctx). -/
def baseRun (K : Nat) (globalCred seizeCred : Credential) (ctx : ScriptContext) :=
  cekExecuteProgram programmableLogicBase.script (baseInputs globalCred seizeCred ctx) K

/-- `programmableTokenMinting` at budget `K` on a ledger-supplied context.

Flat: `WSC/flats/programmableTokenMinting.flat` (`WSC/Prep/Minting900.lean:42`).
The script constant is the one every minting-side shaped prep uses, so the
`exec_{M1,M2,L1,L2,DT1,DS1}` bridges are `rfl` against this definition at
budgets 900 and 2500 alike — the `900` in the constant's NAME is the budget its
own `#prep_uplc` bakes, not a property of the imported bytecode. -/
def mintingRun (K : Nat) (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext) :=
  cekExecuteProgram programmableTokenMinting900.script
    (mintingPolicyInputs900 protocolParamsCS mintingLogicHash ctx) K

/-- `programmableLogicGlobal` at budget `K` on a ledger-supplied context.

Flat: `WSC/flats/programmableLogicGlobal.flat` (`WSC/Prep/Global1600.lean:66`).
Same remark about the `1600` in the constant's name as for `mintingRun`: the
`exec_{G1,GIdx,GNIdx,G6,T1,T2,T6,T7}` bridges are `rfl` against this definition
at 1600, 3300 and 4400. -/
def globalRun (K : Nat) (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) :=
  cekExecuteProgram programmableLogicGlobal1600.script (globalInputs1600 protocolParamsCS ctx) K

/-- `programmableSeize` at budget `K` on a ledger-supplied context.

Flat: `WSC/flats/programmableSeize.flat` (`WSC/Prep/Seize.lean:26`).
This is the definition that makes a seize budget bridge possible at all: an
unshaped `#prep_uplc` of this validator is unaffordable above ~1,000 steps and
every affordable budget is MEASURED vacuous (`WSC/goldens/K-MEASUREMENTS.md`
§5.2), whereas `seizeRun 3800` costs nothing to write and has a concrete
accepting witness (`WSC.P2ShapedWitness`, K = 3004 / 3328). -/
def seizeRun (K : Nat) (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) :=
  cekExecuteProgram programmableSeize.script (seizeInputs protocolParamsCS ctx) K

end Runs
end WSC
