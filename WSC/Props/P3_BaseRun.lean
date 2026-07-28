-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/P3_BaseRun.lean — **P3, THE KEYSTONE, STATED ON THE RUN TERM** (task A1).

WHY THIS MODULE EXISTS.  Task A1 restated `WSC.LR_BUDGET_base` against
`Runs.baseRun K` (`WSC/Runs.lean`), so what that axiom now delivers to a caller is
`isSuccessful (Runs.baseRun K_base g s ctx)`.  The library's only consumer of any
`LR_BUDGET_*` — `WSC.Composition.p3_lifted` — needs to feed that into P3.  The
existing P3 (`WSC/Props/P3_Base.lean`) hypothesises
`isSuccessful (appliedBase.prop g s ctx)`, a DIFFERENT term: `#prep_uplc` emits
`prop` (optimized, `noncomputable`) and `exec` (executable) separately and
`appliedBase.prop = appliedBase.exec` is NOT definitional (kernel error
"Not a definitional equality", `WSC/Shaped/Probe/BridgeProbe2FAILS.lean`).  That
gap is `PropExecFaithful` (`WSC/ShapeBridge.lean` §RESIDUAL, audit **F8**).

Two routes were MEASURED before choosing (both `✅ Valid`, 3.7 s for the module):

* the prop↔run equivalence `propRun_base_600` below, which lets the old P3 be
  reused but leaves `PropExecFaithful`-grade reasoning on the path; and
* **restating P3 itself on the run term** — `P3_base_requires_global_or_seize_run`
  below — which removes `.prop` from the keystone path ENTIRELY.

The second is what `p3_lifted` now uses.  Consequence, checkable with
`#print axioms`: the chain
`LR_SPEND_RUNS_VALIDATOR → LR_BUDGET_base → LR_CTX → P3-on-the-run-term`
mentions no `#prep_uplc` output anywhere, so `PropExecFaithful` is not on it.

WHAT THIS IS **NOT**.  It is not a discharge of `PropExecFaithful` — that residual
is untouched for the SHAPED layer, where every P-theorem is still stated on
`appliedXShaped.prop` and reaches the ledger through
`ShapeBridge.bridge_<S>` (see §FOLLOW-ON).  It is not a coverage argument.  And it
is not unbounded: `Runs.baseRun 600` returns `State.Error` on budget exhaustion
exactly as the prepped term does, so this is bounded-transaction model checking of
the real bytecode, ADDENDUM E1, same as everything else in the campaign.

SCOPE (ADDENDUM E1, binding): the theorem constrains exactly those invocations of
the real compiled `programmableLogicBase` bytecode whose run halts within
`K_base = 600` CEK steps.  NON-VACUOUS at that term: `P3_run_vacuity_probe` below
is `✅ Expected Falsified` **at the run term itself**, not merely at the prep —
which is the check that matters, since a restated theorem needs a restated probe.

PRECONDITION AUDIT: unchanged from `WSC/Props/P3_Base.lean` — the only hypothesis
is CLAB's `validSpendingContext` (ledger normalization).  It constrains the
withdrawal map ONLY to be credential-sorted; it assumes nothing about WHICH
credentials appear there, so the postcondition is not smuggled in.  The redeemer
is wholly unconstrained and `globalCred`/`seizeCred` are universally quantified.

§FOLLOW-ON (identified, NOT done).  The same restatement applied to the shaped
P-theorems (P1 T1/T2/T6/T7, P2 S1, P4 M1/M2/L1/L2/DT1/DS1, P5 G1, P6 G6) would
delete `PropExecFaithful` from the campaign.  Each needs its own `blaster` run AND
its own re-measured vacuity probe at the run term — 14 theorem groups, 14 probes,
real proving work with real risk of a probe coming back `Valid` (i.e. vacuous), as
happened to P6 at 2500.  This module is the existence proof that the technique
works at keystone grade, and nothing more.
-/
import WSC.Runs
import WSC.Honest
import Blaster

namespace WSC

open CardanoLedgerApi.V3 (Credential ScriptContext validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false
set_option maxHeartbeats 0

/-! ## The keystone, on the ledger-side run term -/

/-- **P3 (keystone), RUN FORM.** *You cannot spend a mini-ledger UTxO unless the
global (transfer) or seize validator runs in the same transaction.*

Identical in content to `WSC.P3_base_requires_global_or_seize`, with the accept
hypothesis moved from `appliedBase.prop` (an `Optimize.main` output) to
`Runs.baseRun 600` (the imported flat + `WSC.baseInputs` + `cekExecuteProgram`).
This is the form `WSC.LR_BUDGET_base` delivers after task A1, so
`WSC.Composition.p3_lifted` consumes THIS theorem and no `#prep_uplc` output
appears anywhere on the composition's keystone path.

`blaster` closes it in the same way it closes the `.prop` form — by running
`Optimize.main` on the goal itself — so the two carry the SAME trust status
(solver verdict + `admit`; `sorryAx` in `#print axioms`). The gain is not in the
strength of the verdict, it is that the term in the statement is the term the
ledger side names, so no unproved `prop = exec` step is interposed. -/
theorem P3_base_requires_global_or_seize_run :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    isSuccessful (Runs.baseRun K_base globalCred seizeCred ctx) →
      credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster

/-! ## Polarity controls and the MANDATORY vacuity probe, AT THE RUN TERM

A restated theorem needs a restated probe: a probe at the old prep term would say
nothing about the accept class of the new one. Both stanzas below are stated over
`Runs.baseRun K_base`. -/

/-- Negative control at the run term: a context violating the postcondition
(NEITHER credential in the withdrawal map) is rejected by the bytecode.

NOTE (ADDENDUM E9, binding): this control is satisfied by budget-`Error` as well,
so it cannot detect the bound. The vacuity probe is what rules out vacuity. -/
theorem P3_run_negative_control :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    ¬(credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl) →
    isUnsuccessful (Runs.baseRun K_base globalCred seizeCred ctx) := by
  blaster

/-- **MANDATORY vacuity probe at the RUN term** (SPIKE-FINDINGS / E9): "no
accepting context within budget 600" must be FALSIFIED, i.e. accepting contexts
of the run term exist inside the meter, so the theorem above is not vacuous.
Expected result: Falsified. -/
def P3_run_vacuity_probe : Prop :=
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    ¬ isSuccessful (Runs.baseRun K_base globalCred seizeCred ctx)

#blaster (gen-cex: 0) (solve-result: 1) [P3_run_vacuity_probe]

/-! ## The prop↔run equivalence at this prep — RECORDED, WITH ITS HEALTH WARNING

Not used by anything. Kept because it is the machine-checked form of a dependency
the campaign carried SILENTLY until task U1 named it (`PropExecFaithful`, audit
F8), and because it certifies that the two P3 statements — this module's and
`WSC/Props/P3_Base.lean`'s — are about the same accept class at this prep.

**HEALTH WARNING, and it is the same one `WSC/SHAPE-BRIDGE.md` §5.2 attaches to
every Tier-B bridge: this verdict is NOT independent evidence that
`Optimize.main` is faithful.** `blaster` begins by running `Optimize.main` on the
goal, so presented with `run ↔ prop` it normalises the left side into (a term
equal to) the right and the SMT query it emits is trivial. MEASURED: `✅ Valid` in
well under a second. That cheapness is the tell. What the verdict IS evidence for
is that the optimizer is DETERMINISTIC and IDEMPOTENT. Do not upgrade it. -/
theorem propRun_base_600 (g s : Credential) (ctx : ScriptContext) :
    isSuccessful (Runs.baseRun K_base g s ctx) ↔ isSuccessful (appliedBase.prop g s ctx) := by
  blaster

/-! ## AXIOM AUDIT -/

#print axioms WSC.P3_base_requires_global_or_seize_run
#print axioms WSC.P3_run_negative_control

end WSC
