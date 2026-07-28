/-
WSC/Props/P3_BaseRun.lean — **P3, THE KEYSTONE, ON THE LEDGER-SIDE RUN TERM**
(task A1; RE-BASED on wsc-poc `main` @ 2306678, PR #112, by task N3).

WHY THIS MODULE EXISTS.  Task A1 restated `WSC.LR_BUDGET_base` against
`Runs.baseRun K` (`WSC/Runs.lean`), so what that axiom delivers to a caller is
`isSuccessful (Runs.baseRun K_base g s ctx)`.  The library's only consumer of any
`LR_BUDGET_*` — `WSC.Composition.p3_lifted` — needs to feed that into P3.  A P3
stated on `appliedBase.prop` (an `Optimize.main` output) is a DIFFERENT term:
`#prep_uplc` emits `prop` and `exec` separately and `prop = exec` is NOT
definitional (kernel error "Not a definitional equality",
`WSC/Shaped/Probe/BridgeProbe2FAILS.lean`).  That gap is `PropExecFaithful`
(`WSC/ShapeBridge.lean` §RESIDUAL, audit **F8**).  Stating P3 directly on the run
term removes it from the keystone path.

════════════════════════════════════════════════════════════════════════════
WHAT PR #112 CHANGED HERE
════════════════════════════════════════════════════════════════════════════
Two things, and both are visible in the statements below.

**(1) The theorem is SHAPED now.**  Pre-#112 this module proved the run form over
a fully symbolic `ScriptContext`.  That no longer closes: the unshaped run/prop
goals at budget 600 are `⚠️ Undetermined` at a 600 s Z3 cap, and so are two
escalations (a 2400 s cap; a minimal shape freezing only the redeemer skeleton).
The measurement table is in `WSC/Props/P3_Base.lean` §MEASUREMENT and is not
repeated.  So the run-form keystone is stated over SHAPES B1RG / B1RS
(`WSC/Shaped/BaseShapedR.lean`) — the same two shapes
`WSC/Props/Shaped/P3ShapedR.lean` proves the `.prop` form over.

**(2) The import is `WSC.Runs.Base`, not `WSC.Runs`.**  `WSC/Runs.lean` imports
all four preps, two of which are substrate-broken after #112
(`WSC/IMPACT-PR112.md` §6).  Task N3 split `Runs.baseRun` into its own leaf
(`WSC/Runs/Base.lean`) so the base keystone does not depend on the seize and
global bytecode's substrate state.  `WSC.Runs.baseRun` is the SAME constant.
The budget is written as the literal `600`; `WSC.K_base = 600` is a `def` in
`WSC/Honest.lean`, reducible by `rfl`, so `Composition.p3_lifted` sees the same
statement — no edit to `Honest.lean` was needed or made.

WHAT THIS IS **NOT**.  It is not a discharge of `PropExecFaithful` for the rest
of the library — every other shaped P-theorem is still stated on
`appliedXShaped.prop`.  It is not a coverage argument.  And it is not unbounded:
`Runs.baseRun 600` returns `State.Error` on budget exhaustion exactly as the
prepped term does, so this is bounded-transaction model checking of the real
bytecode (ADDENDUM E1), now bounded in the shape dimension as well.

NON-VACUITY: `P3_run_vacuity_probe_B1RG` / `_B1RS` below are ✅ Expected
Falsified **at the run terms themselves**, not merely at the preps — a restated
theorem needs a restated probe.  Concrete accepting witnesses at K = 194,
pinned two-sided, are `WSC.P3RWitness.K_B1RG_two_sided` / `_B1RS_two_sided`
(`WSC/Props/Shaped/P3ShapedR.lean` §3), whose `runG`/`runS` are literally
`cekExecuteProgram programmableLogicBase.script (baseR{G,S}Inputs …)` — the same
term the `exec_B1R*` bridges below equate to `Runs.baseRun 600 …`.

PRECONDITION AUDIT: as in `WSC/Props/Shaped/P3ShapedR.lean`, and STRICTLY
STRONGER than the pre-#112 module on one axis — `validSpendingContext` is not
assumed at all.  The redeemer's index field stays universally quantified, so a
dishonest witness index is inside the class.
-/
import WSC.Runs.Base
import WSC.Shaped.BaseShapedR
import Blaster

namespace WSC

open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false
set_option maxHeartbeats 0

/-! ## §0 THE SHAPE BRIDGE, KERNEL-CHECKED

Level-2 bridges: the shaped prep's EXECUTABLE output is literally
`Runs.baseRun 600` at the shape's own context.  Both are `rfl` — `baseRGInputs`
unfolds to `baseInputs (ScriptCredential gh) (ScriptCredential sh)
(baseRShapedCtx 0 …)`, which is exactly what `Runs.baseRun` applies.  So the
step from the shaped world to the ledger-side term is kernel computation, not a
solver verdict and not an axiom. -/

/-- SHAPE B1RG: the shaped prep's exec output IS `Runs.baseRun 600` at the
shape's context. -/
theorem exec_B1RG (gh sh baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString) :
    appliedBaseB1RG.exec gh sh baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid
      = Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
          (baseRShapedCtx 0 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid) := rfl

/-- SHAPE B1RS: same, at redeemer constructor tag 1. -/
theorem exec_B1RS (gh sh baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString) :
    appliedBaseB1RS.exec gh sh baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid
      = Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
          (baseRShapedCtx 1 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid) := rfl

/-! ## §1 THE KEYSTONE, ON THE RUN TERM, ONE THEOREM PER ARM -/

/-- **P3 (keystone), RUN FORM, SHAPE B1RG.**

Identical in content to `WSC.P3_base_requires_global_or_seize_B1RG`, with the
accept hypothesis moved from `appliedBaseB1RG.prop` (an `Optimize.main` output)
to `Runs.baseRun 600` (the imported flat + `WSC.baseInputs` +
`cekExecuteProgram`).  This is the form `WSC.LR_BUDGET_base` delivers, so
`WSC.Composition.p3_lifted` can consume THIS theorem and no `#prep_uplc` output
appears anywhere on the composition's keystone path.

`blaster` closes it the same way it closes the `.prop` form — by running
`Optimize.main` on the goal itself — so the two carry the SAME trust status
(solver verdict + `admit`; `sorryAx` in `#print axioms`).  The gain is not in the
strength of the verdict, it is that the term in the statement is the term the
ledger side names, so no unproved `prop = exec` step is interposed. -/
theorem P3_base_requires_global_or_seize_run_B1RG :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 0 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid)) →
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1) := by
  blaster (timeout: 900)

/-- **P3 (keystone), RUN FORM, SHAPE B1RS** — the `SpendViaSeize` arm. -/
theorem P3_base_requires_global_or_seize_run_B1RS :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 1 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid)) →
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1) := by
  blaster (timeout: 900)

/-! ## §2 POLARITY CONTROLS AND THE MANDATORY VACUITY PROBES, AT THE RUN TERMS

A restated theorem needs a restated probe: a probe at the prep term would say
nothing about the accept class of the run term.  All four stanzas below are
stated over `Runs.baseRun 600`.

NOTE (ADDENDUM E9, binding): the negative controls are satisfied by
budget-`Error` as well, so they cannot detect the bound.  The vacuity probes are
what rule out vacuity. -/

/-- Negative control at the run term, SHAPE B1RG. -/
theorem P3_run_negative_control_B1RG :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1)) →
    isUnsuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 0 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid)) := by
  blaster (timeout: 900)

/-- Negative control at the run term, SHAPE B1RS. -/
theorem P3_run_negative_control_B1RS :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1)) →
    isUnsuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 1 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid)) := by
  blaster (timeout: 900)

/-- **MANDATORY vacuity probe AT THE RUN TERM, SHAPE B1RG.** "No accepting
context of this shape within budget 600" must be FALSIFIED.
Expected result: Falsified. -/
def P3_run_vacuity_probe_B1RG : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬ isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 0 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid))

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_run_vacuity_probe_B1RG]

/-- **MANDATORY vacuity probe AT THE RUN TERM, SHAPE B1RS.**
Expected result: Falsified. -/
def P3_run_vacuity_probe_B1RS : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬ isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 1 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid))

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_run_vacuity_probe_B1RS]

/-! ## §3 THE prop↔run EQUIVALENCE AT THESE SHAPES — RECORDED, WITH ITS
HEALTH WARNING

Not used by anything.  Kept because it is the machine-checked form of a
dependency the campaign carried SILENTLY until task U1 named it
(`PropExecFaithful`, audit F8), and because it certifies that §1 and
`WSC/Props/Shaped/P3ShapedR.lean` §1 are about the same accept class.

**HEALTH WARNING, the same one `WSC/SHAPE-BRIDGE.md` §5.2 attaches to every
Tier-B bridge: this verdict is NOT independent evidence that `Optimize.main` is
faithful.**  `blaster` begins by running `Optimize.main` on the goal, so
presented with `run ↔ prop` it normalises the left side into (a term equal to)
the right and the SMT query it emits is trivial.  That cheapness is the tell.
What the verdict IS evidence for is that the optimizer is DETERMINISTIC and
IDEMPOTENT.  Do not upgrade it. -/
theorem propRun_B1RG (gh sh baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString) :
    isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 0 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid))
      ↔ isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                        rw0 rw1 lo hi tid) := by
  blaster (timeout: 900)

/-- Same at SHAPE B1RS. -/
theorem propRun_B1RS (gh sh baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString) :
    isSuccessful (Runs.baseRun 600 (.ScriptCredential gh) (.ScriptCredential sh)
      (baseRShapedCtx 1 baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid))
      ↔ isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                        rw0 rw1 lo hi tid) := by
  blaster (timeout: 900)

/-! ## AXIOM AUDIT -/

#print axioms WSC.exec_B1RG
#print axioms WSC.exec_B1RS
#print axioms WSC.P3_base_requires_global_or_seize_run_B1RG
#print axioms WSC.P3_base_requires_global_or_seize_run_B1RS
#print axioms WSC.P3_run_negative_control_B1RG
#print axioms WSC.P3_run_negative_control_B1RS

end WSC
