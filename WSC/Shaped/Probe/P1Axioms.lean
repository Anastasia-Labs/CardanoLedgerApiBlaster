-- ⚠️ PRE-#112 SHAPES (T1/T2/T6/T7): superseded as RESULTS by the re-cut T1R/T2R/T6R/T7R. The censuses below are still the record that the shaped route never carried `globalModel_faithful` — which task R1 later deleted as FALSE. See WSC/IMPACT-PR112.md and WSC/Model/GlobalModelRefuted.lean.
/-
WSC/Shaped/Probe/P1Axioms.lean — AXIOM AUDIT of every shaped P1 theorem (task V1).

The point of the audit: `WSC/Props/P1_Transfer.lean` proved P1 only on a
hand-transcribed SOURCE MODEL and bridged it to the bytecode with the
whole-validator faithfulness axiom `WSC.Model.globalModel_faithful`, whose own
docstring called that "the ONLY unverified step" and flagged the risk. The shaped
theorems are stated against the REAL prepped bytecode, so that axiom must NOT
appear below — and neither may any `WSC/Honest.lean` axiom.

**POSTSCRIPT (task R1).** The risk this audit was hedging against was real: the
axiom is FALSE (`WSC/Model/GlobalModelRefuted.lean`) and was DELETED. Because
this census had already measured it absent, the deletion cost the shaped route
nothing — which is exactly what an audit like this is for.

EXPECTED (and measured) reading:
* `P1_T1`, `P1_T2`, `P1_T6`, `P1_T7`, `P1_T1_negative_control` →
  `propext, sorryAx, Classical.choice, Quot.sound` only.
  `sorryAx` is blaster's `admit` (SPIKE-FINDINGS: every blaster-proved theorem
  carries it, including the pre-existing reviewed `P3_base_requires_global_or_seize`);
  it is NOT a gap left by this task.
* every `native_decide` witness → `propext, Classical.choice, Lean.ofReduceBool,
  Lean.trustCompiler` (no `sorryAx`): independent of both the solver and `admit`.
* NOWHERE: `WSC.Model.globalModel_faithful`, `WSC.Deployed`, `WSC.OnChain`,
  `WSC.TS3`, or any other WSC axiom.
-/
import WSC.Props.Shaped.P1Shaped

namespace WSC

#print axioms P1_T1
#print axioms P1_T2
#print axioms P1_T6
#print axioms P1_T7
#print axioms P1_T1_negative_control

#print axioms P1ShapedWitness.ctxOk_valid
#print axioms P1ShapedWitness.exec_accepts_at_4400
#print axioms P1ShapedWitness.exec_rejects_escape
#print axioms P1ShapedWitness.K_T1_is_2603
#print axioms P1ShapedWitness.mintPos_form_REFUTED
#print axioms P1ShapedWitness.model_agrees_on_witnesses
#print axioms P1ShapedOutWitness.exec_accepts_T6_at_4400
#print axioms P1ShapedOutWitness.exec_rejects_T6_escape
#print axioms P1ShapedOutWitness.K_T6_is_3150

end WSC
