/-
WSC/Shaped/Probe/U3Census.lean — TASK U3, the AXIOM CENSUS as one machine-checked
artifact.

Every headline theorem of the campaign in ONE module, so that a single
`lake build WSC.Shaped.Probe.U3Census` reproduces the table in WSC/AUDIT.md §3.
Nothing here is a proof; the module contains only `#print axioms` commands, so it
adds no trust surface and can be deleted without affecting any result.

Reading the output (WSC/AUDIT.md §3 classifies every line):
* `propext` / `Classical.choice` / `Quot.sound`            — Lean standard.
* `Lean.ofReduceBool` / `Lean.trustCompiler`               — `native_decide`.
* `sorryAx`                                                — `blaster`'s `admit`
  (SPIKE-FINDINGS): present on EVERY solver-closed theorem, and the reason the
  `✅ Valid` marker, not the kernel, is what certifies those.
* anything prefixed `WSC.`                                 — a PROJECT axiom.
-/
import WSC.Props.Shaped.P1Shaped
import WSC.Props.Shaped.P2Shaped
import WSC.Props.Shaped.P4Shaped
import WSC.Props.Shaped.P4ShapedIdx
import WSC.Props.Shaped.P4LocalShaped
import WSC.Props.Shaped.P4DelegateShaped
import WSC.Props.Shaped.P5Shaped
import WSC.Props.Shaped.P6Shaped
import WSC.Props.Shaped.P6Bridge
import WSC.Props.P3_Base
import WSC.Props.P1_Transfer
import WSC.Props.P2_Seize
import WSC.Props.P6_Member
import WSC.Props.P5_NonMember
import WSC.Composition
import WSC.ShapeBridge

/-! ## §A — the top claim -/
#print axioms WSC.Composition.top_claim
#print axioms WSC.Composition.no_programmable_tokens_outside_mini_ledger
#print axioms WSC.Composition.preservation

/-! ## §B — P1 (containment), SHAPES T1/T2/T6/T7, budget 4400 -/
#print axioms WSC.P1_T1
#print axioms WSC.P1_T2
#print axioms WSC.P1_T6
#print axioms WSC.P1_T7
#print axioms WSC.P1_T1_negative_control

/-! ## §C — P2 (seize), SHAPE S1, budget 3800 -/
#print axioms WSC.P2a_shaped_structure
#print axioms WSC.P2b_shaped_containment
#print axioms WSC.P2_shaped
#print axioms WSC.P2a_shaped_negative_control
#print axioms WSC.P2b_shaped_negative_control

/-! ## §D — P3 (base/spending), UNSHAPED, budget 600 -/
#print axioms WSC.P3_base_requires_global_or_seize
#print axioms WSC.P3_base_negative_control

/-! ## §E — P4 (issuance), the four custody arms -/
#print axioms WSC.P4a_shaped_mint_runs_minting_logic
#print axioms WSC.P4_burn_only_shaped
#print axioms WSC.P4_burnonly_arm_shaped
#print axioms WSC.P4a_shapedIdx_mint_runs_minting_logic
#print axioms WSC.P4_burn_only_shapedIdx
#print axioms WSC.P4_local_noEscape_shaped
#print axioms WSC.P4_local_noEscape_shapedIdx
#print axioms WSC.P4_local_arm_shaped
#print axioms WSC.P4_disjunction_at_L1
#print axioms WSC.P4_delegateTransfer_arm_shaped
#print axioms WSC.P4_disjunction_at_DT1
#print axioms WSC.P4_delegateSeize_arm_shaped
#print axioms WSC.P4_disjunction_at_DS1

/-! ## §F — P5 (escape-critical NonMember), SHAPE G1, budget 1600 -/
#print axioms WSC.P5_shaped_indexed
#print axioms WSC.P5_shaped_exists
#print axioms WSC.P5_shaped_groundtruth

/-! ## §G — P6 (Member self-penalization), SHAPE G6, budget 3300 -/
#print axioms WSC.P6_shaped_noBaseInputs
#print axioms WSC.P6_shaped_member_adds_to_requirement
#print axioms WSC.P6_shaped_member_mint_stays_at_base

/-! ## §H — the SOURCE-MODEL route: the faithfulness axioms' consumers -/
#print axioms WSC.Model.P1_bytecode_of_P1_model
#print axioms WSC.Model.P6_bytecode_of_P6_model
#print axioms WSC.P2.P2a_bytecode
#print axioms WSC.P2.P2b_model_implies_bytecode
#print axioms WSC.P2.P2a_seizeModel_preserves_structure

/-! ## §I — the SHAPE BRIDGE (task U1) -/
#print axioms WSC.ShapeBridge.exec_M1
#print axioms WSC.ShapeBridge.exec_T1
#print axioms WSC.ShapeBridge.bridge_M1
#print axioms WSC.ShapeBridge.bridge_T1

/-! ## §J — composition-layer derivations (task U2) -/
#print axioms WSC.Composition.mintingNonVacuous
#print axioms WSC.Composition.LR_BALANCE_SLOT_of_valueAlgebra
#print axioms WSC.Composition.leafP1_of_shapedGlobalContainment
#print axioms WSC.Composition.p4_disjuncts_of_custody
#print axioms WSC.Composition.coveringIn_of_coveringRaw
#print axioms WSC.Composition.coveringRaw_false_of_registered
#print axioms WSC.Composition.contain_iff_modelSums
#print axioms WSC.covering_node_excludes_registration
#print axioms WSC.covering_excludes_registeredIn
#print axioms WSC.Composition.covering_excludes_ledger_registration

/-! ## §K — concrete CEK witnesses (must NOT carry `sorryAx`) -/
#print axioms WSC.P1ShapedWitness.exec_accepts_at_4400
#print axioms WSC.P1ShapedWitness.K_T1_is_2603
#print axioms WSC.P1ShapedWitness.K_T2_is_3572
#print axioms WSC.P1ShapedWitness.exec_rejects_escape
#print axioms WSC.P1ShapedWitness.mintPos_form_REFUTED
#print axioms WSC.P1ShapedWitness.exec_accepts_unshaped
#print axioms WSC.P1ShapedOutWitness.K_T6_is_3150
#print axioms WSC.P2ShapedWitness.K_is_3004_and_3328
#print axioms WSC.P2ShapedWitness.exec_rejects_escaping_seize
#print axioms WSC.P4ShapedWitness.exec_accepts_at_900
#print axioms WSC.P4LocalShapedWitness.K_is_1681
#print axioms WSC.P6ShapedWitness.K_is_2837
#print axioms WSC.P5ShapedWitness.K_is_1541
#print axioms WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped
