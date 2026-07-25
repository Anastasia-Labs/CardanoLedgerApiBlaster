/- Task V3: `#print axioms` audit of every new shaped theorem and every new
concrete witness.  Kept separate from WSC/Shaped/Probe/Axioms.lean (task Z2) to
avoid cross-agent edit collisions. -/
import WSC.Props.Shaped.P4LocalShaped
import WSC.Props.Shaped.P4DelegateShaped
import WSC.Props.Shaped.P6Shaped

-- P4 Local arm (SHAPE L1)
#print axioms WSC.P4_local_noEscape_shaped
#print axioms WSC.P4a_local_shaped
#print axioms WSC.P4_local_registration_shaped
#print axioms WSC.P4_local_arm_shaped
#print axioms WSC.P4_disjunction_at_L1
#print axioms WSC.P4_local_negative_control
-- P4 delegating arms (SHAPES DT1 / DS1)
#print axioms WSC.P4_delegateTransfer_arm_shaped
#print axioms WSC.P4_delegateTransfer_globalRuns_shaped
#print axioms WSC.P4_disjunction_at_DT1
#print axioms WSC.P4_delegateSeize_arm_shaped
#print axioms WSC.P4_disjunction_at_DS1
-- P6 (SHAPE G6)
#print axioms WSC.P6_shaped_member_adds_to_requirement
#print axioms WSC.P6_shaped_member_mint_stays_at_base
#print axioms WSC.P6_shaped_noBaseInputs
#print axioms WSC.P6_shaped_negative_control
-- concrete witnesses (must NOT carry sorryAx)
#print axioms WSC.P4LocalShapedWitness.exec_accepts_at_2500
#print axioms WSC.P4LocalShapedWitness.K_is_1681
#print axioms WSC.P4LocalShapedWitness.exec_rejects_escaping_output
#print axioms WSC.P4DelegateShapedWitness.ctxDT_K_is_1257
#print axioms WSC.P4DelegateShapedWitness.ctxDS_valid
#print axioms WSC.P6ShapedWitness.K_is_2837
#print axioms WSC.P6ShapedWitness.exec_rejects_escape_under_member
#print axioms WSC.P6ShapedWitness.exec_accepts_same_escape_under_nonmember
