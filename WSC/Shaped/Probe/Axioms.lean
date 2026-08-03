-- ⚠️ PRE-#112 (PARTIAL): part of this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Read WSC/IMPACT-PR112.md for the split before quoting anything here.
/- Z2: what do the shaped theorems actually rest on? -/
import WSC.Props.Shaped.P4Shaped
import WSC.Props.Shaped.P4ShapedIdx
import WSC.Props.Shaped.P5Shaped
import WSC.Props.P3_BaseRun
-- corrected 2026-08-02: `P3_base_requires_global_or_seize` no longer exists;
-- its live successors are the per-shape run forms in WSC/Props/P3_BaseRun.lean
-- (this module had been failing to build since the rename).
#print axioms WSC.P3_base_requires_global_or_seize_run_B1RG
#print axioms WSC.P3_base_requires_global_or_seize_run_B1RS
#print axioms WSC.P4a_shaped_mint_runs_minting_logic
#print axioms WSC.P4_burn_only_shaped
#print axioms WSC.P4a_shapedIdx_mint_runs_minting_logic
#print axioms WSC.P5_shaped_indexed
#print axioms WSC.P5_shaped_exists
#print axioms WSC.P5_shaped_groundtruth
#print axioms WSC.P5.nthFrom_mem
#print axioms WSC.P5ShapedWitness.exec_accepts_at_1600
-- corrected 2026-08-02: `K_is_1541` was the pre-#112 pin and no longer exists;
-- the live two-sided pin is `K_is_1402` (WSC/Props/Shaped/P5Shaped.lean).
#print axioms WSC.P5ShapedWitness.K_is_1402
#print axioms WSC.P4ShapedWitness.exec_rejects_positive_mint
