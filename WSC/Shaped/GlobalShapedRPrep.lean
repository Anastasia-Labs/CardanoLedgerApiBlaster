-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedRPrep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over the NODE-REALIZABLE re-cut **SHAPE G1R (P5, NonMember mint-side claim)**
at CEK step budget **1600** (task C1).

The shape and the reason it exists: WSC/Shaped/GlobalShapedR.lean's header.
The budget is the one the pre-re-cut shape was stated at, so the before/after
comparison is at equal budget; the witness K is pinned in the corresponding
`Props/Shaped/*` module.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedG1R programmableLogicGlobal1600 globalRShapedInputs 1600

end WSC
