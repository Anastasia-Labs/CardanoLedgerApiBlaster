-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalMemberShapedRPrep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over the NODE-REALIZABLE re-cut **SHAPE G6R (P6, Member claim)**
at CEK step budget **3300** (task C1).

The shape and the reason it exists: WSC/Shaped/GlobalShapedR.lean's header.
The budget is the one the pre-re-cut shape was stated at, so the before/after
comparison is at equal budget; the witness K is pinned in the corresponding
`Props/Shaped/*` module.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalMemberShapedG6R programmableLogicGlobal1600 memberRShapedInputs 3300

end WSC
