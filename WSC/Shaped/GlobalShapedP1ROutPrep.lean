-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedP1ROutPrep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over the NODE-REALIZABLE re-cut **SHAPE T6R (P1 output aggregation)**
at CEK step budget **4400** (task C1).

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

#prep_uplc appliedGlobalShapedT6R programmableLogicGlobal1600 p1ROutInputs 4400

end WSC
