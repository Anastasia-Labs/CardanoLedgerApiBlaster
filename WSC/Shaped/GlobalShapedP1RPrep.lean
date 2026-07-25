/-
WSC/Shaped/GlobalShapedP1RPrep.lean — the SHAPED `#prep_uplc` of the production
transfer validator over the NODE-REALIZABLE re-cut **SHAPE T1R (P1 base, pure transfer)**
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

#prep_uplc appliedGlobalShapedT1R programmableLogicGlobal1600 p1RShapedInputs 4400

end WSC
