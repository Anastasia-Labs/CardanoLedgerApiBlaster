-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedP1ROutMintPrep.lean — the SHAPED `#prep_uplc` of the
production transfer validator over the NODE-REALIZABLE re-cut **SHAPE T7R (P1
output aggregation + nonzero symbolic mint)** at CEK step budget **4400**
(task C1).

The shape and the reason it exists: WSC/Shaped/GlobalShapedR.lean's header.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT7R programmableLogicGlobal1600 p1ROutMintInputs 4400

end WSC
