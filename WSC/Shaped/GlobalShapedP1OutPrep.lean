/-
WSC/Shaped/GlobalShapedP1OutPrep.lean — SHAPED `#prep_uplc` over **SHAPE T6**
(two mini-ledger outputs) and **SHAPE T7** (two mini-ledger outputs + nonzero
symbolic mint) at CEK step budget **4400** (task V1 step 4).
-/
import WSC.Shaped.GlobalShapedP1Out
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT6 programmableLogicGlobal1600 p1ShapedOutInputs 4400
#prep_uplc appliedGlobalShapedT7 programmableLogicGlobal1600 p1ShapedOutMintInputs 4400

end WSC
