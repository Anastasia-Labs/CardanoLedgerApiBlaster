-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedP1MintPrep.lean — the SHAPED `#prep_uplc` over **SHAPE
T2** (SHAPE T1 plus a nonzero symbolic mint of unconstrained sign, `Member`
proof) at CEK step budget **4400** (task V1).  See
WSC/Shaped/GlobalShapedP1Prep.lean for the budget justification.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT2 programmableLogicGlobal1600 p1ShapedMintInputs 4400

end WSC
