-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Shaped/GlobalShapedP1ROutMintPrep.lean — the SHAPED `#prep_uplc` of the
production transfer validator over the NODE-REALIZABLE re-cut **SHAPE T7R (P1
output aggregation + nonzero symbolic mint)** at CEK step budget **4400**
(task C1).

The shape and the reason it exists: WSC/Shaped/GlobalShapedR.lean's header.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT7R programmableLogicGlobal1600 p1ROutMintInputs 4400

end WSC
