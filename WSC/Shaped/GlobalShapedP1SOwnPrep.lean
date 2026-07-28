/-
WSC/Shaped/GlobalShapedP1SOwnPrep.lean — the SHAPED `#prep_uplc` over
**SHAPE T8R (script-OWNED mini-ledger input)**, at CEK step budget **4400**
(task N4, PR #112).

The shape and the reason it exists: WSC/Shaped/GlobalShapedR.lean §7. In one
line: it is the only prep in this library that drives PR #112's new INDEXED
owner-witness check (ProgrammableLogicBase.hs:386-393); every other shape, and
every golden, witnesses its mini-ledger owner by SIGNATURE and so takes the
pubkey arm at :370-376 instead.

Budget 4400 matches SHAPE T1R's, so the T1R/T8R pair differs in exactly one
thing — the owner-witness arm — and their K's are directly comparable.
-/
import WSC.Shaped.GlobalShapedR
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT8R programmableLogicGlobal1600 p1SOwnInputs 4400

end WSC
