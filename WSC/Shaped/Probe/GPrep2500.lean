-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/- Z2 prep-ceiling probe: SHAPED global prep at budget 2500. -/
import WSC.Shaped.GlobalShaped
import Blaster
set_option maxHeartbeats 0
namespace WSC
#prep_uplc appliedGlobalShaped2500 programmableLogicGlobal1600 globalShapedInputs 2500
end WSC
