-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/- Z2 prep-ceiling probe: SHAPED global prep at budget 4000. -/
import WSC.Shaped.GlobalShaped
import Blaster
set_option maxHeartbeats 0
namespace WSC
#prep_uplc appliedGlobalShaped4000 programmableLogicGlobal1600 globalShapedInputs 4000
end WSC
