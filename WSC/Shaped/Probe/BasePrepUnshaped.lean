/- Z2 control: UNSHAPED base prep at 600, timed under `lake build`. -/
import WSC.Prep.Base
import Blaster
set_option maxHeartbeats 0
namespace WSC.Z2Probe
#prep_uplc appliedBaseUnshapedCtl programmableLogicBase baseInputs 600
end WSC.Z2Probe
