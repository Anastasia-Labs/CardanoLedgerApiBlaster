/- Z2 exploration probe: concrete SHAPE G1 instance — K bracket + validity. -/
import WSC.Shaped.GlobalShaped
import WSC.Prep.Global
import WSC.Props.P5_NonMember
import WSC.Goldens.Decode
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.Z2Probe.G1W

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext ScriptHash validRewardingContext)
open PlutusCore.ByteString (ByteString)

def ctx : ScriptContext :=
  globalShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "DEST") 150 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

#eval validRewardingContext ctx
#eval (WSC.Goldens.conjuncts .rewarding ctx).filter (fun p => !p.2)

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

#eval isHaltB (appliedGlobal.exec (ByteString.mk "PARAMS") ctx)
#eval isHaltB (appliedGlobal1600.exec (ByteString.mk "PARAMS") ctx)
#eval isHaltB (appliedGlobalShaped1600.exec (ByteString.mk "PARAMS")
    (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "DEST") 150 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50)

end WSC.Z2Probe.G1W
