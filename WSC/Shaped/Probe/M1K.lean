/- Z2 exploration probe: exact CEK step count K of the concrete SHAPE M1 instance. -/
import WSC.Props.Shaped.P4Shaped
import Blaster

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.Z2Probe.M1K

open PlutusCore.ByteString (ByteString)

def isHalt : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

partial def findK (lo hi : Nat) : Nat :=
  if lo >= hi then hi
  else
    let mid := (lo + hi) / 2
    if isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                 (WSC.mintingPolicyInputs900 WSC.P4ShapedWitness.ppCS WSC.P4ShapedWitness.mlh
                   WSC.P4ShapedWitness.ctx) mid)
    then findK lo mid else findK (mid + 1) hi

#eval findK 1 1200

end WSC.Z2Probe.M1K
