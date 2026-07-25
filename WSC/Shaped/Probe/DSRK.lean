/- Scratch K-measurement for SHAPE DS1R (task C2). Not imported by WSC.lean. -/
import WSC.Props.Shaped.P4DelegateShapedR

set_option maxRecDepth 1000000

namespace WSC.Probe.DSRK
open WSC WSC.DelegateRWitness

def halts (k : Nat) : Bool :=
  match PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
          (mintingPolicyInputs900 ppCS mlh ctxDS) k with
  | .Halt _ => true
  | _ => false

#eval (List.range 40).map (fun i => (1450 + i, halts (1450 + i))) |>.filter (·.2)  |>.take 3

end WSC.Probe.DSRK
