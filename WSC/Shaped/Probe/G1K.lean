-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/- Z2 exploration probe: exact CEK step count K of the concrete SHAPE G1 instance. -/
import WSC.Shaped.Probe.G1Witness
import Blaster

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.Z2Probe.G1K


open PlutusCore.ByteString (ByteString)

def isHalt : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

/-- Smallest `n` in `[lo, hi]` at which the run halts (binary search). -/
partial def findK (lo hi : Nat) : Nat :=
  if lo >= hi then hi
  else
    let mid := (lo + hi) / 2
    if isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
                 (WSC.globalInputs1600 (ByteString.mk "PARAMS") WSC.Z2Probe.G1W.ctx) mid)
    then findK lo mid else findK (mid + 1) hi

#eval findK 600 1600

end WSC.Z2Probe.G1K
