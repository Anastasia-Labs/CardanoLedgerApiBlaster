/- Task V3 probe: concrete accepting instances of SHAPE DT1 / SHAPE DS1, their
ledger validity, their arm postconditions and their exact CEK step counts. -/
import WSC.Shaped.MintingDelegateShaped
import WSC.Spec
import Blaster

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.V3Probe.DTDSK

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (ScriptContext validMintingContext)

def ppCS := ByteString.mk "PARAMS"
def mlh  := ByteString.mk "MINTLOGIC"

/-- SHAPE DT1 witness: withdrawal 1's credential IS the params datum's
`globalLogicCred` (`SGLOBAL`), and the map stays sorted (`MINTLOGIC < SGLOBAL`). -/
def ctxDT : ScriptContext :=
  WSC.dtShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "SGLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "SGLOBAL") 0 0
    50

/-- SHAPE DS1 witness: the `Rewarding` redeemer entry carries `SeizeAct 1 …` and
its credential IS the params datum's `seizeLogicCred` (`SEIZE`); `sIdx = 1`
matches the redeemer's `mrNodeRefIdx`, which is the reference input holding the
`DIRCS.OWNCS` directory NFT. -/
def ctxDS : ScriptContext :=
  WSC.dsShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
    (ByteString.mk "SEIZE") 1
    50

def isHalt : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

def prm := WSC.localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
             (ByteString.mk "SGLOBAL") (ByteString.mk "SEIZE")
def prmDS := WSC.localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
               (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")

#eval validMintingContext ctxDT
#eval WSC.DelegateTransferOk mlh prm (ByteString.mk "OWNCS") ctxDT
#eval validMintingContext ctxDS
#eval WSC.DelegateSeizeOk mlh prmDS (ByteString.mk "OWNCS") ctxDS
#eval isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                (WSC.mintingPolicyInputs900 ppCS mlh ctxDT) 2500)
#eval isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                (WSC.mintingPolicyInputs900 ppCS mlh ctxDS) 2500)

partial def findK (c : ScriptContext) (lo hi : Nat) : Nat :=
  if lo >= hi then hi
  else
    let mid := (lo + hi) / 2
    if isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                 (WSC.mintingPolicyInputs900 ppCS mlh c) mid)
    then findK c lo mid else findK c (mid + 1) hi

#eval findK ctxDT 1 2500
#eval findK ctxDS 1 2500

end WSC.V3Probe.DTDSK
