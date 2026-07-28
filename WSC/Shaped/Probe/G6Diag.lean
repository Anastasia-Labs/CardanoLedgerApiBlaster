-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/- Task V3 diagnostic: is the SHAPE G6 witness budget-starved or genuinely
rejected?  Runs the real CEK at increasing budgets and reports the raw state. -/
import WSC.Shaped.GlobalMemberShaped
import WSC.Spec
import Blaster

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC.V3Probe.G6Diag

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Credential ScriptContext validRewardingContext)

def ppCS := ByteString.mk "PARAMS"

def ctx : ScriptContext :=
  WSC.memberShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "PROGLOGIC") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

/-- Whole expected value in ONE output instead of split across two. -/
def ctxOne : ScriptContext :=
  WSC.memberShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 7
    (ByteString.mk "PROGLOGIC") 50 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

def tag : PlutusCore.UPLC.CekMachine.State → String
  | .Halt _ => "HALT"
  | .Error => "ERROR"
  | _ => "RUNNING(budget exhausted)"

#eval tag (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
             (WSC.globalInputs1600 ppCS ctx) 2500)
#eval tag (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
             (WSC.globalInputs1600 ppCS ctx) 20000)
#eval tag (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
             (WSC.globalInputs1600 ppCS ctxOne) 20000)


def isHalt : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

partial def findK (c : ScriptContext) (lo hi : Nat) : Nat :=
  if lo >= hi then hi
  else
    let mid := (lo + hi) / 2
    if isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
                 (WSC.globalInputs1600 ppCS c) mid)
    then findK c lo mid else findK c (mid + 1) hi

#eval findK ctx 1 20000

end WSC.V3Probe.G6Diag
