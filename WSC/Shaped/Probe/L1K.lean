/- Task V3 probe: exact CEK step count K of the concrete SHAPE L1 instance,
plus the ledger-validity / postcondition checks of the witness and its
excluded-case sibling.  Run BEFORE pinning K in
WSC/Props/Shaped/P4LocalShaped.lean. -/
import WSC.Shaped.MintingLocalShaped
import WSC.Spec
import Blaster

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.V3Probe.L1K

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Credential ScriptContext validMintingContext)

def ppCS := ByteString.mk "PARAMS"
def mlh  := ByteString.mk "MINTLOGIC"

def ctx : ScriptContext :=
  WSC.localShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
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
    50

def ctxEscape : ScriptContext :=
  WSC.localShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "EVIL") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
    50

def isHalt : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

#eval validMintingContext ctx
#eval WSC.LocalCustodyOk mlh
  (WSC.localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
    (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")) (ByteString.mk "OWNCS") ctx
#eval validMintingContext ctxEscape
#eval WSC.noEscape (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "OWNCS") ctxEscape.scriptContextTxInfo.txInfoOutputs

#eval isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                (WSC.mintingPolicyInputs900 ppCS mlh ctx) 2500)
#eval isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                (WSC.mintingPolicyInputs900 ppCS mlh ctxEscape) 2500)

partial def findK (lo hi : Nat) : Nat :=
  if lo >= hi then hi
  else
    let mid := (lo + hi) / 2
    if isHalt (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
                 (WSC.mintingPolicyInputs900 ppCS mlh ctx) mid)
    then findK lo mid else findK (mid + 1) hi

#eval findK 1 2500

end WSC.V3Probe.L1K
