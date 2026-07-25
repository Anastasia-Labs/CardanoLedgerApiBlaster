/-
PROBE (task U1) — `#eval` search for an accepting SHAPE B1 leaf assignment, used by
`WSC/ShapeBridge.lean` §CONCRETE.  MEASURED: accepts with `w0 = "GLOBAL"` and with
`w0 = "SEIZE"`, rejects with `w0 = "AAA"`; `validSpendingContext` is FALSE on it
(the B1 instance is a bridge witness, not a ledger-normalized context — SHAPE M1's
witness is the ledger-valid one).
-/
import WSC.Shaped.BaseShaped
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace WSC.B1Accept
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false
-- gh in wdrl at index 0
#eval isHaltB (appliedBaseShaped.exec (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
  (ByteString.mk "") 0 (ByteString.mk "BASE") 100
  (ByteString.mk "GLOBAL") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk ""))
-- sh in wdrl
#eval isHaltB (appliedBaseShaped.exec (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
  (ByteString.mk "") 0 (ByteString.mk "BASE") 100
  (ByteString.mk "SEIZE") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk ""))
-- neither
#eval isHaltB (appliedBaseShaped.exec (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
  (ByteString.mk "") 0 (ByteString.mk "BASE") 100
  (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk ""))
#eval CardanoLedgerApi.V3.validSpendingContext (baseShapedCtx
  (ByteString.mk "") 0 (ByteString.mk "BASE") 100
  (ByteString.mk "GLOBAL") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk ""))
end WSC.B1Accept
