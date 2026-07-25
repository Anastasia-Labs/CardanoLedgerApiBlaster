/-
PROBE (task U1): is the SHAPE BRIDGE definitional at the `exec` level, and is
`prop = exec` provable at all?  Cheapest validator (base, budget 600).
-/
import WSC.Shaped.BaseShaped

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace WSC.BridgeProbe

open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)

/-- STEP 1: inputs-function level. -/
theorem inputs_bridge
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    baseShapedInputs gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid
      = baseInputs (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
          (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) := rfl

/-- STEP 2: exec level. -/
theorem exec_bridge
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    appliedBaseShaped.exec gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid
      = appliedBase.exec (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
          (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) := rfl

end WSC.BridgeProbe
