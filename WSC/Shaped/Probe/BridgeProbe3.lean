/-
PROBE (task U1) — `isSuccessful X.prop ↔ isSuccessful X.exec` via `blaster` at
budget 600.  MEASURED `Valid` in ~1 s; that cheapness is the evidence that
`blaster` discharges it by re-normalising both sides with the same optimizer
(WSC/SHAPE-BRIDGE.md §5.2 health warning).
-/
import WSC.Shaped.BaseShaped
set_option maxHeartbeats 0
namespace WSC.BridgeProbe3
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- PROBE B: optimizer faithfulness on the SHAPED base prep, via blaster
(blaster re-runs Optimize on the goal, so both sides may normalize together). -/
theorem opt_faithful_shaped
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBaseShaped.exec gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    := by blaster (timeout: 600)

end WSC.BridgeProbe3
