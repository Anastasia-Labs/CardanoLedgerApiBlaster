/-
PROBE (task U1) — **THIS FILE IS EXPECTED TO FAIL TO BUILD**, in the style of
`T3PrepFAILS.lean` / `T4PrepFAILS.lean`: the failure IS the recorded measurement.

It asks whether `#prep_uplc`'s two outputs are definitionally equal, i.e. whether
`Optimize.main` is defeq-preserving.  They are not.  Kernel verdict:

    error: Not a definitional equality: the left-hand side
    is not definitionally equal to the right-hand side

That is the reason the shape bridge cannot be pushed from the `exec` level to the
`prop` level by `rfl`, and the reason `WSC/ShapeBridge.lean` §RESIDUAL exists.
See WSC/SHAPE-BRIDGE.md §2(b).
-/
import WSC.Shaped.BaseShaped
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace WSC.BridgeProbe2FAILS
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-- PROBE A: is `prop` defeq to `exec` for the UNSHAPED base prep? -/
theorem prop_eq_exec_unshaped :
    @appliedBase.prop = @appliedBase.exec := rfl

end WSC.BridgeProbe2FAILS
