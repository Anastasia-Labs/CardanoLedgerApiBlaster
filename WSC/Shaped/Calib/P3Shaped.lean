/-
WSC/Shaped/Calib/P3Shaped.lean — CALIBRATION (task Z2, rung 1): P3 over SHAPE B1.

Compare with WSC/Shaped/Calib/P3Unshaped.lean (same flat, same budget 600, same
statement, fully symbolic context). The ONLY difference is the shape.

The conclusion is quoted through `baseShapedWdrl`, which
`WSC.baseShapedCtx_wdrl` proves (`by rfl`) is exactly the shaped context's
`txInfoWdrl` — so this is P3's postcondition, not a weaker surrogate.
-/
import WSC.Shaped.BaseShaped
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Calib

open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)
open WSC (baseShapedCtx baseShapedWdrl)

/-- P3 over SHAPE B1: an accepting run of the real base validator on a
shape-B1 context puts one of the two parameters into the withdrawal map. -/
theorem P3_shaped :
  ∀ (gh sh : ScriptHash) (txid : ByteString) (idx : Integer) (baseHash : ScriptHash)
    (lovelace : Integer) (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    validSpendingContext
      (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
    isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
      credentialInWithdrawals (Credential.ScriptCredential gh) (baseShapedWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (Credential.ScriptCredential sh)
          (baseShapedWdrl w0 w1 a0 a1) := by blaster

/-- Negative control over SHAPE B1. -/
theorem P3_shaped_negative_control :
  ∀ (gh sh : ScriptHash) (txid : ByteString) (idx : Integer) (baseHash : ScriptHash)
    (lovelace : Integer) (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    validSpendingContext
      (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
    ¬(credentialInWithdrawals (Credential.ScriptCredential gh) (baseShapedWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (Credential.ScriptCredential sh)
          (baseShapedWdrl w0 w1 a0 a1)) →
    isUnsuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
      := by blaster

/-- Tightness over SHAPE B1. Expected: Falsified. -/
def P3_shaped_tightness : Prop :=
  ∀ (gh sh : ScriptHash) (txid : ByteString) (idx : Integer) (baseHash : ScriptHash)
    (lovelace : Integer) (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    validSpendingContext
      (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
    isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
    ¬(credentialInWithdrawals (Credential.ScriptCredential gh) (baseShapedWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (Credential.ScriptCredential sh)
          (baseShapedWdrl w0 w1 a0 a1))

#blaster (gen-cex: 0) (solve-result: 1) [P3_shaped_tightness]

/-- MANDATORY vacuity probe AT THE SHAPE: shaping can easily produce an
accept-UNSAT class, which would make the shaped theorem vacuous. Expected:
Falsified (an accepting shape-B1 context exists within 600 steps). -/
def P3_shaped_vacuity : Prop :=
  ∀ (gh sh : ScriptHash) (txid : ByteString) (idx : Integer) (baseHash : ScriptHash)
    (lovelace : Integer) (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    validSpendingContext
      (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) →
    ¬ isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)

#blaster (gen-cex: 0) (solve-result: 1) [P3_shaped_vacuity]

end WSC.Z2Calib
