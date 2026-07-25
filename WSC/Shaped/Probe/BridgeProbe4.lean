/-
PROBE (task U1) — first full prop-level shape bridge, plus the two controls whose
verdicts produced the methodological finding of WSC/SHAPE-BRIDGE.md §7.1.
Superseded as evidence by `WSC/ShapeBridge.lean`; retained for the record.
-/
import WSC.Shaped.BaseShaped
set_option maxHeartbeats 0
namespace WSC.BridgeProbe4
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- PROBE C — the FULL prop-level shape bridge, stated directly.
MEASURED: `Valid`. -/
def fullBridge : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 0) [fullBridge]

/-- NEGATIVE CONTROL 1 — the WRONG polarity must NOT come out Valid.
MEASURED: `Falsified`, as required. -/
def negControlPolarity : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isUnsuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [negControlPolarity]

/-- NEGATIVE CONTROL 2 — **A BADLY-CHOSEN CONTROL, retained as the finding.**
Bridging to a context with the shape's two withdrawal credentials SWAPPED
(`w1`, `w0` instead of `w0`, `w1`) comes out **`Valid`** — and correctly so: both
are universally quantified and the base validator's membership test is symmetric
in them, so `∀ w0 w1, A w0 w1 ↔ A w1 w0` really is a theorem.  This is a SYMMETRY
of the statement, not a false positive.  The lesson (WSC/SHAPE-BRIDGE.md §7.1):
bridge controls must perturb ASYMMETRICALLY — see `BridgeProbe5.lean`.
MEASURED: `Valid`; expectation below set to the measured value so the file
builds. -/
def negControlWrongCtx : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w1 w0 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 0) [negControlWrongCtx]

end WSC.BridgeProbe4
