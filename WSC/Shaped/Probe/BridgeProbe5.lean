-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
PROBE (task U1) — the corrected, ASYMMETRIC controls for the SHAPE B1 bridge.
MEASURED: bridge `Valid`, both controls `Falsified`.
-/
import WSC.Shaped.BaseShaped
set_option maxHeartbeats 0
namespace WSC.BridgeProbe5
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- Confirmed Valid in BridgeProbe4; re-asserted with the RIGHT expectation. -/
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

/-- CONTROL A — parameter constructor perturbed: the FIRST base parameter is
handed to the unshaped prep as a PUBKEY credential instead of a SCRIPT one
(`Data.Constr 0` vs `Constr 1`), so the right-hand side can no longer be
satisfied through the `globalCred ∈ wdrl` disjunct.  Must be FALSIFIED. -/
def controlPubKeyParam : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.PubKeyCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [controlPubKeyParam]

/-- CONTROL B — the shaped context's SECOND withdrawal credential is collapsed
onto the first on the right-hand side only, so the right side's withdrawal map
offers strictly fewer hashes.  Must be FALSIFIED. -/
def controlCollapsedWdrl : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w0 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [controlCollapsedWdrl]

end WSC.BridgeProbe5
