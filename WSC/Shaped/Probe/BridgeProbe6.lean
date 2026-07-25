/-
PROBE (task U1) — SHAPE M1 (issuance policy, budget 900 = `K_mint`): LEVEL 1,
LEVEL 2 by `rfl`, LEVEL 3 by `blaster` (`Valid`), two asymmetric controls
(`Falsified`).
-/
import WSC.Shaped.MintingShaped
set_option maxHeartbeats 0
namespace WSC.BridgeProbe6
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- STEP 1/2 for SHAPE M1: inputs level and exec level, both by `rfl`. -/
theorem inputs_bridge_M1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    mintShapedInputs ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid
      = mintingPolicyInputs900 ppCS mlh
          (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    := rfl

theorem exec_bridge_M1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    appliedMintShaped900.exec ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid
      = appliedMinting900.exec ppCS mlh
          (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    := rfl

/-- STEP 3 for SHAPE M1 — the prop-level bridge. -/
def fullBridgeM1 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    ↔ isSuccessful
      (appliedMinting900.prop ppCS mlh
        (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 0) [fullBridgeM1]

/-- CONTROL — the redeemer's withdrawal index is perturbed on the right-hand side
by swapping the two withdrawal credentials WITHOUT swapping their amounts is
symmetric for this validator, so instead collapse both entries onto `w0`. -/
def controlM1CollapsedWdrl : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    ↔ isSuccessful
      (appliedMinting900.prop ppCS mlh
        (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w1 w1 a0 a1 fee txid oidx lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [controlM1CollapsedWdrl]

/-- CONTROL — the minted quantity is negated on the right-hand side only.  The
`BurnOnly` arm's scan is a sign test on exactly that leaf, so this must be
FALSIFIED. -/
def controlM1NegatedQ : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    ↔ isSuccessful
      (appliedMinting900.prop ppCS mlh
        (mintShapedCtx ownCS tn (-q) owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [controlM1NegatedQ]

end WSC.BridgeProbe6
