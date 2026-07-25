/- Z2 exploration probe: P4a + vacuity at SHAPE M1, Z3 capped. Not a deliverable. -/
import WSC.Shaped.MintingShaped
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Probe

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC (mintShapedCtx mintShapedWdrl mintShapedMint mintPos)

def P4a_M1 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
      credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 0) [P4a_M1]

def vac_M1 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
    ¬ isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [vac_M1]

def burn_M1 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
      mintPos ownCS (mintShapedMint ownCS tn q) = false

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 0) [burn_M1]

end WSC.Z2Probe
