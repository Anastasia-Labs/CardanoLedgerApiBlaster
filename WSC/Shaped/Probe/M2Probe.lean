/- Z2 loosening rung: P4a at SHAPE M2 (symbolic redeemer index). Z3 capped. -/
import WSC.Shaped.MintingShapedIdx
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
open WSC (mintShapedCtxIdx mintShapedWdrl mintShapedMint mintPos)

def P4a_M2 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
    isSuccessful
      (appliedMintShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
      credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 0) [P4a_M2]

def burn_M2 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
    isSuccessful
      (appliedMintShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
      mintPos ownCS (mintShapedMint ownCS tn q) = false

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 0) [burn_M2]

def vac_M2 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
    ¬ isSuccessful
      (appliedMintShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_M2]

end WSC.Z2Probe
