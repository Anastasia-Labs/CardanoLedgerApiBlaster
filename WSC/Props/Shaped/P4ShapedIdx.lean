/-
WSC/Props/Shaped/P4ShapedIdx.lean — **P4a and the BurnOnly scan over SHAPE M2**:
the SAME two theorems as WSC/Props/Shaped/P4Shaped.lean, but with the redeemer's
withdrawal-index field SYMBOLIC (task Z2, loosening rung).

WHY THIS FILE EXISTS. The task's shaping doctrine allows fixing the redeemer's
index fields, on the grounds that they are self-validating hints. This module
MEASURES whether that concession was needed for the minting policy, and the answer
is **no**: with `pboMintingLogicWdrlIdx` a free `Integer` — so that the `dropList`
inside `pcheckedDrop` (Issuance.hs:126-130) cannot be reduced at prep time —
`blaster` still returns `✅ Valid` in ≈1 s.

Consequence for the method (recorded in WSC/SHAPING-RESULTS.md): for this
validator the SMT wall is broken by fixing the `Data` SKELETON (list lengths,
constructor tags, `Option`s) alone. Concrete redeemer indices are a convenience,
not a load-bearing part of the technique. The theorems here therefore SUPERSEDE
the M1 ones in strength, and WSC/Props/Shaped/P4Shaped.lean is kept because it
carries the concrete witness, the arm-scope discussion and the full control set.

SCOPE: exactly WSC/Props/Shaped/P4Shaped.lean's, minus the `wIdx = 0`
restriction. Everything else (budget 900, SHAPE M1's fixed dimensions, the
`BurnOnly` tag, defect D1's non-applicability at a 1-entry redeemer map) is
unchanged — read that file's SCOPE block.
-/
import WSC.Shaped.MintingShapedIdx
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- **P4a over SHAPE M2 (symbolic withdrawal index) — PROVED AT UPLC.**
MEASURED: `✅ Valid`. -/
theorem P4a_shapedIdx_mint_runs_minting_logic :
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
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (mintShapedWdrl w0 w1 a0 a1) := by blaster

/-- **The `BurnOnly` no-positive-mint scan over SHAPE M2 — PROVED AT UPLC.**
MEASURED: `✅ Valid`. -/
theorem P4_burn_only_shapedIdx :
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
      mintPos ownCS (mintShapedMint ownCS tn q) = false := by blaster

/-- Negative control over SHAPE M2. MEASURED: `✅ Valid`. -/
theorem P4a_shapedIdx_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1) →
    isUnsuccessful
      (appliedMintShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx)
      := by blaster

/-- MANDATORY vacuity probe at SHAPE M2. Expected and MEASURED: `Falsified`. -/
def P4_shapedIdx_vacuity_probe : Prop :=
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

#blaster (gen-cex: 0) (solve-result: 1) [P4_shapedIdx_vacuity_probe]

/-- Tightness stanza at SHAPE M2. Expected and MEASURED: `Falsified`. -/
def P4a_shapedIdx_tightness : Prop :=
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
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1)

#blaster (gen-cex: 0) (solve-result: 1) [P4a_shapedIdx_tightness]

end WSC
