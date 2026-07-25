/-
WSC/Props/Shaped/P4ShapedRIdx.lean — **P4a and the `BurnOnly` scan over SHAPE M2R**
(task C2): the re-cut of `WSC/Props/Shaped/P4ShapedIdx.lean`, i.e. the LOOSENING
rung with the redeemer's withdrawal index symbolic, over a REALIZABLE class.

SHAPE M2R is SHAPE M1R with `pboMintingLogicWdrlIdx` a free `Integer`
(`WSC/Shaped/MintingShapedRIdx.lean`). The two theorems below therefore SUPERSEDE
`P4a_R_mint_runs_minting_logic` and `P4_burn_only_R` in strength — the shape class
is strictly larger — and the coverage facts are unchanged
(`WSC.mintRIdx_{wdrl,spend,mint}_covered`), because the index lives in the
redeemer PAYLOAD and not in the map's keys.

Budget 900, same flat. Read `WSC/Props/Shaped/P4ShapedR.lean`'s SCOPE block: every
bound there binds here too.
-/
import WSC.Shaped.MintingShapedRIdx
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

/-- **P4a over SHAPE M2R — PROVED AT UPLC, index SYMBOLIC, class REALIZABLE.**
Whatever index the `BurnOnly` redeemer names — including every out-of-range value
and every negative one, which `pcheckedDrop` rejects explicitly
(Issuance.hs:126-130) — an accepted mint has the minting-logic script's credential
in the withdrawal map. -/
theorem P4a_RIdx_mint_runs_minting_logic :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) →
    isSuccessful
      (appliedMintRShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid wIdx) →
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (mintRWdrl w0 a0) := by blaster

/-- **The `BurnOnly` no-positive-mint scan over SHAPE M2R — PROVED AT UPLC.** -/
theorem P4_burn_only_RIdx :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) →
    isSuccessful
      (appliedMintRShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid wIdx) →
      mintPos ownCS (mintRMint ownCS tn q) = false := by blaster

/-- Negative control at SHAPE M2R. -/
theorem P4a_RIdx_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintRWdrl w0 a0) →
    isUnsuccessful
      (appliedMintRShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid wIdx) := by blaster

/-- Tightness stanza at SHAPE M2R. Expected: `Falsified`. -/
def P4a_RIdx_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) →
    isSuccessful
      (appliedMintRShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid wIdx) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintRWdrl w0 a0)

#blaster (gen-cex: 0) (solve-result: 1) [P4a_RIdx_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND SHAPE M2R.** Freeing the index
changes the class, so L1's/M1R's probes do not cover it. Expected: `Falsified`. -/
def P4_RIdx_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    validMintingContext
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) →
    ¬ isSuccessful
      (appliedMintRShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid wIdx)

#blaster (gen-cex: 0) (solve-result: 1) [P4_RIdx_vacuity_probe]

/-! ### REALIZABILITY OF SHAPE M2R -/

namespace M2RWitness

set_option maxRecDepth 100000

/-- The script's two applied parameters, as at SHAPE M1R. -/
def ppCS : CurrencySymbol := ByteString.mk "PARAMS"
def mlh  : ScriptHash     := ByteString.mk "MINTLOGIC"

/-- SHAPE M2R at `wIdx = 0` and M1R's witness leaves. -/
def ctx : ScriptContext :=
  mintRCtxIdx (ByteString.mk "OWNCS") (ByteString.mk "TOK") (-3)
    (ByteString.mk "OWNER") 100 5 (ByteString.mk "DEST") 60 2
    (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED") 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "") 0

theorem ctx_covered : Realizability.redeemerCovered ctx = true := by native_decide

theorem ctx_realizable : Realizability.Realizable ctx := by
  refine ⟨by native_decide, ctx_covered, ?_, ?_, ?_⟩
  · apply mintRIdx_wdrl_covered
  · apply mintRIdx_spend_covered
  · apply mintRIdx_mint_covered

/-! ### CONCRETE ACCEPTING CEK WITNESS AT SHAPE M2R (audit finding **F17**)

Until this stanza landed, SHAPE M2R was the ONE realizable family in the library
meeting only 3 of the 4 bars: it had the theorem, the vacuity probe and the
realizability result, but **no concrete run of the real bytecode**. The sealing
audit measured the answer (AUDIT §7.5) and left the paste to this file's owner;
this is that paste, with `K` pinned TWO-SIDED as every other witness pins it. -/

/-- House `Halt` recogniser (M1R's, restated locally so this namespace stays
self-contained — `WSC/Props/Shaped/P4ShapedR.lean` is deliberately not imported). -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- **NON-VACUITY, EXECUTABLE — the F17 witness.** The real compiled
`programmableTokenMinting` bytecode ACCEPTS this shape-M2R context at budget 900,
through the SHAPED applied term the three theorems above quantify over (the same
`appliedMintRShapedIdx900`, with the withdrawal index carried as an ordinary
argument). This is what the SMT verdicts cannot supply: the `Valid` markers say
"every accepting run has the property", not "an accepting run exists". -/
theorem exec_accepts_at_900 :
    isSuccessful
      (appliedMintRShapedIdx900.exec ppCS mlh
        (ByteString.mk "OWNCS") (ByteString.mk "TOK") (-3)
        (ByteString.mk "OWNER") 100 5 (ByteString.mk "DEST") 60 2
        (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED") 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "") 0) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT WITNESS K = 784, PINNED TWO-SIDED** — halts at 784, budget-errors at
783. **Byte-identical to `M1RWitness.K_is_784`** and to the `mint-burnonly`
golden's measured `K = 784`, which is the predicted result: freeing
`pboMintingLogicWdrlIdx` moves nothing in the CEK trace because the index lives in
the redeemer PAYLOAD, and at `wIdx = 0` `pcheckedDrop` takes the same branch it
takes when the index is the literal 0. So the M2 loosening rung costs ZERO CEK
steps at its own witness. -/
theorem K_is_784 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 784) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 783) = false := by native_decide

end M2RWitness

end WSC
