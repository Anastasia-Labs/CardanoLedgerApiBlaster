/-
WSC/Props/Shaped/P4ShapedR.lean — **P4a and P4's `BurnOnly` arm, re-proved over
the NODE-REALIZABLE SHAPE M1R** (task C2).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS FOR
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P4Shaped.lean` proves the same two obligations over SHAPE M1,
and `WSC/Props/Shaped/ShapeRealizability.lean`'s
`m1_class_is_empty_under_coverage` proves SHAPE M1 is an EMPTY class of ledger
transactions (two SCRIPT withdrawals, one redeemer entry — Conway
`MissingRedeemers`). The theorems there are true and uncomposable. The theorems
here are the same statements over SHAPE M1R, whose class is **REALIZABLE**:
`M1RWitness.ctx_realizable` exhibits a member satisfying `validScriptContext`
AND the `MissingRedeemers` row CLAB is missing, and
`WSC.mintR_{wdrl,spend,mint}_covered` prove the coverage holds at EVERY leaf
assignment, not just at the witness.

Nothing else moved: same flat (`WSC/flats/programmableTokenMinting.flat`, byte
identity with the production build at wsc-poc `f918ec6` on main verified in
AUDIT §6; exported at `7ae0024`, identical tree),
same imported program object `programmableTokenMinting900`, same CEK step budget
900, same postconditions, same ground-truth vocabulary.

════════════════════════════════════════════════════════════════════════════
SCOPE — THREE BOUNDS NOW, ALL BINDING
════════════════════════════════════════════════════════════════════════════
**Bound 1 — the CEK step budget 900** (ADDENDUM E1), bridged to node acceptance
by `LR_BUDGET_minting`. Unchanged.

**Bound 2 — the SHAPE M1R.** Published in full in
`WSC/Shaped/MintingShapedR.lean`'s header. Relative to SHAPE M1 the withdrawal
map SHRANK from 2 script entries to 1 and the redeemer map GREW from 1 entry to 2.

**Bound 3 — the arm.** The redeemer tag is 3 (`BurnOnly`), so the class is the
`BurnOnly` arm. At budget 900 that costs nothing: the other three arms' cheapest
accepting goldens are 1,257 and 1,681 CEK steps (K-MEASUREMENTS §3).

**WHAT IS STILL NOT CLAIMED.** Realizable ≠ "a node would accept it". CLAB does
not model fees against a real protocol-parameter set, script-hash agreement
between a withdrawal credential and the script actually supplied, `ExtraRedeemers`
(SHAPE M1R hits the coverage count exactly, so it carries no extra), or the UTxO
set the input is drawn from. What changed is that the ONE defect audit F2
identified — the class being provably empty — is gone.

════════════════════════════════════════════════════════════════════════════
IS THE POSTCONDITION STILL EARNED? (the question a shrink must answer)
════════════════════════════════════════════════════════════════════════════
P4a's conclusion is `credentialInWithdrawals (ScriptCredential mlh) (mintRWdrl w0 a0)`,
which at SHAPE M1R is `w0 == mlh`. Both `w0` (the shape's withdrawal credential)
and `mlh` (the script's second APPLIED PARAMETER) are universally quantified and
independent, and `validMintingContext` on a ONE-entry withdrawal map imposes
nothing at all — `validWithdrawals`' only content is strict sortedness, which is
vacuous on a singleton. So the equality is derived from the bytecode's C1 check
(Issuance.hs:150-151), exactly as at SHAPE M1. The negative control
(`P4a_R_negative_control`) is the contrapositive and is `Valid` too, which is the
machine-checked form of "not hypothesis-implied".

The `BurnOnly` scan's conclusion `mintPos ownCS (mintRMint ownCS tn q) = false`
is likewise earned: SHAPE M1R keeps SHAPE M1's output carrying the policy's own
token, so `q = qOut - qIn` may be POSITIVE and still ledger-legal
(`M1RWitness.ctxPos_valid_and_positive`), and the bytecode is what rejects it
(`M1RWitness.exec_rejects_positive_mint`).
-/
import WSC.Shaped.MintingShapedR
import WSC.Prep.Minting
import WSC.Prep.Minting800
import WSC.Spec
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry` warnings
-- on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext validScriptContext ownCurrencySymbol
                          credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## The two proved obligations, over the REALIZABLE shape -/

/-- **P4a over SHAPE M1R — PROVED AT UPLC, over a REALIZABLE class.** *Any
accepted `BurnOnly` mint of shape M1R runs the token's issuance minting-logic
script: its script credential appears in the transaction's withdrawal map.*

Common conjunct C1 of all four custody arms (Issuance.hs:150-151, listed at :195,
:216, :242, :253). This is `WSC.P4a_shaped_mint_runs_minting_logic` restated over
SHAPE M1R. -/
theorem P4a_R_mint_runs_minting_logic :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid) →
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (mintRWdrl w0 a0) := by blaster

/-- **The `BurnOnly` no-positive-mint scan over SHAPE M1R — PROVED AT UPLC.**
*An accepted `BurnOnly` mint of shape M1R is a genuine pure burn: no token of the
policy's own currency symbol has a strictly positive quantity in `txInfoMint`.*
Second conjunct of arm 4 (Issuance.hs:251-254). -/
theorem P4_burn_only_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid) →
      mintPos ownCS (mintRMint ownCS tn q) = false := by blaster

/-- **P4's arm-4 predicate over SHAPE M1R — PROVED AT UPLC.** The conjunction of
the two theorems above IS `WSC/Spec.lean`'s `BurnOnlyOk`, i.e. the fourth disjunct
of P4, now over a realizable class. -/
theorem P4_burnonly_arm_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid) →
      BurnOnlyOk mlh ownCS
        (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid)
        = true := by blaster

/-! ## Polarity controls (ADDENDUM E9) — the FULL control set at the NEW shape -/

/-- Negative control (≡ the contrapositive of P4a over SHAPE M1R): a shape-M1R
context whose withdrawal map does NOT contain the minting-logic credential is
rejected by the bytecode. -/
theorem P4a_R_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintRWdrl w0 a0) →
    isUnsuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid)
      := by blaster

/-- Tightness stanza at SHAPE M1R: the NEGATION of P4a's postcondition under an
accepting run must be FALSIFIABLE. -/
def P4a_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    isSuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintRWdrl w0 a0)

#blaster (gen-cex: 0) (solve-result: 1) [P4a_R_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND THE NEW SHAPE.** This is the one
stanza a re-cut cannot inherit: shrinking the withdrawal map to a single entry
could easily have made the arm accept-UNSAT (a pubkey entry at index 0 certainly
would have — see `WSC/Shaped/MintingShapedR.lean`'s header), and no other control
detects that. "No accepting shape-M1R context exists within 900 CEK steps" must be
FALSIFIED. -/
def P4_R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid) →
    ¬ isSuccessful
      (appliedMintRShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut
        w0 a0 mlRed fee txid oidx lo hi tid)

#blaster (gen-cex: 0) (solve-result: 1) [P4_R_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE M1R — and its REALIZABILITY

The acceptance criterion of task C2: a concrete context of the re-cut shape proved
to satisfy `validScriptContext` AND the redeemer-coverage condition, plus the
executable non-vacuity that the SMT verdicts cannot supply. -/

namespace M1RWitness

set_option maxRecDepth 100000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"
def tn    : TokenName      := ByteString.mk "TOK"
def owner : ByteString     := ByteString.mk "OWNER"
def dest  : ByteString     := ByteString.mk "DEST"
def w0    : ScriptHash     := ByteString.mk "MINTLOGIC"
def mlRed : ByteString     := ByteString.mk "MLRED"

/-- The witness context: SHAPE M1R burning 3 of `OWNCS.TOK` — input holds 5,
output holds 2, 100 lovelace in, 60 out, 40 fee (balanced on both axes). The
single withdrawal is `(ScriptCredential "MINTLOGIC", 0)` and the redeemer map is
`[(Minting "OWNCS", BurnOnly 0), (Rewarding (ScriptCredential "MINTLOGIC"),
B "MLRED")]` — coverage exact: 0 script inputs + 1 mint policy + 1 script
withdrawal = 2 redeemer entries. -/
def ctx : ScriptContext :=
  mintRCtx ownCS tn (-3) owner 100 5 dest 60 2 w0 0 mlRed 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis. -/
theorem ctx_valid : validMintingContext ctx = true := by native_decide

/-- **AND IT SATISFIES THE `MissingRedeemers` ROW CLAB IS MISSING.** This is the
conjunct no witness in the pre-C2 library can satisfy: it is `false` for
`WSC.P4ShapedWitness.ctx` and for every other shaped witness. -/
theorem ctx_covered : Realizability.redeemerCovered ctx = true := by native_decide

/-- **REALIZABILITY OF SHAPE M1R — the acceptance criterion.** A concrete member
of the class satisfying CLAB's strongest ledger predicate AND redeemer coverage,
with the two ∀-form coverage facts supplied by the shape-level theorems (so they
hold at every other member too, not only here). -/
theorem ctx_realizable : Realizability.Realizable ctx :=
  ⟨by native_decide, ctx_covered,
   mintR_wdrl_covered ownCS tn (-3) owner 100 5 dest 60 2 w0 0 mlRed 40
     (ByteString.mk "") 0 0 1 (ByteString.mk ""),
   mintR_spend_covered ownCS tn (-3) owner 100 5 dest 60 2 w0 0 mlRed 40
     (ByteString.mk "") 0 0 1 (ByteString.mk ""),
   mintR_mint_covered ownCS tn (-3) owner 100 5 dest 60 2 w0 0 mlRed 40
     (ByteString.mk "") 0 0 1 (ByteString.mk "")⟩

/-- The witness names `ownCS` as the minting policy. -/
theorem ctx_ownCS : ownCurrencySymbol ctx = some ownCS := by native_decide

/-- The witness satisfies P4a's postcondition and the `BurnOnly` arm's. -/
theorem ctx_post : credentialInWithdrawals (Credential.ScriptCredential mlh) (mintRWdrl w0 0) = true
    ∧ BurnOnlyOk mlh ownCS ctx = true := by native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-M1R
context at budget 900, through the shaped applied term the theorems above quantify
over. -/
theorem exec_accepts_at_900 :
    isSuccessful
      (appliedMintRShaped900.exec ppCS mlh ownCS tn (-3) owner 100 5 dest 60 2 w0 0 mlRed 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT WITNESS K.** Measured to the step against the unshaped executable term
(same flat, same parameters, the shaped context passed as an ordinary
`ScriptContext`). Recorded so the re-cut's cost can be compared with SHAPE M1's
`K = 784` and with the `mint-burnonly` golden's measured `K = 784`. -/
theorem K_is_784 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 784) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 783) = false := by native_decide

/-! ### EXCLUDED-CASE WITNESS — the positive-mint case is real, and rejected -/

/-- SHAPE M1R with `q = +3`: input holds 2, output holds 5. -/
def ctxPos : ScriptContext :=
  mintRCtx ownCS tn 3 owner 100 2 dest 60 5 w0 0 mlRed 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

/-- The positive-mint shape-M1R context IS ledger-valid, IS redeemer-covered, and
genuinely has a positive mint of the policy's own symbol. -/
theorem ctxPos_valid_and_positive :
    validMintingContext ctxPos = true ∧
    Realizability.redeemerCovered ctxPos = true ∧
    mintPos ownCS ctxPos.scriptContextTxInfo.txInfoMint = true := by
  native_decide

/-- …and the REAL compiled bytecode REJECTS it at budget 900. So `P4_burn_only_R`
excludes a non-empty, ledger-legal, REDEEMER-COVERED set of transactions. -/
theorem exec_rejects_positive_mint :
    isHaltB
      (appliedMintRShaped900.exec ppCS mlh ownCS tn 3 owner 100 2 dest 60 5 w0 0 mlRed 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) = false := by native_decide

end M1RWitness

end WSC
