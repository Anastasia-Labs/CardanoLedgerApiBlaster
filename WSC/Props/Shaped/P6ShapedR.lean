-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/P6ShapedR.lean — **P6 (the `Member` claim is self-penalizing)
re-proved over the NODE-REALIZABLE re-cut SHAPE G6R** (task C1).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P6Shaped.lean` proves P6 over SHAPE G6. That theorem is TRUE
and unchanged, but SHAPE G6's class is EMPTY as a class of ledger transactions:
its withdrawal map has TWO script credentials and its redeemer map has ONE entry,
so the Conway `MissingRedeemers` rule excludes it — the same argument
`WSC/Props/Shaped/ShapeRealizability.lean` runs for SHAPE G1
(`g1_class_is_empty_under_coverage`; SHAPE G6 shares `globalShapedWdrl` and the
one-entry map, so the proof transfers verbatim — see
`WSC.g6_class_is_empty_under_coverage` in
`WSC/Props/Shaped/GlobalRealizability.lean`, where it is stated and proved rather
than asserted).

This module re-states and re-proves P6's obligation over SHAPE G6R
(WSC/Shaped/GlobalShapedR.lean §2), whose class is proved NON-EMPTY in
`WSC/Props/Shaped/GlobalRealizability.lean` (`g6R_realizable`).

WHAT CHANGED FROM SHAPE G6, EXHAUSTIVELY: the withdrawal map is ONE script entry
(the validator's own rewarding credential, the only one this shape's redeemer
lets the bytecode dereference) instead of two, and the redeemer map is TWO
entries `[(Minting cs, I rMint), (Rewarding w0, red)]` instead of one. The
parameters `w1`, `a1` are gone; `rMint` is added. The input, the params reference
input, BOTH outputs (`memberShapedOutputs` — literally the same object, so the
postcondition is about the same list), the mint, the redeemer content and the
budget (3300) are untouched, and so is the "WHY TWO OUTPUTS" anti-tautology
argument: `ob0`, `ob1`, `plc` remain three distinct free variables and
`isBalanced` still only forces `qq0 + qq1 = q`.

SCOPE. Both bounds of `WSC/Props/Shaped/P6Shaped.lean` (budget 3300 via
`LR_BUDGET_global`; SHAPE G6's FIXED/SYMBOLIC split; single-asset dispatch path
only; `paramsRefIdx = 0` concrete) apply here word for word.

MEASURED (this task): `✅ Valid`; witness K = 2837 (unchanged from SHAPE G6),
budget 3300, headroom 463.
-/
import WSC.Shaped.GlobalMemberShapedRPrep
import WSC.Props.Shaped.P6Shaped
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): expected `sorry`s.
set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxOut TxInInfo valueOf validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## §1 The bytecode obligation — RE-PROVED over the realizable shape

`outAtBaseQty` / `inAtBaseQty` are the ground-truth quantities defined in
`WSC/Props/Shaped/P6Shaped.lean` (imported here, not redefined), so this is
literally the same inequality as `P6_shaped_member_adds_to_requirement`. -/

/-- AUDIT (published scope, unchanged): SHAPE G6R has NO mini-ledger inputs, for
every leaf assignment — the sole input is the pubkey ada-only
`memberShapedInput`. So the signed inequality specialises to
`outAtBaseQty ≥ mintOf` and the whole content is the MINT side. -/
theorem P6R_shaped_noBaseInputs
    (plc cs tn owner : ByteString) (inAda : Integer) :
    inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda] = 0 := rfl

/-- **P6 over the REALIZABLE SHAPE G6R — PROVED AT UPLC.**

*If the real compiled transfer validator accepts a shape-G6R transaction — in
which the redeemer classifies the minted policy `cs` as `Member` — then the
quantity of `cs.tn` sitting at outputs at the mini-ledger base credential is at
least the quantity spent from the base PLUS the signed minted amount.*

Identical statement to `WSC.P6_shaped_member_adds_to_requirement`, over a shape
whose class is inhabited by node-acceptable transactions
(`WSC.g6R_realizable`). MEASURED: `✅ Valid`. -/
theorem P6R_shaped_member_adds_to_requirement :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    isSuccessful
      (appliedGlobalMemberShapedG6R.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
      outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q) := by blaster

/-- The specialised reading, as in `P6_shaped_member_mint_stays_at_base`. -/
theorem P6R_shaped_member_mint_stays_at_base
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer)
    (hv : validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee))
    (ha : isSuccessful
      (appliedGlobalMemberShapedG6R.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee)) :
    outAtBaseQty (Credential.ScriptCredential plc) cs tn
      (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
      ≥ mintOf cs tn (Shape.mintOne cs tn q) := by
  have h := P6R_shaped_member_adds_to_requirement ppCS cs tn q owner inAda ob0 outAda0 qq0
    ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee hv ha
  rw [P6R_shaped_noBaseInputs, Int.zero_add] at h
  exact h

/-! ## §2 Polarity controls (ADDENDUM E9) — the full four-stanza set, re-run -/

/-- Negative control at the re-cut shape. MEASURED: `✅ Valid`. -/
theorem P6R_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    ¬ (outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q)) →
    isUnsuccessful
      (appliedGlobalMemberShapedG6R.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) := by blaster

/-- Tightness stanza at the re-cut shape. Expected: `Falsified`. -/
def P6R_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    isSuccessful
      (appliedGlobalMemberShapedG6R.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    ¬ (outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q))

#blaster (gen-cex: 0) (solve-result: 1) [P6R_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE G6R AND ITS OWN TERM.** "No accepting
shape-G6R context exists within 3300 CEK steps" must be FALSIFIED. Expected:
`Falsified`. A new obligation: the SHAPE-G6 probe says nothing about this term.
(At SHAPE G6 this probe caught a genuinely vacuous budget of 2500 — see
`P6_shaped_vacuity_probe`.) -/
def P6R_shaped_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) →
    ¬ isSuccessful
      (appliedGlobalMemberShapedG6R.prop ppCS cs tn q owner inAda ob0 outAda0 qq0
        ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee)

#blaster (gen-cex: 0) (solve-result: 1) [P6R_shaped_vacuity_probe]

/-! ## §3 CONCRETE accepting witness OF EXACTLY SHAPE G6R — executable, no SMT

SHAPE G6's witness leaf values with the two re-cut changes and nothing else. -/

namespace P6RShapedWitness

set_option maxRecDepth 4000000

open P6ShapedWitness (ppCS base cs tn isHaltB isHaltB_sound)

def ctx : ScriptContext :=
  memberRShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "PROGLOGIC") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") 0 99
    50

/-- The witness satisfies the theorem's ledger-normalization hypothesis IN FULL. -/
theorem ctx_valid : validRewardingContext ctx = true := by native_decide

/-- The witness satisfies P6's postcondition, numbers visible: 4 + 3 = 7 of the
minted asset at the base credential against a +7 mint and zero base inputs. -/
theorem ctx_post :
    outAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoOutputs = 7
    ∧ mintOf cs tn ctx.scriptContextTxInfo.txInfoMint = 7
    ∧ inAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoInputs = 0 := by native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this
shape-G6R context at budget 3300, through the shaped applied term. -/
theorem exec_accepts_at_3300 :
    isSuccessful
      (appliedGlobalMemberShapedG6R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "PROGLOGIC") 100 4
        (ByteString.mk "PROGLOGIC") 50 3
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "GLOBAL") 0 99
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 2837`, UNCHANGED from SHAPE G6** (`K_is_2837`).
Budget 3300, headroom 463. -/
theorem K_is_2837 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 2837) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 2836) = false := by native_decide

/-! ### § SELF-PENALIZATION, MEASURED — re-run at the realizable cut

The executable form of P6's plain-English sentence, now on transactions that are
also redeemer-covered: ONE ledger-legal escaping transaction, REJECTED under the
`Member` claim. (The `NonMember` half of the contrast needs a covering directory
node at reference input 1, i.e. SHAPE G6N; the re-cut of that sibling is not
needed for any theorem and is not built — the `Member` rejection is the half that
carries P6's content, and the `NonMember` acceptance is already recorded at SHAPE
G6N in `WSC/Props/Shaped/P6Shaped.lean`.) -/

/-- SHAPE G6R with 3 of the 7 minted tokens escaping to a non-base credential. -/
def ctxEscape : ScriptContext :=
  memberRShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "OUTSIDE") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") 0 99
    50

/-- The escaping context IS ledger-valid and genuinely violates P6's
postcondition: only 4 of the 7 minted tokens are at the base. -/
theorem ctxEscape_valid_and_escaping :
    validRewardingContext ctxEscape = true
    ∧ outAtBaseQty base cs tn ctxEscape.scriptContextTxInfo.txInfoOutputs = 4
    ∧ mintOf cs tn ctxEscape.scriptContextTxInfo.txInfoMint = 7 := by native_decide

/-- …and the REAL compiled bytecode REJECTS it under the `Member` claim at budget
3300. So P6 at the REALIZABLE cut still excludes a non-empty, ledger-legal,
redeemer-covered set of transactions. -/
theorem exec_rejects_escape_under_member :
    isHaltB
      (appliedGlobalMemberShapedG6R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "PROGLOGIC") 100 4
        (ByteString.mk "OUTSIDE") 50 3
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "GLOBAL") 0 99
        50) = false := by native_decide

end P6RShapedWitness

end WSC
