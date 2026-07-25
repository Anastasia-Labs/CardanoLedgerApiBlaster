/-
WSC/Props/Shaped/P4Shaped.lean — **P4a AND the BurnOnly arm of P4, PROVED at
UPLC level against the real compiled issuance bytecode, over SHAPE M1**
(task Z2 rung 2/3).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED, AND WHY IT MATTERS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/P4_Minting.lean` records P4a over a FULLY SYMBOLIC `ScriptContext` at
budget 900 as **Undetermined** — no verdict from Z3 at caps of 300 s, 3,300 s, and
1,748 s uncapped. The same obligation over SHAPE M1 — same flat, same budget 900,
same postcondition — is **Valid in ≈1 s**, together with its negative control,
its tightness stanza and its vacuity probe. Measured ladder in
WSC/SHAPING-RESULTS.md.

That is the whole point of shaping: it attacks the term the SOLVER sees. It does
not weaken the bytecode (byte-identical flat), it does not weaken the budget
(unchanged at 900), and it does not weaken the postcondition. It narrows the
class of transactions quantified over, and that class is published below in full.

════════════════════════════════════════════════════════════════════════════
SCOPE — TWO BOUNDS, BOTH BINDING. Never quote a theorem below without both.
════════════════════════════════════════════════════════════════════════════
**Bound 1 — the CEK step budget (ADDENDUM E1).** `#prep_uplc … 900` bakes a
900-step budget into `appliedMintShaped900.prop`; exhaustion is `Error`, so
`isSuccessful` is false and the implications say nothing past the bound. Bridged
to real node acceptance by `LR_BUDGET_minting` (WSC/Honest.lean).

**Bound 2 — the SHAPE.** The theorems quantify over the 21 scalar leaves of
`WSC.mintShapedCtx`, not over `ScriptContext`. Everything that shape fixes is
listed in WSC/Shaped/MintingShaped.lean's header: 1 input, 1 output, 0 reference
inputs, one-policy/one-token mint, a 2-entry all-script withdrawal map, 1
redeemer entry, pubkey addresses with no datums, empty cert/signatory/datum/vote/
proposal lists, treasury and donation = 1, and the redeemer fixed to `BurnOnly`
(tag 3) with `pboMintingLogicWdrlIdx = 0`. Everything else — every byte string
and every integer, including BOTH withdrawal credentials and the signed minted
quantity — is universally quantified.

**Bound 2 is NOT a weakening of the postcondition.** The two facts the theorems
conclude are both free in the shape: the withdrawal credentials `w0`, `w1` are
symbolic (so "the minting-logic credential is in the withdrawal map" has to be
earned), and the minted quantity `q` is symbolic and NOT sign-constrained by the
shape (the shape has an output carrying the policy's own token, so the ledger
balance rule permits `q > 0` — see WSC/Shaped/MintingShaped.lean's header).

**ARM SCOPE.** Fixing the redeemer tag to 3 restricts the class to the
`BurnOnly` arm. At budget 900 that costs nothing: the cheapest accepting goldens
of the other three arms are 1,257 and 1,681 CEK steps (WSC/goldens/K-MEASUREMENTS.md
§3), so they cannot accept inside 900 at all. The four-way P4 disjunction is
therefore not restated here; `P4_burnonly_arm_shaped` below is its `BurnOnlyOk`
disjunct, which is what carries P4 at this budget anyway
(WSC/Props/P4_Minting.lean "ARM SCOPE").

**DEFECT D1 STILL APPLIES.** `validMintingContext` includes CLAB's
`validRedeemerMap`, whose `ScriptPurpose` order disagrees with the ledger's
(WSC/STATUS.md §3 D1). SHAPE M1 has exactly ONE redeemer entry, so it is sorted
under either order and D1 does not bite HERE — but that is because the shape
avoids the mixed spending+minting redeemer map that every real programmable-token
mint carries. A shaped theorem over a 2-entry redeemer map would hit D1 head on.
This is a scope statement, not a fix.

════════════════════════════════════════════════════════════════════════════
PRECONDITION AUDIT (arch §4.1)
════════════════════════════════════════════════════════════════════════════
The only hypothesis besides the shape is `validMintingContext (mintShapedCtx …)`
— CLAB ledger normalization, specialized to the shape. It constrains the
withdrawal map only to be credential-SORTED (`validWithdrawals`,
CardanoLedgerApi/V3/Contexts.lean:923), i.e. `w0 < w1`; it says nothing about
WHICH credentials appear. The script parameters `ppCS`, `mlh` are universally
quantified, never concrete hashes. The shape itself supplies no fact about
withdrawals, and the sign of `q` is left to the balance rule.

════════════════════════════════════════════════════════════════════════════
SOURCE FIDELITY
════════════════════════════════════════════════════════════════════════════
Unchanged from WSC/Props/P4_Minting.lean's fidelity stanza (same flat, same
mirrors). The two conjuncts of the `BurnOnly` arm that these theorems certify are
`Issuance.hs:253` (`mintingLogicInvokedAt # wdrlIdx`, defined :150-151 against
`mintingLogicCred` :136) and `Issuance.hs:254`
(`pall # plam (\pair -> pfromData (psndBuiltin # pair) #<= 0) # ownTkPairs`,
where `ownTkPairs = ptryLookupValue # ownCS' # mint` :251).
-/
import WSC.Shaped.MintingShaped
-- the 600 and 800 preps are used ONLY by the concrete witness's step-count
-- bracket at the bottom of this file (their `exec` terms take a `ScriptContext`,
-- so the shaped witness context can be run through them unchanged).
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
                          validMintingContext ownCurrencySymbol credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## The two proved obligations -/

/-- **P4a over SHAPE M1 — PROVED AT UPLC.** *Any accepted `BurnOnly` mint of
shape M1 runs the token's issuance minting-logic script: its script credential
appears in the transaction's withdrawal map.*

This is common conjunct C1 of all four custody arms (Issuance.hs:150-151, listed
at :195, :216, :242, :253). With `LR_WDRL_RUNS_VALIDATOR` (WSC/Honest.lean) it is
what makes the token-specific authorization script unavoidable on every burn in
this class.

NOT hypothesis-implied: `validMintingContext` constrains the withdrawal map only
to be sorted, and both credentials in the shape are free variables.

MEASURED: `✅ Valid`. The same statement over a fully symbolic context is
Undetermined after 3,208 s (WSC/Props/P4_Minting.lean). -/
theorem P4a_shaped_mint_runs_minting_logic :
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
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (mintShapedWdrl w0 w1 a0 a1) := by blaster

/-- **The `BurnOnly` no-positive-mint scan over SHAPE M1 — PROVED AT UPLC.**
*An accepted `BurnOnly` mint of shape M1 is a genuine pure burn: no token of the
policy's own currency symbol has a strictly positive quantity in `txInfoMint`.*

This is the second conjunct of arm 4 (Issuance.hs:251-254). It is EARNED from the
bytecode, not handed over by the hypothesis: SHAPE M1 carries an output holding
the policy's own token, so the ledger balance rule admits `q > 0`
(`q = qOut - qIn` with both quantities strictly positive). A `q > 0` shape-M1
context is ledger-valid; what this theorem says is that the bytecode rejects it.

MEASURED: `✅ Valid`. -/
theorem P4_burn_only_shaped :
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
      mintPos ownCS (mintShapedMint ownCS tn q) = false := by blaster

/-- **P4's arm-4 predicate over SHAPE M1 — PROVED AT UPLC.** The conjunction of
the two theorems above IS `WSC/Spec.lean`'s `BurnOnlyOk`, i.e. the fourth
disjunct of P4. At budget 900 the other three disjuncts are unreachable
(K-MEASUREMENTS §3), so this is P4's positive content at this budget and shape. -/
theorem P4_burnonly_arm_shaped :
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
      BurnOnlyOk mlh ownCS
        (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
        = true := by blaster

/-! ## Polarity controls (ADDENDUM E9) — the FULL control set, all four stanzas -/

/-- Negative control (≡ the contrapositive of P4a over the shape): a shape-M1
context whose withdrawal map does NOT contain the minting-logic credential is
rejected by the bytecode. MEASURED: `✅ Valid`.

NOTE (E9, binding): a negative control is also satisfied by budget-`Error`, so it
cannot by itself detect the 900-step bound. That job belongs to the vacuity probe
and the concrete witness below. -/
theorem P4a_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    validMintingContext
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1) →
    isUnsuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
      := by blaster

/-- Tightness stanza: the NEGATION of P4a's postcondition under an accepting run
must be FALSIFIABLE. Expected and MEASURED: `Falsified`. -/
def P4a_shaped_tightness : Prop :=
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
    ¬ credentialInWithdrawals (Credential.ScriptCredential mlh) (mintShapedWdrl w0 w1 a0 a1)

#blaster (gen-cex: 0) (solve-result: 1) [P4a_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT THE SHAPE** (SPIKE-FINDINGS / E9, and the one
stanza a shaped theorem cannot skip: a shape class can easily be accept-UNSAT,
which would make every theorem above vacuous in a way no other control detects).
"No accepting shape-M1 context exists within 900 CEK steps" must be FALSIFIED.

Expected and MEASURED: `Falsified` — accepting shape-M1 contexts exist inside the
budget. Contrast `WSC/Props/P4_Minting.lean`'s `minting600_is_vacuous`, which is
`Valid` (= genuinely vacuous) at budget 600, and its probe at 900 over a symbolic
context, which is Undetermined after 3,207 s. The concrete witness below
discharges the same obligation a second time, executably and without the SMT
solver. -/
def P4_shaped_vacuity_probe : Prop :=
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

#blaster (gen-cex: 0) (solve-result: 1) [P4_shaped_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE M1 — executable, no SMT

The task's rung-3 requirement: exhibit a concrete accepting context of the exact
shape, so that non-vacuity does not rest on a solver verdict. This instantiates
the 21 leaves of SHAPE M1 and runs the REAL compiled bytecode through the actual
CEK machine (`appliedMintShaped900.exec` = `cekExecuteProgram` at budget 900),
closed by `native_decide`.

Leaf values: burn 3 of `OWNCS.TOK`, spending an input that holds 5 and producing
an output that holds 2, paying 40 lovelace of a 100-lovelace input as fee (so the
ledger balance rule is satisfied on both the ada and the token axis), with the
withdrawal map `[(ScriptCredential "MINTLOGIC", 0), (ScriptCredential "ZZZ", 0)]`
— sorted, and the minting-logic credential is the entry at index 0, which is the
index the `BurnOnly` redeemer names. -/

namespace P4ShapedWitness

-- `native_decide` on the applied program needs more than the default recursion
-- depth (same as WSC/Props/P4_Minting.lean's witness).
set_option maxRecDepth 100000

def ppCS   : CurrencySymbol := ByteString.mk "PARAMS"
def mlh    : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS  : CurrencySymbol := ByteString.mk "OWNCS"
def tn     : TokenName      := ByteString.mk "TOK"
def owner  : ByteString     := ByteString.mk "OWNER"
def dest   : ByteString     := ByteString.mk "DEST"
def w0     : ScriptHash     := ByteString.mk "MINTLOGIC"
def w1     : ScriptHash     := ByteString.mk "ZZZ"

/-- The witness context: SHAPE M1 at the leaf values above. -/
def ctx : ScriptContext :=
  mintShapedCtx ownCS tn (-3) owner 100 5 dest 60 2 w0 w1 0 0 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

/-- Bool reflection of `isSuccessful` (a `Prop`), for `native_decide`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis. -/
theorem ctx_valid : validMintingContext ctx = true := by native_decide

/-- The witness names `ownCS` as the minting policy. -/
theorem ctx_ownCS : ownCurrencySymbol ctx = some ownCS := by native_decide

/-- The witness satisfies P4a's postcondition… -/
theorem ctx_post_P4a :
    credentialInWithdrawals (Credential.ScriptCredential mlh)
      (mintShapedWdrl w0 w1 0 0) = true := by native_decide

/-- …and the `BurnOnly` arm's postcondition, i.e. P4's fourth disjunct. -/
theorem ctx_post_burnOnly : BurnOnlyOk mlh ownCS ctx = true := by native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this
shape-M1 context at budget 900, through the shaped applied term the theorems
above quantify over. -/
theorem exec_accepts_at_900 :
    isSuccessful
      (appliedMintShaped900.exec ppCS mlh ownCS tn (-3) owner 100 5 dest 60 2 w0 w1 0 0 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) :=
  isHaltB_sound _ (by native_decide)

/-- Lower bracket: the SAME context is REJECTED at budget 600 (budget exhaustion
⟹ `Error`), via the unshaped 600 prep's executable term — so the witness's true
CEK step count lies in (600, 900], consistent with the `mint-burnonly` golden's
measured K = 784 (WSC/goldens/K-MEASUREMENTS.md §3). This is what pins the shape
to the same step-count regime as the real off-chain transaction. -/
theorem exec_rejects_at_600 :
    isHaltB (appliedMinting.exec ppCS mlh ctx) = false := by native_decide

/-- …and it is accepted at budget 800 by the unshaped executable term as well —
i.e. the shape adds no measurable step cost over `P4Witness.ctx`. -/
theorem exec_accepts_at_800_unshaped :
    isSuccessful (appliedMinting800.exec ppCS mlh ctx) :=
  isHaltB_sound _ (by native_decide)

/-! ### EXCLUDED-CASE WITNESS — the positive-mint case is real, and rejected

`P4_burn_only_shaped` is only interesting if a shape-M1 context with a STRICTLY
POSITIVE mint of the policy's own token is ledger-valid in the first place. It is,
and the bytecode rejects it. This is a sharper control than the tightness stanza:
tightness only says "some accepting context satisfies the postcondition", whereas
this exhibits the specific ledger-valid context that the postcondition EXCLUDES
and shows the real CEK rejecting it.

Leaves: mint +3 of `OWNCS.TOK`, input holds 2, output holds 5, 100 lovelace in,
60 out, 40 fee — balanced on both axes. -/

/-- SHAPE M1 with `q = +3`. -/
def ctxPos : ScriptContext :=
  mintShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 100 2 (ByteString.mk "DEST") 60 5
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

/-- The positive-mint shape-M1 context IS ledger-valid, and it genuinely has a
positive mint of the policy's own symbol. -/
theorem ctxPos_valid_and_positive :
    validMintingContext ctxPos = true ∧
    mintPos (ByteString.mk "OWNCS") ctxPos.scriptContextTxInfo.txInfoMint = true := by
  native_decide

/-- …and the REAL compiled bytecode REJECTS it at budget 900. So
`P4_burn_only_shaped` excludes a non-empty, ledger-legal set of transactions —
it is not vacuous on its interesting case. -/
theorem exec_rejects_positive_mint :
    isHaltB
      (appliedMintShaped900.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 100 2 (ByteString.mk "DEST") 60 5
        (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) = false := by native_decide

end P4ShapedWitness

end WSC
