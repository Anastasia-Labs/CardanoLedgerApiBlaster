/-
WSC/Props/Shaped/P3ShapedR.lean — **P3, THE KEYSTONE, RE-PROVED AGAINST THE
POST-#112 BASE VALIDATOR** over SHAPES B1RG / B1RS (task N3).

P3 in plain English, unchanged in meaning by PR #112: *you cannot spend a
mini-ledger UTxO unless the global (transfer) or seize validator runs in the
same transaction* — which is what forces the containment checks (P1 or P2) on
every exit from the mini-ledger.

════════════════════════════════════════════════════════════════════════════
BEFORE / AFTER — the honest summary
════════════════════════════════════════════════════════════════════════════
| | pre-#112 (`f918ec6`) | post-#112 (`main` @ 2306678) |
|---|---|---|
| validator route | `pfix` SCAN of `txInfoWdrl` for either parameter | reads the redeemer: constructor TAG picks the arm, `Integer` field INDEXES the credential-sorted withdrawal map, one equality check |
| P3 statement | `∀ ctx, validSpendingContext ctx → accept → cred ∈ wdrl ∨ cred ∈ wdrl` | same postcondition, quantified over SHAPE B1RG / B1RS leaves — and proved in a SHARPER per-arm form (§1), the disjunction being derived |
| P3 proof route | UNSHAPED, fully symbolic `ScriptContext`, the only property in the campaign that needed no coverage argument | **SHAPED** — the unshaped goal no longer closes (measurement below) |
| K (accepting) | 208 (bootstrap ctx) / 208 (golden) | **194** (both bootstraps) / **194** (golden, N2) |

**THE MEASUREMENT, because this is a REGRESSION and it must not be silent.**
Same flat, same `WSC.baseInputs`, same 600-step budget, same machine, three
separate modules so the Z3 cap is per goal:

| goal, UNSHAPED at `appliedBase.prop` (budget 600) | Z3 cap | verdict |
|---|---|---|
| P3 itself (`accept → cred ∈ wdrl ∨ cred ∈ wdrl`) | 600 s | **`⚠️ Undetermined`** (602 s wall) |
| negative control (`¬post → reject`) | 600 s | **`⚠️ Undetermined`** (602 s wall) |
| **vacuity probe** (`∀ ctx, ¬accept`) | 600 s | **`⚠️ Undetermined`** (602 s wall) |
| P3 itself, UNCAPPED (the form the pre-#112 module shipped) | ∞ | no verdict at 93 min, killed |

The vacuity probe coming back Undetermined is the sharp part: Z3 cannot even
EXHIBIT an accepting unshaped context, although one demonstrably exists
(`WSC/Props/P3_Base.lean`'s two bootstrap witnesses both halt accepting at
K = 194, by `native_decide` on the real CEK machine, no solver involved). The
blocker is not that the property became false or vacuous; it is that
`pdropList <symbolic index>` into a symbolic list is a search Z3 does not
finish. Three escalations were run and none recovers it — a 2400 s cap; a
MINIMAL shape freezing only the redeemer's `Data` skeleton and nothing else; a
smaller prep budget (250). See `WSC/Props/P3_Base.lean` §MEASUREMENT for the
full table and `WSC/Props/P3Unshaped.lean.disabled` for the re-runnable goals.

That last escalation is what localizes the blocker: freezing the redeemer alone
does NOT help, and freezing the redeemer AND the withdrawal map — which is
exactly what the shapes below add — closes every goal in under 2 seconds.

CONSEQUENCE FOR `WSC/Coverage.lean` §7: `p3_lives_over_a_covering_class` — "P3
is the one property that needs no coverage argument at all" — is no longer
true of production. That sentence must be retired, not re-pointed.

════════════════════════════════════════════════════════════════════════════
PRECONDITION AUDIT (arch §4.1, may-assume / must-not-assume)
════════════════════════════════════════════════════════════════════════════
* **The redeemer's CONTENT is not assumed.** The shape freezes the redeemer's
  constructor TAG (it is part of the `Data` skeleton `#prep_uplc` needs) and
  NOTHING else about it: the index field `red` is a free symbolic `Integer`, so
  an attacker naming a wrong index, an out-of-range index or a negative index is
  INSIDE the class and the theorem has to survive all of them. Both tags are
  covered, one shape each, so no arm is assumed away.
* **`validSpendingContext` is NOT assumed either** — it is not a hypothesis of
  the theorems below at all. The shaped statements are therefore STRICTLY
  STRONGER on that axis than the pre-#112 unshaped one, which did assume it.
  (It reappears as an obligation on the point-level realizability witness in
  §4, where it belongs.)
* **The two script parameters `gh`/`sh` and the two withdrawal hashes
  `w0`/`w1` are four INDEPENDENT symbolic leaves.** Nothing ties a parameter to
  a withdrawal entry. Tying any of them would have smuggled P3's postcondition
  into the shape.

ANTI-TAUTOLOGY: the postcondition is `CardanoLedgerApi.V3.credentialInWithdrawals`
over `WSC.baseRWdrl`, which `WSC.baseRShapedCtx_wdrl` proves IS the shaped
context's `txInfoWdrl`. It is ground-truth ledger vocabulary; the validator's own
computed value (`witnessed`) appears nowhere in any statement.

SCOPE (ADDENDUM E1 + shaping, both binding): each theorem constrains exactly
those invocations of the real compiled post-#112 `programmableLogicBase`
bytecode that (a) are of SHAPE B1RG / B1RS and (b) halt within 600 CEK steps.
-/
import WSC.Shaped.BaseShapedR
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC

open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash ScriptPurpose TxInfo
                          Withdrawals findRedeemer
                          validSpendingContext credentialInWithdrawals)
open CardanoLedgerApi.V3.Contexts (redeemerCoverageAllPlutus noExtraRedeemersAllPlutus
                                   redeemersExactAllPlutus scriptPurposesWitnessed coveredBy)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ════════════════════════════════════════════════════════════════════════
## §1 THE KEYSTONE, ONE THEOREM PER ARM — proved in its SHARP form
════════════════════════════════════════════════════════════════════════

P3's published conclusion is a DISJUNCTION ("global **or** seize is in the
withdrawal map"), because pre-#112 the validator scanned for either and an
accepting run genuinely did not say which. After #112 it does: the redeemer's
constructor tag selects exactly one of the two parameters. So each arm is
proved in the sharper, per-credential form and the disjunction is DERIVED from
it in pure Lean (`Or.inl` / `Or.inr`, kernel-checked, no second solver call).

Two consequences worth stating: the campaign gets a strictly stronger fact than
it had; and §2's mutation controls can now check that the tag really does select
the arm, which is a sharpness test the pre-#112 statement could not express. -/

/-- **SHAPE B1RG (`SpendViaGlobal`) forces the GLOBAL parameter, specifically.**

Any accepting run of the production post-#112 `programmableLogicBase` spending
validator on a SHAPE B1RG context (within the 600-step bound) implies that the
`globalCred` parameter appears in the transaction's withdrawal map — not merely
one of the two.

Note the index leaf `red` is universally quantified: this holds for a dishonest
witness index too, which after #112 is the point. -/
theorem P3_B1RG_forces_globalCred :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1) := by
  blaster (timeout: 600)

/-- **SHAPE B1RS (`SpendViaSeize`) forces the SEIZE parameter, specifically.**

This arm is worth having on its own: NO GOLDEN VECTOR exercises `SpendViaSeize`
(task N2 §5 records that gap explicitly — tag 1 is pinned only negatively
there), so this theorem and the `B1RS` witness in §3 are the only positive
evidence in the library about the seize arm of the new base redeemer. -/
theorem P3_B1RS_forces_seizeCred :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
      credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1) := by
  blaster (timeout: 600)

/-- **P3 (keystone), SHAPE B1RG — the published disjunctive form.**

Combined with LR6/LR-CTX ("a script-cred withdrawal entry means that stake
validator ran and succeeded"), every base spend of this shape forces a run of
the global (⟹ P1) or seize (⟹ P2) validator over the same transaction. This
is the form the composition consumes. DERIVED, not separately solved. -/
theorem P3_base_requires_global_or_seize_B1RG
    (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString)
    (h : isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                         rw0 rw1 lo hi tid)) :
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1) :=
  Or.inl (P3_B1RG_forces_globalCred gh sh baseHash lovelace w0 w1 a0 a1 fee red
            rw0 rw1 lo hi tid h)

/-- **P3 (keystone), SHAPE B1RS — the published disjunctive form.** DERIVED. -/
theorem P3_base_requires_global_or_seize_B1RS
    (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString)
    (h : isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                         rw0 rw1 lo hi tid)) :
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1) :=
  Or.inr (P3_B1RS_forces_seizeCred gh sh baseHash lovelace w0 w1 a0 a1 fee red
            rw0 rw1 lo hi tid h)

/-! ### §1b ARM-SELECTION SHARPNESS — the mutation controls

If the shape or the prep were wrong in a way that made the redeemer tag
irrelevant, §1's two theorems would BOTH still be `Valid` (each would just be
proving the same scan fact twice). The two probes below rule that out: swapping
the credential in each arm's conclusion must be FALSIFIABLE. Expected result:
Falsified, both. Together with §1 this pins the `pif` on `tag #== 0`
(`ProgrammableLogicBase.hs:729`) as really selecting the parameter. -/

/-- MUTATION CONTROL: SHAPE B1RG does NOT force the seize parameter into the
map. Expected result: Falsified. -/
def P3_B1RG_does_not_force_seizeCred : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
      credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RG_does_not_force_seizeCred]

/-- MUTATION CONTROL: SHAPE B1RS does NOT force the global parameter into the
map. Expected result: Falsified. -/
def P3_B1RS_does_not_force_globalCred : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
      credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RS_does_not_force_globalCred]

/-! ════════════════════════════════════════════════════════════════════════
## §2 POLARITY CONTROLS, TIGHTNESS, AND THE MANDATORY VACUITY PROBES
════════════════════════════════════════════════════════════════════════

NOTE (ADDENDUM E9, binding): the negative controls are satisfied by
budget-`Error` as well, so they cannot detect the bound. The vacuity probes —
**at these terms and these shapes**, not at some other prep — plus the concrete
`native_decide` witnesses of §3 are what rule out vacuity. This is the highest
risk axis in the campaign (SHAPE G6 at budget 2500 was silently accept-UNSAT and
only its probe caught it), so both probes are run at both arms. -/

/-- Negative control, SHAPE B1RG: a context of the shape violating the
postcondition (NEITHER parameter in the withdrawal map) is rejected by the
bytecode. -/
theorem P3_B1RG_negative_control :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1)) →
    isUnsuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                      rw0 rw1 lo hi tid) := by
  blaster (timeout: 600)

/-- Negative control, SHAPE B1RS. -/
theorem P3_B1RS_negative_control :
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1)) →
    isUnsuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                      rw0 rw1 lo hi tid) := by
  blaster (timeout: 600)

/-- Tightness stanza, SHAPE B1RG: the NEGATION of P3's postcondition under an
accepting run must be FALSIFIABLE. Expected result: Falsified. -/
def P3_B1RG_tightness : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1))

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RG_tightness]

/-- Tightness stanza, SHAPE B1RS. Expected result: Falsified. -/
def P3_B1RS_tightness : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                    rw0 rw1 lo hi tid) →
    ¬(credentialInWithdrawals (.ScriptCredential gh) (baseRWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals (.ScriptCredential sh) (baseRWdrl w0 w1 a0 a1))

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RS_tightness]

/-- **MANDATORY vacuity probe, SHAPE B1RG, AT ITS OWN PREP TERM.** "No
accepting context of this shape within budget 600" must be FALSIFIED — i.e.
accepting contexts exist inside the meter, so §1 is not vacuous.
Expected result: Falsified. -/
def P3_B1RG_vacuity_probe : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬ isSuccessful (appliedBaseB1RG.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                      rw0 rw1 lo hi tid)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RG_vacuity_probe]

/-- **MANDATORY vacuity probe, SHAPE B1RS, AT ITS OWN PREP TERM.**
Expected result: Falsified. -/
def P3_B1RS_vacuity_probe : Prop :=
  ∀ (gh sh baseHash : ScriptHash) (lovelace : Integer) (w0 w1 : ScriptHash)
    (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString),
    ¬ isSuccessful (appliedBaseB1RS.prop gh sh baseHash lovelace w0 w1 a0 a1 fee red
                      rw0 rw1 lo hi tid)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [P3_B1RS_vacuity_probe]

/-! ════════════════════════════════════════════════════════════════════════
## §3 CONCRETE ACCEPTING WITNESSES, K PINNED TWO-SIDED
════════════════════════════════════════════════════════════════════════

One witness per arm. Both are members of the shape by construction (each is a
`baseRShapedCtx` application), both satisfy `validSpendingContext` OUTRIGHT (no
relaxation), and both are accepted by the REAL compiled bytecode through
`cekExecuteProgram` under `native_decide` — no solver anywhere on this path.

K is pinned TWO-SIDED: `Halt` at K and budget-`Error` at K − 1. -/

namespace P3RWitness

open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

/-- Global parameter hash. Deliberately EQUAL to `w0` in the witness so the
accepting instance goes through the FIRST disjunct; `sh`/`w1` do the same for
the seize arm. Nothing in §1 ties them. -/
def gh : ScriptHash := ByteString.mk "AAA"
/-- Seize parameter hash. -/
def sh : ScriptHash := ByteString.mk "ZZZ"

/-- SHAPE B1RG witness: withdrawal map `[(Script "AAA", 0), (Script "ZZZ", 0)]`
(credential-sorted, as the ledger requires), redeemer `SpendViaGlobal 0` — the
HONEST index, naming entry 0, whose credential is `gh`. -/
def ctxG : ScriptContext :=
  baseRShapedCtx 0 (ByteString.mk "BASE") 100 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
    0 0 100 0 7 9 0 1 (ByteString.mk "")

/-- SHAPE B1RS witness: same map, redeemer `SpendViaSeize 1` — index 1, whose
credential is `sh`. -/
def ctxS : ScriptContext :=
  baseRShapedCtx 1 (ByteString.mk "BASE") 100 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
    0 0 100 1 7 9 0 1 (ByteString.mk "")

/-- The metered run of the REAL bytecode on the B1RG witness's leaves. -/
def runG (K : Nat) :=
  cekExecuteProgram programmableLogicBase.script
    (baseRGInputs gh sh (ByteString.mk "BASE") 100 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
      0 0 100 0 7 9 0 1 (ByteString.mk "")) K

/-- The metered run of the REAL bytecode on the B1RS witness's leaves. -/
def runS (K : Nat) :=
  cekExecuteProgram programmableLogicBase.script
    (baseRSInputs gh sh (ByteString.mk "BASE") 100 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
      0 0 100 1 7 9 0 1 (ByteString.mk "")) K

/-- Bool reflection of `isSuccessful` (a `Prop`), for `native_decide`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- **K = 194, PINNED TWO-SIDED, SHAPE B1RG.** The run HALTS at 194 steps and
budget-errors at 193, so 194 is exactly the minimal budget at which the outcome
appears; it is also stable at 10× (1940). Pre-#112 the same-role bootstrap cost
208. -/
theorem K_B1RG_two_sided :
    isHaltB (runG 194) = true ∧ isHaltB (runG 193) = false ∧ isHaltB (runG 1940) = true := by
  native_decide

/-- **K = 194, PINNED TWO-SIDED, SHAPE B1RS.** -/
theorem K_B1RS_two_sided :
    isHaltB (runS 194) = true ∧ isHaltB (runS 193) = false ∧ isHaltB (runS 1940) = true := by
  native_decide

/-- AUDIT LINK, and the one that stops this section being about a different
term than §1: at the module's own budget, `runG` IS the shaped prep's
executable output at the witness's leaves. `rfl` — kernel computation, no
solver, no axiom. (`WSC/Props/P3_BaseRun.lean`'s `exec_B1RG` then carries the
same term to `Runs.baseRun 600`.) -/
theorem runG_is_exec :
    runG 600 = appliedBaseB1RG.exec gh sh (ByteString.mk "BASE") 100
      (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0 100 0 7 9 0 1 (ByteString.mk "") := rfl

/-- Same for the seize arm. -/
theorem runS_is_exec :
    runS 600 = appliedBaseB1RS.exec gh sh (ByteString.mk "BASE") 100
      (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0 100 1 7 9 0 1 (ByteString.mk "") := rfl

/-- REAL-CEK acceptance of the B1RG witness at the module's 600-step budget. -/
theorem exec_accepts_G : isSuccessful (runG 600) := isHaltB_sound _ (by native_decide)

/-- REAL-CEK acceptance of the B1RS witness at the module's 600-step budget. -/
theorem exec_accepts_S : isSuccessful (runS 600) := isHaltB_sound _ (by native_decide)

/-- Both witnesses satisfy the ledger-normalization predicate OUTRIGHT. -/
theorem ctx_valid : validSpendingContext ctxG = true ∧ validSpendingContext ctxS = true := by
  native_decide

/-- Each witness satisfies P3's postcondition, through a DIFFERENT disjunct —
`ctxG` through the global parameter, `ctxS` through the seize parameter. That
both disjuncts are reachable is what makes the disjunction in §1 non-degenerate. -/
theorem ctx_post :
    credentialInWithdrawals (.ScriptCredential gh)
      ctxG.scriptContextTxInfo.txInfoWdrl = true
    ∧ credentialInWithdrawals (.ScriptCredential sh)
      ctxS.scriptContextTxInfo.txInfoWdrl = true := by
  native_decide

end P3RWitness

/-! ════════════════════════════════════════════════════════════════════════
## §4 SHAPE REALIZABILITY — class level and point level
════════════════════════════════════════════════════════════════════════

Why this section is not optional: shapes that omit redeemer entries are
PROVABLY UNBUILDABLE (audit **F2**). Conway UTXOW's `hasExactSetOfRedeemers`
requires one redeemer entry per script witness, and
`#redeemers = #script-inputs + #mint-policies + #script-withdrawals`, measured
exact on 13/13 goldens. The OLD SHAPE B1 (`WSC/Shaped/BaseShaped.lean`) has two
script-credential withdrawals and a ONE-entry redeemer map, so its class is
empty; SHAPES B1RG / B1RS carry three entries and are not.

* **CLASS LEVEL** (`baseR_class_covered`): for EVERY leaf assignment and both
  tags, the shape's redeemer map covers every script purpose the transaction's
  own `TxInfo` shows to need one — CLAB's `redeemerCoverageAllPlutus`, the
  `MissingRedeemers` half of the Conway rule, in the ledger's own vocabulary.
* **POINT LEVEL** (`b1RG_realizable` / `b1RS_realizable`): a concrete inhabitant
  of each class that is simultaneously `validSpendingContext`, satisfies
  `redeemersExactAllPlutus` (BOTH halves — `MissingRedeemers` AND
  `ExtraRedeemers`), and is ACCEPTED by the real compiled bytecode.

WHAT THIS DOES NOT CLAIM: redeemer coverage is NECESSARY for a node to accept,
not sufficient. A fully node-accepted transaction additionally needs every OTHER
script to succeed — here the two stake validators sitting at `w0`/`w1`. Those
are separate validators and separate properties (P1, P2). -/

/-- The three-entry map covers the `Spending` purpose of the own input — the
purpose whose absence made SHAPE T1 (and, by the same argument, the old SHAPE
B1) empty. Kernel computation. -/
theorem baseR_spending_covered (w0 w1 : ScriptHash) (rw0 rw1 : Integer)
    (own : PlutusCore.Data.Data) :
    (findRedeemer (ScriptPurpose.Spending baseROutRef)
      (baseRRedeemers w0 w1 rw0 rw1 own)).isSome = true := rfl

/-- …and it covers the `Rewarding` purpose of EITHER script withdrawal.

The case split is real, not bureaucratic: `w0` and `w1` are independent symbolic
hashes, so whether the map's `Rewarding w0` entry already answers the
`Rewarding w1` lookup is undecided at this level. Coverage holds either way — a
duplicated key still returns `some`. -/
theorem baseR_rewarding_covered (w0 w1 h : ScriptHash) (rw0 rw1 : Integer)
    (own : PlutusCore.Data.Data) (hh : h = w0 ∨ h = w1) :
    (findRedeemer (ScriptPurpose.Rewarding (Credential.ScriptCredential h))
      (baseRRedeemers w0 w1 rw0 rw1 own)).isSome = true := by
  show (if (ScriptPurpose.Spending baseROutRef
            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
        then some own
        else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                  == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
             then some (PlutusCore.Data.Data.I rw0)
             else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w1)
                       == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                  then some (PlutusCore.Data.Data.I rw1) else none).isSome = true
  rw [show (ScriptPurpose.Spending baseROutRef
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  by_cases hw : (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
  · simp [hw]
  · have hw1 : h = w1 := by
      rcases hh with h1 | h1
      · exact absurd (by rw [h1]; simp) hw
      · exact h1
    subst hw1
    simp [hw]

/-- **SHAPES B1RG / B1RS ARE REDEEMER-COVERED, FOR EVERY LEAF ASSIGNMENT AND
BOTH TAGS.** Stated in CLAB's ledger vocabulary (`redeemerCoverageAllPlutus`,
the `MissingRedeemers` half of Conway UTXOW's `hasExactSetOfRedeemers`) rather
than a WSC-local predicate, so it needs no separate faithfulness argument.

The `show` step is where the shape does its work: `scriptPurposesWitnessed`
reduces by `rfl` to exactly `[Spending ⟨"",0⟩, Rewarding w0, Rewarding w1]`
because the skeleton fixes one script-payment input, two script-credential
withdrawals and an empty mint / certificate / vote / proposal list. -/
theorem baseR_class_covered (tag : Nat)
    (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 fee red rw0 rw1 lo hi : Integer) (tid : ByteString) :
    redeemerCoverageAllPlutus
      ((baseRShapedCtx tag baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi
          tid).scriptContextTxInfo) = true := by
  show ((findRedeemer (ScriptPurpose.Spending baseROutRef)
          (baseRRedeemers w0 w1 rw0 rw1 (baseRRedeemerData tag red))).isSome
     && ((findRedeemer (ScriptPurpose.Rewarding (Credential.ScriptCredential w0))
          (baseRRedeemers w0 w1 rw0 rw1 (baseRRedeemerData tag red))).isSome
     && ((findRedeemer (ScriptPurpose.Rewarding (Credential.ScriptCredential w1))
          (baseRRedeemers w0 w1 rw0 rw1 (baseRRedeemerData tag red))).isSome
        && true))) = true
  rw [baseR_spending_covered, baseR_rewarding_covered w0 w1 w0 rw0 rw1 _ (Or.inl rfl),
      baseR_rewarding_covered w0 w1 w1 rw0 rw1 _ (Or.inr rfl)]
  rfl

/-- **SHAPE B1RG IS REALIZABLE.** Budget 600, witness K = 194. -/
theorem b1RG_realizable :
    validSpendingContext P3RWitness.ctxG = true
    ∧ redeemersExactAllPlutus P3RWitness.ctxG.scriptContextTxInfo = true
    ∧ redeemerCoverageAllPlutus P3RWitness.ctxG.scriptContextTxInfo = true
    ∧ isSuccessful (P3RWitness.runG 600) :=
  ⟨P3RWitness.ctx_valid.1, by native_decide,
   baseR_class_covered 0 (ByteString.mk "BASE") 100 (ByteString.mk "AAA")
     (ByteString.mk "ZZZ") 0 0 100 0 7 9 0 1 (ByteString.mk ""),
   P3RWitness.exec_accepts_G⟩

/-- **SHAPE B1RS IS REALIZABLE.** Budget 600, witness K = 194. This is the
library's only positive evidence about the `SpendViaSeize` arm — no golden
vector exercises it (task N2 §5). -/
theorem b1RS_realizable :
    validSpendingContext P3RWitness.ctxS = true
    ∧ redeemersExactAllPlutus P3RWitness.ctxS.scriptContextTxInfo = true
    ∧ redeemerCoverageAllPlutus P3RWitness.ctxS.scriptContextTxInfo = true
    ∧ isSuccessful (P3RWitness.runS 600) :=
  ⟨P3RWitness.ctx_valid.2, by native_decide,
   baseR_class_covered 1 (ByteString.mk "BASE") 100 (ByteString.mk "AAA")
     (ByteString.mk "ZZZ") 0 0 100 1 7 9 0 1 (ByteString.mk ""),
   P3RWitness.exec_accepts_S⟩

/-! ════════════════════════════════════════════════════════════════════════
## §5 RETIREMENT OF THE OLD SHAPE B1 — PROVED, NOT ASSERTED
════════════════════════════════════════════════════════════════════════

SHAPE B1 (`WSC/Shaped/BaseShaped.lean`) is the pre-#112 base shape. It carries
`scriptContextRedeemer := Data.I red` — a bare integer, because the pre-#112
validator never looked at its redeemer. Against the post-#112 bytecode
`pasConstr` on a `Data.I` ERRORS, so no member of that class can be accepted at
all.

That is a fact worth machine-checking rather than asserting, because it is what
turns "SHAPE B1's results are invalidated" into "SHAPE B1's results are
VACUOUS": anything of the form `accept → …` over `appliedBaseShaped` is now
true for the empty reason, and any future edit that re-proves such a theorem
would get a green tick over nothing. `WSC/ShapeBridge.lean`'s `bridge_B1`,
`inputs_B1`, `exec_B1` and the three `control_B1_*` stanzas are all in that
position and need the final unit's attention.

MEASURED (`WSC/Shaped/Calib/P3Shaped.lean`, the Z2 rung-2 module, which is
where the probe lives so it is run exactly once):
`∀ leaves, ¬ isSuccessful (appliedBaseShaped.prop leaves)` is **`✅ Valid`** at a
600 s Z3 cap, in 5.1 s — i.e. the accept class of SHAPE B1 under the post-#112
bytecode is EMPTY. Note the polarity: this is the one place in the campaign
where a vacuity probe coming back `Valid` is the intended result, and it is
labelled as such there. -/

/-! ## AXIOM AUDIT -/

#print axioms WSC.P3_B1RG_forces_globalCred
#print axioms WSC.P3_B1RS_forces_seizeCred
#print axioms WSC.P3_base_requires_global_or_seize_B1RG
#print axioms WSC.P3_base_requires_global_or_seize_B1RS
#print axioms WSC.P3RWitness.K_B1RG_two_sided
#print axioms WSC.P3RWitness.K_B1RS_two_sided
#print axioms WSC.b1RG_realizable
#print axioms WSC.b1RS_realizable

end WSC
