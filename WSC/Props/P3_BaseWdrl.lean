/-
WSC/Props/P3_BaseWdrl.lean — **P3, THE KEYSTONE, AT SHAPE B1W** (task N6).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS — and it REVERSES part of task N3's regression report
════════════════════════════════════════════════════════════════════════════
Task N3 measured that after wsc-poc PR #112 the UNSHAPED P3 goal no longer
closes (`⚠️ Undetermined` at a 600 s cap, at a 2400 s cap, at a redeemer-only
shape and at a smaller prep budget — `WSC/Props/P3_Base.lean` §MEASUREMENT), and
re-proved P3 over SHAPES B1RG / B1RS, which freeze the WHOLE `TxInfo`: one
input, no outputs, no reference inputs, an empty mint, a three-entry redeemer map
and a frozen redeemer constructor tag.

That cut is unusable by `WSC/Composition.lean`.  The composition runs the base
validator at `WSC.withPurpose ctx r (.SpendingScript …)`, whose `TxInfo` is the
LEDGER transaction's — and the classes the composition's leaves are discharged
over (SHAPE T1R: two inputs, two outputs, two reference inputs; SHAPE S1R: two
inputs, two outputs, a mint) are DISJOINT from B1RG/B1RS.  With P3 available only
at B1R, branch C of `Composition.nonEscape_of_registered` — *exit: a mini-ledger
UTxO is spent* — cannot be closed for either composed class, and both composed
results die.

N3 localised the blocker correctly ("it is the symbolic withdrawal LIST under
`pdropList <symbolic index>`") but tested only two points: redeemer-only (fails)
and redeemer + withdrawal map (closes in < 2 s).  **The intermediate point was
never measured.**  It is measured here, and it closes:

| cut | redeemer | rest of `TxInfo` | params | verdict | wall |
|---|---|---|---|---|---|
| unshaped (N3) | symbolic | symbolic | symbolic | `⚠️ Undetermined` | 602 s / 2404 s |
| redeemer-only (N3) | `Constr 0 [I red]` | symbolic | symbolic | `⚠️ Undetermined` | 903 s |
| **B1W (this module)** | **symbolic `Data`** | **symbolic** | **symbolic `Credential`** | **✅ Valid** | **≈ 4 s** |
| B1RG/B1RS (N3) | `Constr t [I red]` | frozen | `ScriptCredential` | ✅ Valid | ≈ 2 s |

SHAPE **B1W** freezes exactly ONE thing: `txInfoWdrl` is a two-entry list at two
script credentials.  Both script hashes, both amounts, the redeemer (a free
symbolic `Data`, so a wrong index, a wrong constructor tag, a non-`Constr`
redeemer and a non-redeemer are all inside the class), the `ScriptInfo`, every
other `TxInfo` field, and BOTH script parameters (free symbolic `Credential`s —
constructor tags NOT frozen) stay symbolic.

FREEZING THE TWO WITHDRAWAL CREDENTIALS' KIND IS NOT NECESSARY, only cheap:
`WSC/Shaped/Probe/P3WdrlLadder.lean`'s `P3_cc` proves the same statement with
BOTH withdrawal credentials fully symbolic `Credential`s, `✅ Valid`.  It is not
used here because the seven solver calls of this module then cost more than ten
minutes against about five seconds, and both classes the composition instantiates
at have `ScriptCredential` withdrawals anyway.

WHY THAT PARTICULAR CUT IS THE RIGHT ONE: it is the withdrawal map SHAPE T1R and
SHAPE S1R both already have — `WSC.p1ShapedWdrl` and `WSC.seizeShapedWdrl` are
both literally `[(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]`
(`WSC/Shaped/GlobalShapedP1.lean:250-251`, `WSC/Shaped/SeizeShaped.lean:262-263`),
which is `bwWdrl`.  So the composition's two classes satisfy the B1W side
condition by `rfl`, and `p3_lifted` is restored over both.

WHAT IS STILL LOST relative to pre-#112, stated plainly: P3 used to hold for a
transaction with a withdrawal map of ANY LENGTH.  It now holds only at a FIXED
length — measured `✅ Valid` at 1 and 2 and `⚠️` (no verdict at a 900 s cap) at 3
(`WSC/Shaped/Probe/P3WdrlLadder.lean`).  The length is what
`pdropList <symbolic index>` cannot tolerate symbolically.
`WSC/Shaped/Probe/P3WdrlLadder.lean` measures how far the cut generalises.

THE INPUTS FUNCTION IS LITERALLY `WSC.baseInputs`, so `WSC.Runs.baseRun 600` and
this prep's `exec` are the same term by `rfl` (§1) — the `prop`-vs-`exec` residual
(audit F8) stays off the composition's keystone path exactly as task A1 arranged.
-/
import WSC.Prep.Base
import WSC.Runs.Base
import WSC.Props.Shaped.P3ShapedR
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC

open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash ScriptInfo TxInfo
                          Withdrawals credentialInWithdrawals validSpendingContext)
open CardanoLedgerApi.V3.Contexts (redeemerCoverageAllPlutus redeemersExactAllPlutus)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §0 SHAPE B1W -/

/-- The ONLY frozen thing: a two-entry withdrawal map at two script credentials.
Definitionally equal to `WSC.p1ShapedWdrl` (SHAPE T1R), `WSC.seizeShapedWdrl`
(SHAPE S1R) and `WSC.baseRWdrl` (SHAPES B1RG/B1RS) — see §5.  The map's LENGTH is
the load-bearing part: `WSC/Shaped/Probe/P3WdrlLadder.lean` measures `✅ Valid` at
lengths 1 and 2 (with the credentials fully symbolic too) and NO VERDICT at
length 3, at a 900 s cap. -/
def bwWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- SHAPE B1W.  `ti`, `red` and `si` are FREE symbolic leaves. -/
def bwCtx (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer) : ScriptContext :=
  { scriptContextTxInfo := { ti with txInfoWdrl := bwWdrl w0 w1 a0 a1 }
  , scriptContextRedeemer := red
  , scriptContextScriptInfo := si }

/-- Literally `WSC.baseInputs`, which is what makes §1's bridge `rfl`. -/
def bwInputs (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer) : List Term :=
  baseInputs g s (bwCtx ti red si w0 w1 a0 a1)

#prep_uplc appliedBaseB1W programmableLogicBase bwInputs 600

/-! ## §1 P3 AT SHAPE B1W — the `prop` form and the RUN form -/

/-- **P3 at SHAPE B1W, `prop` form.** -/
theorem P3_B1W_prop :
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    isSuccessful (appliedBaseB1W.prop g s ti red si w0 w1 a0 a1) →
      credentialInWithdrawals g (bwWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals s (bwWdrl w0 w1 a0 a1) := by
  blaster (timeout: 900)

/-- The prep's EXECUTABLE output IS `Runs.baseRun 600`, by `rfl`, because
`bwInputs` IS `baseInputs`.  No `Optimize.main` output on this path. -/
theorem exec_B1W (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer) :
    appliedBaseB1W.exec g s ti red si w0 w1 a0 a1
      = Runs.baseRun 600 g s (bwCtx ti red si w0 w1 a0 a1) := rfl

/-- **P3 at SHAPE B1W, RUN form** — the form `WSC.LR_BUDGET_base` delivers and
`WSC.Composition.p3_lifted` consumes. -/
theorem P3_B1W_run :
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    isSuccessful (Runs.baseRun 600 g s (bwCtx ti red si w0 w1 a0 a1)) →
      credentialInWithdrawals g (bwWdrl w0 w1 a0 a1)
      ∨ credentialInWithdrawals s (bwWdrl w0 w1 a0 a1) := by
  blaster (timeout: 900)

/-! ## §2 CONTROLS AND THE MANDATORY VACUITY PROBES

Four stanzas, two at the prep term and two at the run term — a restated theorem
needs a restated probe. -/

/-- **MANDATORY vacuity probe at SHAPE B1W's OWN PREP TERM.**  "No accepting
context of this shape within budget 600" must be FALSIFIED.
Expected: Falsified. -/
def P3_B1W_vacuity_probe : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    ¬ isSuccessful (appliedBaseB1W.prop g s ti red si w0 w1 a0 a1)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_B1W_vacuity_probe]

/-- **MANDATORY vacuity probe at SHAPE B1W's OWN RUN TERM.**
Expected: Falsified. -/
def P3_B1W_run_vacuity_probe : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    ¬ isSuccessful (Runs.baseRun 600 g s (bwCtx ti red si w0 w1 a0 a1))

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_B1W_run_vacuity_probe]

/-- **TIGHTNESS.**  Drop the seize disjunct: acceptance must NOT force the
GLOBAL credential into the map, because the `SpendViaSeize` arm exists.
Expected: Falsified.  A `Valid` here would mean the theorem's disjunction is
decoration and one half is doing all the work. -/
def P3_B1W_tightness_global : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    isSuccessful (appliedBaseB1W.prop g s ti red si w0 w1 a0 a1) →
      credentialInWithdrawals g (bwWdrl w0 w1 a0 a1)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_B1W_tightness_global]

/-- **TIGHTNESS, the other half.**  Expected: Falsified. -/
def P3_B1W_tightness_seize : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    isSuccessful (appliedBaseB1W.prop g s ti red si w0 w1 a0 a1) →
      credentialInWithdrawals s (bwWdrl w0 w1 a0 a1)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_B1W_tightness_seize]

/-- **NEGATIVE CONTROL.**  If NEITHER parameter is a withdrawal credential the
bytecode must refuse.  This is the contrapositive of §1 and is stated separately
so a solver regression that made §1 vacuously true would show up here as a
polarity mismatch rather than silently.  Expected: Valid. -/
theorem P3_B1W_negative_control :
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (w0 w1 : ScriptHash) (a0 a1 : Integer),
    ¬ credentialInWithdrawals g (bwWdrl w0 w1 a0 a1) →
    ¬ credentialInWithdrawals s (bwWdrl w0 w1 a0 a1) →
      ¬ isSuccessful (appliedBaseB1W.prop g s ti red si w0 w1 a0 a1) := by
  blaster (timeout: 900)

/-! ## §3 CONCRETE ACCEPTING WITNESS, K PINNED TWO-SIDED

SHAPE B1RG ⊆ SHAPE B1W (§5), so task N3's certified B1RG witness is a B1W
inhabitant.  The identification below is `rfl`, so the K measurement and the
realizability certificate transfer without a second `native_decide`. -/

/-- **SHAPE B1RG's witness IS a SHAPE B1W instance**, by kernel computation. -/
theorem ctxG_is_B1W :
    bwCtx P3RWitness.ctxG.scriptContextTxInfo P3RWitness.ctxG.scriptContextRedeemer
      P3RWitness.ctxG.scriptContextScriptInfo
      (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0
      = P3RWitness.ctxG := rfl

/-- **SHAPE B1RS's witness is likewise a SHAPE B1W instance** — so the class
contains inhabitants of BOTH redeemer arms. -/
theorem ctxS_is_B1W :
    bwCtx P3RWitness.ctxS.scriptContextTxInfo P3RWitness.ctxS.scriptContextRedeemer
      P3RWitness.ctxS.scriptContextScriptInfo
      (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0
      = P3RWitness.ctxS := rfl

/-- **K = 194, PINNED TWO-SIDED, at SHAPE B1W's own run term.**  `Runs.baseRun`
HALTS at 194 and budget-errors at 193; stable at 10×.  `native_decide` on the
real CEK machine, no solver.  (Same 194 as `WSC.P3RWitness.K_B1RG_two_sided` and
as the regenerated golden `base-spend-transfer-tx` — `WSC/goldens/
K-MEASUREMENTS.md` §3.) -/
theorem K_B1W_two_sided :
    P3RWitness.isHaltB (Runs.baseRun 194 (.ScriptCredential P3RWitness.gh)
      (.ScriptCredential P3RWitness.sh) P3RWitness.ctxG) = true
    ∧ P3RWitness.isHaltB (Runs.baseRun 193 (.ScriptCredential P3RWitness.gh)
      (.ScriptCredential P3RWitness.sh) P3RWitness.ctxG) = false
    ∧ P3RWitness.isHaltB (Runs.baseRun 1940 (.ScriptCredential P3RWitness.gh)
      (.ScriptCredential P3RWitness.sh) P3RWitness.ctxG) = true := by
  native_decide

/-! ## §4 REALIZABILITY

SHAPE B1W does not constrain the redeemer map at all, so a CLASS-level
`redeemerCoverageAllPlutus` theorem is not even statable over it — the class
contains contexts that are provably unbuildable (audit **F2**), exactly as it
contains contexts the validator rejects.  That is not a weakening of the
theorem: what realizability has to establish is that the class is not
DISJOINT from the buildable, accepting transactions, and that is a POINT-level
obligation, discharged here by an inhabitant that is simultaneously ledger-valid,
Conway-redeemer-exact in BOTH directions, redeemer-covered, and accepted by the
production bytecode.

The class-level statement that does exist is N3's, over the SUBSET B1RG/B1RS
(`WSC.baseR_class_covered`, `✅ Valid` for both tags): every context of those
sub-shapes is redeemer-covered.  §5's inclusion is what makes that a statement
about B1W inhabitants. -/

/-- **THE B1W CLASS IS NODE-REALIZABLE.**  Every conjunct is `native_decide` or a
theorem; nothing is assumed. -/
theorem b1W_realizable :
    validSpendingContext P3RWitness.ctxG = true
    ∧ redeemersExactAllPlutus P3RWitness.ctxG.scriptContextTxInfo = true
    ∧ redeemerCoverageAllPlutus P3RWitness.ctxG.scriptContextTxInfo = true
    ∧ isSuccessful (Runs.baseRun 600 (.ScriptCredential P3RWitness.gh)
        (.ScriptCredential P3RWitness.sh) P3RWitness.ctxG) :=
  ⟨b1RG_realizable.1, b1RG_realizable.2.1, b1RG_realizable.2.2.1,
   P3RWitness.isHaltB_sound _ (by native_decide)⟩

/-! ## §5 THE SHAPE SIDE CONDITION, AND WHO SATISFIES IT

`WdrlPair ctx` is the ONE thing SHAPE B1W asks of a transaction.  It is a
statement in ground-truth ledger vocabulary about `txInfoWdrl` and nothing else. -/

/-- SHAPE B1W's side condition on a transaction: the withdrawal map is exactly two
entries at two script credentials.  Nothing is said about either amount, and
nothing at all about any other part of the transaction. -/
def WdrlPair (ctx : ScriptContext) : Prop :=
  ∃ w0 w1 a0 a1, ctx.scriptContextTxInfo.txInfoWdrl = bwWdrl w0 w1 a0 a1

/-- SHAPES B1RG/B1RS's withdrawal map is `bwWdrl`, definitionally.  The same
identity for SHAPE T1R's `WSC.p1ShapedWdrl` and SHAPE S1R's
`WSC.seizeShapedWdrl` is proved where those are in scope —
`WSC/Props/Shaped/RealizableLeaves.lean` §W and
`WSC/Props/Shaped/RealizableLeavesS1R.lean` §W — so this module does not have to
import the two heavy shape builders. -/
theorem baseRWdrl_is_bwWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) :
    baseRWdrl w0 w1 a0 a1 = bwWdrl w0 w1 a0 a1 := rfl

/-- A context satisfying `WdrlPair` IS a SHAPE B1W instance — structure eta, no
solver, no axiom.  This is what lets §1's shaped theorem be applied to a
transaction the composition produced rather than one this module built. -/
theorem bwCtx_eta (ctx : ScriptContext) (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (hw : ctx.scriptContextTxInfo.txInfoWdrl = bwWdrl w0 w1 a0 a1) :
    bwCtx ctx.scriptContextTxInfo ctx.scriptContextRedeemer
      ctx.scriptContextScriptInfo w0 w1 a0 a1 = ctx := by
  obtain ⟨ti, red, si⟩ := ctx
  obtain ⟨i, ri, o, f, m, c, w, vr, sg, rd, dt, tid, v, pp, tr, td⟩ := ti
  simp only [bwCtx] at *
  rw [← hw]

/-! ## §6 THE FORM `WSC.Composition.p3_lifted` CONSUMES

Stated at an ARBITRARY `ScriptContext` under the single side condition, in
ground-truth vocabulary (`credentialInWithdrawals` on the context's own
`txInfoWdrl`), so no shape-specific identifier appears in the conclusion. -/

/-- **P3, RUN FORM, AT AN ARBITRARY CONTEXT WITH A TWO-SCRIPT WITHDRAWAL MAP.**
*If the production `programmableLogicBase` bytecode accepts a spend within 600
CEK steps and the transaction's withdrawal map is a two-entry script map, then
one of the two parameter credentials is IN that map.*

No hypothesis on the redeemer, the inputs, the outputs, the mint, the redeemer
map, the script info or the parameters' constructor tags. -/
theorem P3_base_requires_global_or_seize_run_W
    (g s : Credential) (ctx : ScriptContext) (hw : WdrlPair ctx)
    (h : isSuccessful (Runs.baseRun 600 g s ctx)) :
    credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
    ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  obtain ⟨w0, w1, a0, a1, hwd⟩ := hw
  have hctx := bwCtx_eta ctx w0 w1 a0 a1 hwd
  rw [hwd]
  exact P3_B1W_run g s ctx.scriptContextTxInfo ctx.scriptContextRedeemer
    ctx.scriptContextScriptInfo w0 w1 a0 a1 (by rw [hctx]; exact h)

/-! ## §7 AXIOM AUDIT, printed at build time -/

#print axioms WSC.P3_B1W_prop
#print axioms WSC.P3_B1W_run
#print axioms WSC.exec_B1W
#print axioms WSC.ctxG_is_B1W
#print axioms WSC.K_B1W_two_sided
#print axioms WSC.b1W_realizable
#print axioms WSC.bwCtx_eta
#print axioms WSC.P3_base_requires_global_or_seize_run_W

end WSC
