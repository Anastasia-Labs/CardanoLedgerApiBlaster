/-
WSC/Props/P3_BaseIdx.lean — **P3 OVER THE UNSHAPED PREP, AT A LITERAL REDEEMER
INDEX** (task X2 / consolidation task).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS, AND WHAT IT IS NOT
════════════════════════════════════════════════════════════════════════════
This is a SECOND, INCOMPARABLE class family for P3, landed ALONGSIDE — never
instead of — SHAPE B1W (`WSC/Props/P3_BaseWdrl.lean`) and SHAPES B1RG/B1RS
(`WSC/Props/Shaped/P3ShapedR.lean`).

* SHAPE B1W freezes the WITHDRAWAL MAP in the prep and leaves the redeemer a
  free symbolic `Data`.
* This module freezes NOTHING in the prep — it runs against `WSC.appliedBase`,
  the UNSHAPED prep of the production `programmableLogicBase` at budget 600,
  the same term `WSC/Props/P3_Base.lean` measures `⚠️ Undetermined` over — and
  instead carries ONE HYPOTHESIS: the redeemer is a literal `Constr t [I i]`.
  The withdrawal map's LENGTH, every other `TxInfo` field, and both script
  parameters stay symbolic.

**NEITHER CLASS CONTAINS THE OTHER**, and that is the point of landing both.
The rungs below leave free all five dimensions `WSC.family_invariants` freezes
(signatories, reference inputs, validity range, certificates, datum witnesses),
which no shaped cut in this library does; SHAPE B1W covers every redeemer at a
fixed withdrawal length, which no rung below does.

**⚠ DO NOT READ THIS AS "P3 IS UNSHAPED AGAIN". IT IS NOT.**
The `Data`-SKELETON residual is TRADED for a REDEEMER-INDEX residual. That is a
real improvement — the index residual is ONE-DIMENSIONAL and expressible in
ledger vocabulary ("the base-spend redeemer names withdrawal index `i`"), versus
the 5-plus dimensions and 9.3 × 10⁹ skeletons of the shaped residual, priced at
971 CPU-years (`WSC/COVERAGE.md`) — but it is a residual, and the union of the
rungs is not all transactions. See `WSC/Coverage.lean` and the LIMITATIONS
document.

════════════════════════════════════════════════════════════════════════════
THE MEASURED LADDER, AND WHERE IT STOPS (task X2, serial re-measurement)
════════════════════════════════════════════════════════════════════════════
Against `WSC.appliedBase` @ 600, statement exactly as below:

| rung | verdict | wall | landed here? |
|---|---|---|---|
| `redIsG (-1)` | ✅ Valid | 1.9 s | yes (`P3_idx_gm1`) |
| `redIsG 0` | ✅ Valid | 1.6 s | yes |
| `redIsG 1` | ✅ Valid | 1.8 s | yes |
| `redIsG 2` | ✅ Valid | 1.8 s | yes |
| `redIsG 3` | ✅ Valid | 1.8 s | yes |
| `redIsG 5` | ✅ Valid | 1.8 s | yes |
| `redIsG 10` | ✅ Valid | 2.5 s | yes |
| `redIsG 15` | ✅ Valid | 223 s | yes — `WSC/Props/P3_BaseIdx15.lean` |
| `redIsG 20` | ⚠️ Undetermined | 602 s (cap 600) | **NO** — this is the wall |
| `redIsG 25` | ⚠️ Undetermined | 603 s | no |
| `redIsG 100` | ⚠️ Undetermined | 603 s | no |
| `redIsS 0` (seize arm) | ✅ Valid | 2.0 s | yes (`P3_idx_s0`) |
| `redIsAnyTagIdx0` (tag SYMBOLIC, index 0 — BOTH ARMS IN ONE THEOREM) | ✅ Valid | 1.8 s | yes (`P3_idx_T0`) |

**THE LADDER CANNOT BE COLLAPSED, and that is measured, not assumed.**
`0 ≤ i ≤ 2` with `i` SYMBOLIC is `⚠️ Undetermined` at 608 s, while i = 0, 1 and
2 each close INDIVIDUALLY in 1.8 s. So the win comes from `Optimize.main`
folding a LITERAL index into the term before Z3 sees it — not from the
constraint being satisfiable in only three ways. A hypothesis helps exactly
when it is an equation to a closed term the Lean-level optimizer can
substitute. That probe is deliberately NOT built here (it costs 600 s to
re-learn nothing); it is `WSC/ProbeX2/BR2.lean` in the task's workspace, and it
is the minimal reproducer for the one Blaster change that would convert this
family into a real result — Lean-level case splitting of a bounded symbolic
index.

**AND THERE IS NO BUDGET ARGUMENT THAT CLOSES IT.** `DropList` is a single
builtin in the base validator's builtin set (`WSC/goldens/K-MEASUREMENTS.md`
§7.1), so one application skips an arbitrary index in ~constant CEK steps. The
600-step budget therefore does NOT bound the redeemer index, and there is no
finite `N` after which "index > N ⟹ reject" is forced by the meter. The
complementary "malformed redeemer ⟹ reject" goal is Undetermined too, so even
the well-formedness half is unavailable.

════════════════════════════════════════════════════════════════════════════
WHY THIS IS STRONGER THAN `WSC/Props/P3_Base.lean`'s UNSHAPED STATEMENT
════════════════════════════════════════════════════════════════════════════
`P3_Base.lean`'s unshaped goal ASSUMES `validSpendingContext ctx`. The theorems
below deliberately DO NOT. That ledger predicate is itself a first-order solver
cost independent of the property: an unshaped vacuity probe WITHOUT it is
`✅ Expected Falsified` in 1.7 s and WITH it is `⚠️ Undetermined` at 304 s
(task X2 §6, reproducing the historical U3 result exactly). Dropping it makes
every theorem below both STRONGER and CHEAPER.

════════════════════════════════════════════════════════════════════════════
NON-VACUITY, AND THE FOUR-POINT BAR
════════════════════════════════════════════════════════════════════════════
§2 carries the mandatory vacuity probes. §3 carries the WITNESS-MEMBERSHIP
lemmas: the library's own certified accepting contexts (`WSC.P3Witness.ctx`,
`ctxS`) are INSIDE these classes, by kernel computation, so each rung inherits
the existing four-point-bar evidence — ledger validity (`ctx_valid`), Conway
redeemer-exactness, real-CEK acceptance with K = 194 pinned two-sided
(`P3Witness.K_two_sided`) — instead of needing new witnesses.
-/
import WSC.Prep.Base
import WSC.Props.P3_Base
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC.P3Idx

open CardanoLedgerApi.V3 (Credential ScriptContext credentialInWithdrawals)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §0 THE HYPOTHESIS VOCABULARY

Three `Bool`-valued predicates over a FULLY SYMBOLIC `ScriptContext`. None of
them is a shape: they are used against `WSC.appliedBase`, and they constrain
exactly one `Data` field of the context.

House rule: every predicate here is a pattern-match or a `==`, never
`List.all` / `List.any` / `List.find?` / a projection lambda — the measured
house rule is that the stdlib combinators produce cons-`Undetermined`. -/

/-- The redeemer is `SpendViaGlobal i` on the wire
(`ProgrammableLogicBase.hs`, `Constr 0 [I i]`).  Used with a **literal** `i`. -/
def redIsG (i : Integer) (ctx : ScriptContext) : Bool :=
  ctx.scriptContextRedeemer == Data.Constr 0 [Data.I i]

/-- The redeemer is `SpendViaSeize i` on the wire (`Constr 1 [I i]`). -/
def redIsS (i : Integer) (ctx : ScriptContext) : Bool :=
  ctx.scriptContextRedeemer == Data.Constr 1 [Data.I i]

/-- The redeemer names index 0 through EITHER arm — the constructor tag stays
SYMBOLIC.  This is the one hypothesis that covers both redeemer arms in a
single theorem. -/
def redIsAnyTagIdx0 (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextRedeemer with
  | Data.Constr _ [Data.I i] => i == 0
  | _ => false

/-! ## §1 THE THEOREMS

Statement, at every rung: ground-truth vocabulary only (`credentialInWithdrawals`
over `txInfoWdrl`), no validator-computed value in the conclusion, no
`validSpendingContext` hypothesis, both script parameters symbolic
`Credential`s with their constructor tags NOT frozen. -/

/-- **BOTH ARMS AT INDEX 0, IN ONE THEOREM.**  The redeemer's constructor tag is
SYMBOLIC; only the index is pinned.  Every `TxInfo` field — including the
withdrawal map's LENGTH — and both script parameters are symbolic. -/
theorem P3_idx_T0 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsAnyTagIdx0 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **THE SEIZE ARM AT INDEX 0.**  Subsumed by `P3_idx_T0`, kept because it is
the rung the seize-arm witness `P3Witness.ctxS` is pinned to in §3 and because
it is the arm-separated form the composition documents cite. -/
theorem P3_idx_s0 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsS 0 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG −1.**  Kept deliberately: the vacuity probe at this rung is
`✅ Expected Falsified` (§2), i.e. the base validator ACCEPTS a redeemer naming
index −1 and the postcondition still holds there.  See the FLAG in §4. -/
theorem P3_idx_gm1 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG (-1) ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 0, global arm.** -/
theorem P3_idx_g0 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 0 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 1.** -/
theorem P3_idx_g1 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 1 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 2.** -/
theorem P3_idx_g2 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 2 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 3.** -/
theorem P3_idx_g3 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 3 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 5.** -/
theorem P3_idx_g5 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 5 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-- **RUNG 10.** -/
theorem P3_idx_g10 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 10 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

/-! ## §2 THE MANDATORY VACUITY PROBES

`Falsified` = "an accepting context of this class exists inside budget 600" =
the corresponding theorem is NOT vacuous.  A `Valid` here would mean the class
is empty and the theorem says nothing.  Stated as `#blaster` COMMANDS with
`solve-result: 1` so the expected outcome is the green one. -/

/-- Vacuity at rung T0 (both arms, index 0).  Expected: Falsified. -/
def vac_T0 : Prop :=
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsAnyTagIdx0 ctx = true → ¬ isSuccessful (appliedBase.prop g s ctx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_T0]

/-- Vacuity at rung 0, global arm.  Expected: Falsified. -/
def vac_g0 : Prop :=
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 0 ctx = true → ¬ isSuccessful (appliedBase.prop g s ctx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_g0]

/-- Vacuity at rung 1 — so the ladder is non-vacuous at a rung the certified
witnesses do NOT inhabit, not only at rung 0.  Expected: Falsified. -/
def vac_g1 : Prop :=
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 1 ctx = true → ¬ isSuccessful (appliedBase.prop g s ctx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_g1]

/-- Vacuity at rung −1.  Expected: Falsified — see the FLAG in §4. -/
def vac_gm1 : Prop :=
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG (-1) ctx = true → ¬ isSuccessful (appliedBase.prop g s ctx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_gm1]

/-- Vacuity at the seize rung.  Expected: Falsified. -/
def vac_s0 : Prop :=
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsS 0 ctx = true → ¬ isSuccessful (appliedBase.prop g s ctx)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_s0]

/-! ## §3 WITNESS MEMBERSHIP — the four-point bar, inherited rather than redone

Kernel-level (`native_decide`), no solver.  `WSC.P3Witness.ctx` and `ctxS` are
the library's certified accepting contexts: ledger-valid (`P3Witness.ctx_valid`),
Conway-redeemer-exact, accepted by the real CEK machine with K = 194 pinned
two-sided (`P3Witness.K_two_sided`).  Showing they are INSIDE these classes is
what makes each rung's non-vacuity a statement about a transaction a node would
actually build, rather than only about the solver's model. -/

/-- The global-arm certified witness is in rung 0's class. -/
theorem ctxG_in_g0 : redIsG 0 P3Witness.ctx = true := by native_decide

/-- …and in T0's, so `P3_idx_T0` is non-vacuous with a REALIZABLE inhabitant. -/
theorem ctxG_in_T0 : redIsAnyTagIdx0 P3Witness.ctx = true := by native_decide

/-- The seize-arm certified witness is in the seize rung's class. -/
theorem ctxS_in_s0 : redIsS 0 P3Witness.ctxS = true := by native_decide

/-- …and in T0's — so `P3_idx_T0`'s single class contains inhabitants of BOTH
redeemer arms. -/
theorem ctxS_in_T0 : redIsAnyTagIdx0 P3Witness.ctxS = true := by native_decide

/-! ## §4 ONE THING FLAGGED, NOT CLAIMED

`vac_gm1` is `Falsified`, i.e. the base validator ACCEPTS a redeemer naming
index **−1**.  The postcondition still holds there (`P3_idx_gm1`), so no
property fails and nothing here is unsound.  But *"`pdropList` at a negative
index behaves like index 0 under PlutusCoreBlaster"* has **not** been checked
against `plutus-core`'s own `dropList` semantics.  If PCB and Plutus disagree on
a negative `dropList`, that is a SUBSTRATE-FIDELITY issue (it would belong with
audit D5/F8, the substrate pins), not a validator issue, and rung −1 would have
to be withdrawn while every rung ≥ 0 stood.  Recorded here so it is not
discovered by a reader instead of by us. -/

end WSC.P3Idx
