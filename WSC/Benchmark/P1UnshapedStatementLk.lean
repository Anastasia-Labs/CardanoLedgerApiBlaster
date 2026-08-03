/-
WSC/Benchmark/P1UnshapedStatementLk.lean — the P1 unshaped benchmark obligation
RESTATED IN THE `Lk` (translatable) VOCABULARY, plus the kernel equivalence to
the published form (2026-08-03).

⛔ NOT IMPORTED BY ANYTHING. Build deliberately:

    ( ulimit -v 8388608; timeout -s KILL 1800 \
        lake build WSC.Benchmark.P1UnshapedStatementLk )

════════════════════════════════════════════════════════════════════════════
WHY — BLOCKER-TRANSLATE
════════════════════════════════════════════════════════════════════════════
`WSC.Benchmark.P1UnshapedFormH` (WSC/Benchmark/P1UnshapedStatement.lean) ends in
`Model.Contained`, whose two sums (`Model.outSum` / `Model.inSum`,
WSC/Model/Ground.lean:45,:53) are built on CLAB's `valueOf`
(`CardanoLedgerApi/V1/Value.lean:85`). `valueOf` compares `Data` KEYS with
`==`, i.e. with the mutual-block `eqData`, and Blaster's translation phase dies
on it (`translateRecFun: … eqData`, WSC/BENCHMARK-PREP.md §6.4) on unshaped
goals. PCB's `lookupDataOuter` (PlutusCore/Value/Algebra.lean:1154)
destructures the key first, so no `eqData` application ever forms.

`WSC/Benchmark/P1LkVocab.lean` supplies the vocabulary: `Model.inSumLk`,
`Model.inSumLk_eq_inSum`, `Model.ContainedLk`, `Model.ContainedLk_iff_Contained`
(on top of `Model.outSumLk` / `Model.outSumLk_eq_outSum` and `Model.wfValue` in
WSC/Model/Ground.lean). This module does the last mile: it states the BENCHMARK
in that vocabulary and proves, in the kernel, that the two statements are the
same statement.

WHAT THIS BUYS. `P1UnshapedFormH_Lk_iff` is an `↔` between the two ∀-statements
for EVERY `accept`, with NO side hypothesis. So a future `✅ Valid` verdict on
`P1UnshapedFormH_Lk accept` — a goal Blaster can at least attempt to translate —
DISCHARGES the published `P1UnshapedFormH accept` on exactly the same class of
transactions, with no new trust: no new axiom, no new ledger assumption, no new
modelling step. The bridge is a Lean proof over CLAB's own ledger rules.

**EQUIVALENCE STRENGTH ACHIEVED: UNCONDITIONAL IFF.** The honesty rule in the
task brief anticipated that the inputs-side well-formedness might not follow
from `validRewardingContext`. It does. `CardanoLedgerApi.V3.validInputs`
(CardanoLedgerApi/V3/Contexts.lean:1644-1654) applies
`V2.validTxOutValue x.txInInfoResolved.txOutValue` to EVERY input, exactly as
`validInputs`' sibling `validOutputs` (:1696) applies it to every output, and
both are conjuncts of `validTxInfo` (:1821). §1 below derives both sides and
§0 turns `validTxOutValue` into `Model.wfValue`. Nothing is assumed and nothing
is conditional.

════════════════════════════════════════════════════════════════════════════
THE HYPOTHESIS LIST IS A VERBATIM COPY — HERE IS THE SOURCE
════════════════════════════════════════════════════════════════════════════
Past defects in this benchmark came from drift between hand-maintained copies
(see P1UnshapedStatement.lean's two CORRECTED DEFECT notes). So the source is
quoted here, character for character, from
`WSC/Benchmark/P1UnshapedStatement.lean` (`def P1UnshapedFormH`):

    def P1UnshapedFormH (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
      ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
        (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
        validRewardingContext ctx = true →
        Model.paramsPublishedBy ctx = some (dirCS, IsData.toData base) →
        Model.isProgrammable dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
        accept ppCS ctx →
          Model.Contained base cs tn ctx

§2's `P1UnshapedFormH_Lk` is that text with `Model.Contained` replaced by
`Model.ContainedLk` and NOTHING ELSE changed. In particular:

* the `cs ≠ ada` guard is NOT in this list and must not be added — in the LIVE
  forms it lives in the CONSEQUENT, inside `Model.exempt`, and reaches the
  hypothesis form through `Model.isProgrammable` (which is FALSE at ada:
  `Model.ne_ada_of_isProgrammable`). The guard is present, not missing;
* `validRewardingContext ctx = true` is the `= true` Bool form, not a coercion;
* `Model.paramsPublishedBy`, not `paramsPinned` — the indexed read the bytecode
  performs. The header of the source module explains why.

If the source ever changes, `P1UnshapedFormH_Lk_iff` STOPS TYPECHECKING, which
is the point of proving the `↔` rather than asserting the copy is faithful:
this module is the drift detector.

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE DOES NOT ESTABLISH
════════════════════════════════════════════════════════════════════════════
1. It does not prove P1. No prep, no solver, no accept predicate is named here;
   `accept` stays abstract exactly as in the source module.
2. It does not claim the `Lk` form TRANSLATES — that is a measurement, and it
   belongs to a prep-carrying probe, not to a kernel module. What is proved
   here is only that IF it translates and comes back Valid, the published form
   follows.
3. The `Lk` rewrite touches only the two SUMS. The mint term is
   `WSC.mintOf` in both forms (already match-based, no `eqData`), and the
   HYPOTHESES are untouched — if `Model.isProgrammable` or
   `Model.paramsPublishedBy` carry their own translation blockers, this module
   does not help with them.

MEASURED (2026-08-03, warm cache, 379 jobs, `ulimit -v 8388608`, log
`.lake/wsc-probe-logs/lkstmt.log`): ✅ BUILDS FIRST TRY. **746 ms** for this
module's own elaboration (`Built WSC.Benchmark.P1UnshapedStatementLk (746ms)`),
1.3 s wall for the whole `lake build` invocation, MaxRSS 1.2 GB — kernel-only,
three orders of magnitude cheaper than the ~5 GB / ~30 min-per-leaf shaped
destructure probes, which is the point of keeping the bridge in the kernel.
ZERO `sorry`.

    #print axioms P1UnshapedFormH_Lk_iff
      ⟹ [propext, Classical.choice, Quot.sound]

i.e. the Lean standard three and NOTHING ELSE — no `sorryAx`, and in particular
none of this repo's retracted fidelity axioms. `Classical.choice` enters through
the `simp` calls in the upstream `Lk` bridges (WSC/Model/Ground.lean §2) and the
`Bool` contradiction steps, not through any choice principle about
transactions.
-/
import WSC.Benchmark.P1UnshapedStatement
import WSC.Benchmark.P1LkVocab

namespace WSC
namespace Benchmark

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## §0 — CLAB's `validTxOutValue` implies `Model.wfValue`

`Model.wfValue` (WSC/Model/Ground.lean:80) is the SHAPE-only predicate the
`Lk`↔`valueOf` bridges need: every entry is `(Data.B _, Data.Map ts)` with every
entry of `ts` a `(Data.B _, Data.I _)`. `validTxOutValue`
(CardanoLedgerApi/V1/Contexts.lean:786-802) demands that shape AND the ordering
and positivity conditions, so it is strictly stronger. Ground.lean's docstring
promises this fact by the name `canonical_wf`; it was never written down. It is
written down here.

The two auxiliary `let rec`s of `validTxOutValue` are real constants
(`…validTxOutValue.validTokens` / `.validCurrencySymbol`), so each gets its own
induction. -/

/-- Token-map level: `validTokens` ⟹ `Model.wfTokens`. The ordering/positivity
conjuncts are dropped; only the `(B, I)` skeleton is retained. -/
theorem wfTokens_of_validTokens :
    ∀ (l : List (Data × Data)) (prev : ByteString),
      CardanoLedgerApi.V1.Contexts.validTxOutValue.validTokens l prev = true →
        Model.wfTokens l = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro prev h
      cases a <;> cases b <;>
        simp only [CardanoLedgerApi.V1.Contexts.validTxOutValue.validTokens] at h <;>
        first
          | exact Bool.noConfusion h
          | (simp only [Model.wfTokens]; exact ih _ (andEqTrueR h))

/-- Value level: `validCurrencySymbol` ⟹ `Model.wfValue`. -/
theorem wfValue_of_validCurrencySymbol :
    ∀ (v : CardanoLedgerApi.V1.Value) (prev : ByteString),
      CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol v prev = true →
        Model.wfValue v = true := by
  intro v
  induction v with
  | nil => intro _ _; rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro prev h
      match a, b, h with
      | Data.B cs, Data.Map ((Data.B tn, Data.I n) :: tokens), h =>
          simp only [CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol] at h
          simp only [Model.wfValue, Model.wfTokens]
          exact Bool.and_eq_true _ _ ▸
            ⟨wfTokens_of_validTokens tokens tn (andEqTrueR (andEqTrueL h)),
             ih _ (andEqTrueR h)⟩

/-- **THE MISSING `canonical_wf`.** Every ledger-valid `TxOut` value is
shape-well-formed, so the `Lk` sums agree with the `valueOf` sums on it. -/
theorem wfValue_of_validTxOutValue (v : CardanoLedgerApi.V1.Value)
    (h : CardanoLedgerApi.V2.validTxOutValue v = true) : Model.wfValue v = true := by
  unfold CardanoLedgerApi.V1.Contexts.validTxOutValue at h
  split at h
  · next n xs =>
      simp only [Model.wfValue, Model.wfTokens]
      exact Bool.and_eq_true _ _ ▸
        ⟨rfl, wfValue_of_validCurrencySymbol xs _ (andEqTrueR h)⟩
  · exact Bool.noConfusion h

/-! ## §1 — `validRewardingContext` gives `wfValue` on OUTPUTS and on INPUTS

The outputs half already exists: `outputs_ledger_valid_of_validRewardingContext`
(WSC/Benchmark/P1UnshapedStatement.lean §2.1) walks
`validRewardingContext ⟹ validScriptContext ⟹ validTxInfo ⟹ validOutputs ⟹
V2.validTxOutValue`. The inputs half is the mirror image through `validInputs`
(CardanoLedgerApi/V3/Contexts.lean:1644-1654) and is proved here, because the
task brief flagged it as the fact that might not exist. It does exist: the
ledger rule validates resolved input values exactly as it validates outputs.

The only structural difference is that `validInputs` is not a `Recursor.all` but
a hand-written `visit` carrying the previous `TxOutRef` (it also enforces
ordering), and that its EMPTY case is `false` — a transaction must have an
input. Both are handled below. -/

/-- Per-input extraction from `validInputs`' `visit` loop. -/
theorem validTxOutValue_of_mem_visit :
    ∀ (l : List TxInInfo) (p : CardanoLedgerApi.V3.TxOutRef),
      CardanoLedgerApi.V3.Contexts.validInputs.visit l p = true →
      ∀ x ∈ l, CardanoLedgerApi.V2.validTxOutValue x.txInInfoResolved.txOutValue = true := by
  intro l
  induction l with
  | nil => intro _ _ x hx; cases hx
  | cons y rest ih =>
      intro p h x hx
      simp only [CardanoLedgerApi.V3.Contexts.validInputs.visit] at h
      cases hx with
      | head => exact andEqTrueR (andEqTrueL h)
      | tail _ hm => exact ih _ (andEqTrueR h) x hm

/-- `validScriptContext` carries `validInputs` as a conjunct of `validTxInfo`.
Proved by contradiction on the `Bool`, exactly as the outputs twin, so a future
CLAB conjunct cannot silently shift the projection. -/
theorem validInputs_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    CardanoLedgerApi.V3.validInputs ctx = true := by
  have h := validScriptContext_of_validRewardingContext h
  cases hb : CardanoLedgerApi.V3.validInputs ctx with
  | true => rfl
  | false =>
      exfalso
      unfold CardanoLedgerApi.V3.validScriptContext CardanoLedgerApi.V3.validTxInfo at h
      rw [hb] at h
      simp at h

/-- **THE INPUTS-SIDE TWIN of `outputs_ledger_valid_of_validRewardingContext`.**
The ledger DOES normalise resolved input values the way it normalises outputs —
this is the fact the task brief allowed to be missing, and it is not. -/
theorem inputs_ledger_valid_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    ∀ i ∈ ctx.scriptContextTxInfo.txInfoInputs,
      CardanoLedgerApi.V2.validTxOutValue i.txInInfoResolved.txOutValue = true := by
  have hi := validInputs_of_validRewardingContext h
  unfold CardanoLedgerApi.V3.validInputs at hi
  split at hi
  · next heq => intro i hmem; rw [heq] at hmem; cases hmem
  · next y xs heq =>
      intro i hmem
      rw [heq] at hmem
      cases hmem with
      | head => exact andEqTrueL hi
      | tail _ hm => exact validTxOutValue_of_mem_visit xs _ (andEqTrueR hi) i hm

/-- `Model.wfValue` on every output of a ledger-valid context. -/
theorem wf_outputs_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    ∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, Model.wfValue o.txOutValue = true :=
  fun o ho => wfValue_of_validTxOutValue _ (outputs_ledger_valid_of_validRewardingContext h o ho)

/-- `Model.wfValue` on every resolved input value of a ledger-valid context. -/
theorem wf_inputs_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    ∀ i ∈ ctx.scriptContextTxInfo.txInfoInputs,
      Model.wfValue i.txInInfoResolved.txOutValue = true :=
  fun i hi => wfValue_of_validTxOutValue _ (inputs_ledger_valid_of_validRewardingContext h i hi)

/-- **THE CONTAINMENT BRIDGE, SPECIALISED TO THE BENCHMARK'S HYPOTHESIS.**
`Model.ContainedLk_iff_Contained` (WSC/Benchmark/P1LkVocab.lean) needs `wfValue`
on both sides; `validRewardingContext` supplies both. No other hypothesis of the
benchmark is used. -/
theorem ContainedLk_iff_Contained_of_validRewardingContext
    (base : Credential) (cs : CurrencySymbol) (tn : TokenName) {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    Model.ContainedLk base cs tn ctx ↔ Model.Contained base cs tn ctx :=
  Model.ContainedLk_iff_Contained base cs tn ctx
    (wf_outputs_of_validRewardingContext h) (wf_inputs_of_validRewardingContext h)

/-! ## §2 — THE STATEMENT, `Lk` FORM

Verbatim `P1UnshapedFormH` with `Model.Contained` → `Model.ContainedLk`. The
quoted source is in the module header; do not edit one without the other. -/

/-- **P1 — TRANSFER CONTAINMENT, UNSHAPED, HYPOTHESIS FORM, `Lk` VOCABULARY.**

Identical to `WSC.Benchmark.P1UnshapedFormH` in binders and hypotheses; the
conclusion is `Model.ContainedLk`, which computes the same two sums with PCB's
`lookupDataOuter` instead of CLAB's `valueOf` and therefore contains no
`eqData`. §3 proves the two statements are equivalent for every `accept`. -/
def P1UnshapedFormH_Lk (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx = true →
    Model.paramsPublishedBy ctx = some (dirCS, IsData.toData base) →
    Model.isProgrammable dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
    accept ppCS ctx →
      Model.ContainedLk base cs tn ctx

/-! ## §3 — THE EQUIVALENCE, IN THE KERNEL, UNCONDITIONALLY -/

/-- **THE TWO FORMS ARE THE SAME STATEMENT, FOR EVERY `accept`, WITH NO SIDE
CONDITION.** Each direction instantiates the other form at the same six binders
and rewrites the conclusion with §1's bridge, whose `wfValue` obligations are
discharged from the `validRewardingContext` hypothesis that is already in the
list. A `✅ Valid` on `P1UnshapedFormH_Lk` therefore discharges the published
`P1UnshapedFormH` on the same class, with no new trust.

KILL CRITERION: if this stops typechecking, either the published statement
drifted or the `Lk` vocabulary stopped matching it. Both are defects, and this
theorem is where they surface. -/
theorem P1UnshapedFormH_Lk_iff (accept : CurrencySymbol → ScriptContext → Prop) :
    P1UnshapedFormH_Lk accept ↔ P1UnshapedFormH accept := by
  constructor
  · intro H ppCS ctx base dirCS cs tn hv hp hprog hacc
    exact (ContainedLk_iff_Contained_of_validRewardingContext base cs tn hv).mp
      (H ppCS ctx base dirCS cs tn hv hp hprog hacc)
  · intro H ppCS ctx base dirCS cs tn hv hp hprog hacc
    exact (ContainedLk_iff_Contained_of_validRewardingContext base cs tn hv).mpr
      (H ppCS ctx base dirCS cs tn hv hp hprog hacc)

/-- The same bridge at the DISJUNCTIVE headline form, for free: the exemption
disjunct is untouched by the `Lk` rewrite. -/
def P1UnshapedFormD_Lk (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx = true →
    Model.paramsPublishedBy ctx = some (dirCS, IsData.toData base) →
    accept ppCS ctx →
      Model.ContainedLk base cs tn ctx
      ∨ Model.exempt dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = true

theorem P1UnshapedFormD_Lk_iff (accept : CurrencySymbol → ScriptContext → Prop) :
    P1UnshapedFormD_Lk accept ↔ P1UnshapedFormD accept := by
  constructor
  · intro H ppCS ctx base dirCS cs tn hv hp hacc
    rcases H ppCS ctx base dirCS cs tn hv hp hacc with hc | hex
    · exact Or.inl ((ContainedLk_iff_Contained_of_validRewardingContext base cs tn hv).mp hc)
    · exact Or.inr hex
  · intro H ppCS ctx base dirCS cs tn hv hp hacc
    rcases H ppCS ctx base dirCS cs tn hv hp hacc with hc | hex
    · exact Or.inl ((ContainedLk_iff_Contained_of_validRewardingContext base cs tn hv).mpr hc)
    · exact Or.inr hex

/-- Chained with `P1UnshapedForm_iff` (source module §2.0): the `Lk` hypothesis
form gives the published DISJUNCTIVE headline as well. -/
theorem P1UnshapedFormD_of_P1UnshapedFormH_Lk (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P1UnshapedFormH_Lk accept) : P1UnshapedFormD accept :=
  (P1UnshapedForm_iff accept).mpr ((P1UnshapedFormH_Lk_iff accept).mp H)

#print axioms P1UnshapedFormH_Lk_iff
#print axioms P1UnshapedFormD_of_P1UnshapedFormH_Lk

end Benchmark
end WSC
