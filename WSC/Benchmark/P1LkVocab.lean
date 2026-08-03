/-
WSC/Benchmark/P1LkVocab.lean — the `Lk` (translatable) vocabulary for P1's
containment conclusion (2026-08-02).

⛔ NOT IMPORTED BY ANYTHING YET. Build deliberately:

    lake build WSC.Benchmark.P1LkVocab

WHY THIS EXISTS — BLOCKER-TRANSLATE, root-caused. The unshaped P1 goal dies in
Blaster's translation phase with `translateRecFun: … eqData`
(WSC/BENCHMARK-PREP.md §6.4). The surviving `eqData` comes from CLAB's
`valueOf` (`CardanoLedgerApi/V1/Value.lean:85`) inside `Model.Contained`:
`if Data.B cs == r_cs …` compares `Data` KEYS of a symbolic Value map, and
`BEq Data` is the mutual-block `eqData` the translator cannot unfold. PCB's
`lookupDataOuter` (PlutusCore/Value/Algebra.lean:1154) destructures the key
FIRST (`(Data.B c, Data.Map ts) :: rest` then `c == cur` — ByteString
equality), so no `eqData` application ever forms. `WSC/Model/Ground.lean`
already ships `outSumLk` in that vocabulary plus the kernel bridge
`outSumLk_eq_outSum`; this module adds the missing input-side twin and the
`Contained`-level bridge, so an unshaped P1-class stanza can be STATED in a
vocabulary that translates and RELATED, in the kernel, to the published
`Model.Contained`.

Everything here is pure Lean (no solver, no prep): definitions + kernel
theorems. It lives in its own module rather than in WSC/Model/Ground.lean so
that the live build is not invalidated mid-campaign; folding it into Ground is
an editorial follow-up.
-/
import WSC.Model.Registry
import WSC.Model.Ground

namespace WSC.Model

open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName ScriptContext TxInInfo)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.Value (lookupDataOuter)

/-- Input-side twin of `outSumLk` (WSC/Model/Ground.lean §1): the amount of
`(cs, tn)` coming from inputs spent at the base credential, computed with
PCB's per-slot `Data` lookup instead of CLAB's `valueOf`. -/
def inSumLk (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if WSC.payCred i.txInInfoResolved == base then
         lookupDataOuter cs tn i.txInInfoResolved.txOutValue else 0)
      + inSumLk base cs tn rest

/-- The two input sums agree whenever every contributing input's value is
shape-well-formed — the exact mirror of `outSumLk_eq_outSum`. -/
theorem inSumLk_eq_inSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ ins : List TxInInfo,
      (∀ i ∈ ins, wfValue i.txInInfoResolved.txOutValue = true) →
      inSumLk base cs tn ins = inSum base cs tn ins := by
  intro ins
  induction ins with
  | nil => intro _; rfl
  | cons i rest ih =>
      intro h
      have hi : wfValue i.txInInfoResolved.txOutValue = true := h i (List.mem_cons_self)
      have hr : ∀ x ∈ rest, wfValue x.txInInfoResolved.txOutValue = true :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp [inSumLk, inSum, ih hr, lookupDataOuter_eq_valueOf cs tn _ hi]

/-- **THE CONTAINMENT OBLIGATION, `Lk` FORM.** Same inequality as
`Model.Contained` (WSC/Model/Registry.lean §4) with both sums in the
translatable vocabulary. The mint term is unchanged (`WSC.mintOf` is already
match-based). -/
def ContainedLk (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Prop :=
  outSumLk base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ inSumLk base cs tn ctx.scriptContextTxInfo.txInfoInputs
      + _root_.WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-- **KERNEL BRIDGE.** On shape-well-formed values — which
`validRewardingContext` supplies via `validTxOutValue` on every output and
resolved input — the `Lk` obligation IS the published obligation. A `✅ Valid`
on a `ContainedLk` conclusion therefore discharges `Model.Contained` on the
same class, with no new trust. -/
theorem ContainedLk_iff_Contained (base : Credential) (cs : CurrencySymbol)
    (tn : TokenName) (ctx : ScriptContext)
    (houts : ∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, wfValue o.txOutValue = true)
    (hins : ∀ i ∈ ctx.scriptContextTxInfo.txInfoInputs,
       wfValue i.txInInfoResolved.txOutValue = true) :
    ContainedLk base cs tn ctx ↔ Contained base cs tn ctx := by
  unfold ContainedLk Contained
  rw [outSumLk_eq_outSum base cs tn _ houts, inSumLk_eq_inSum base cs tn _ hins]

end WSC.Model
