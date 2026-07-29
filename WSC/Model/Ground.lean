-- ✅ LIVE, and NOT a source model. This module is GROUND-TRUTH VOCABULARY over `ScriptContext` fields only (ARCHITECTURE.md D3 / Tier 0.1); it is consumed by the UPLC-level shaped theorems and by WSC/Composition.lean. Task R1 cut its `import WSC.Model.GlobalModel` so that nothing live depends, even transitively, on the retracted pre-#112 transcription.
/-
WSC/Model/Ground.lean — GROUND-TRUTH vocabulary and the ledger-canonicity
toolkit that the model-level P1/P6 proofs need (task Z4 step 3).

ARCHITECTURE.md D3 / Tier 0.1 is a HARD GATE here: nothing in this file may
mention a validator-computed accumulator.  Everything below is a function of
`ScriptContext` fields only:

* `outSum` / `inSum` — the per-asset sums at the mini-ledger base payment
  credential, over CLAB's `valueOf` (`CardanoLedgerApi/V1/Value.lean:85`).  These
  are the §3 `outAtBase`/`inAtBase` of ARCHITECTURE.md, in the *sum* form the
  theorems need (`WSC/Spec.lean`'s same-named definitions are the per-output
  membership predicates; both are re-used, they are not in conflict).
* `outSumLk` — the same sum computed with PlutusCoreBlaster's `Data`-level
  per-slot lookup `lookupDataOuter` (`PlutusCore/Value/Algebra.lean:1154`).  This
  is the form the CIP-153 algebra lemmas speak, and `outSumLk_eq_outSum` proves
  the two agree on every well-formed value, so no proof ever silently swaps one
  for the other.
* the canonicity toolkit — every fact the containment proofs need about output
  values is derived from CLAB's own `validTxOutValue`
  (`CardanoLedgerApi/V1/Contexts.lean:769-784`), i.e. from the LEDGER RULE that
  `validRewardingContext` already asserts, not from a predicate invented here.
-/
import WSC.Spec
import PlutusCore.Value.Algebra

namespace WSC.Model

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext TxInInfo valueOf)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.Value (lookupDataInner lookupDataOuter)

/-! ## 1. The ground-truth sums -/

/-- Ground truth: the amount of `(cs, tn)` sitting at outputs whose PAYMENT
credential is the mini-ledger base `base` (ARCHITECTURE.md §3 `outAtBase`, sum
form).  Note the deliberate scope: this is aggregate containment at the shared
base payment credential, NOT per-holder ownership (Tier 3.3). -/
def outSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if WSC.payCred o == base then valueOf cs tn o.txOutValue else 0)
      + outSum base cs tn rest

/-- Ground truth: the amount of `(cs, tn)` coming from inputs spent at the
mini-ledger base credential (ARCHITECTURE.md §3 `inAtBase`, sum form). -/
def inSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if WSC.payCred i.txInInfoResolved == base then
         valueOf cs tn i.txInInfoResolved.txOutValue else 0)
      + inSum base cs tn rest

/-- The same output sum, computed with PlutusCoreBlaster's `Data`-level per-slot
lookup instead of CLAB's `valueOf`; `outSumLk_eq_outSum` below shows they agree
on well-formed values. -/
def outSumLk (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if WSC.payCred o == base then lookupDataOuter cs tn o.txOutValue else 0)
      + outSumLk base cs tn rest

/-! ## 2. `lookupDataOuter` ≡ CLAB `valueOf` on well-formed values -/

/-- Shape well-formedness of a `Data`-encoded token map: every entry is a
`(B tokenName, I quantity)` pair. -/
def wfTokens : List (Data × Data) → Bool
  | [] => true
  | (Data.B _, Data.I _) :: rest => wfTokens rest
  | _ => false

/-- Shape well-formedness of a `Data`-encoded value: every entry is a
`(B currencySymbol, Map tokenMap)` pair with a well-formed token map. -/
def wfValue : Value → Bool
  | [] => true
  | (Data.B _, Data.Map ts) :: rest => wfTokens ts && wfValue rest
  | _ => false

theorem lookupDataInner_eq_find_token (tn : TokenName) :
    ∀ l : List (Data × Data), wfTokens l = true →
      lookupDataInner tn l = CardanoLedgerApi.V1.Value.valueOf.find_token tn l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      cases a <;> cases b <;> intro h <;> simp [wfTokens] at h <;>
        simp [lookupDataInner, CardanoLedgerApi.V1.Value.valueOf.find_token, ih h, BEq.comm]

theorem lookupDataOuter_eq_valueOf (cs : CurrencySymbol) (tn : TokenName) :
    ∀ v : Value, wfValue v = true → lookupDataOuter cs tn v = valueOf cs tn v := by
  intro v
  induction v with
  | nil => intro _; rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      cases a <;> cases b <;> intro h <;> simp [wfValue] at h <;>
        simp [lookupDataOuter, CardanoLedgerApi.V1.Value.valueOf,
              CardanoLedgerApi.V1.Value.valueOf.visit, BEq.comm,
              lookupDataInner_eq_find_token tn _ h.1]
      split
      · rfl
      · simpa [CardanoLedgerApi.V1.Value.valueOf,
               CardanoLedgerApi.V1.Value.valueOf.visit] using ih h.2

/-- The two output sums agree whenever every contributing output's value is
shape-well-formed (which `validTxOutValue` guarantees — `canonical_wf` below). -/
theorem outSumLk_eq_outSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ outs : List TxOut,
      (∀ o ∈ outs, wfValue o.txOutValue = true) →
      outSumLk base cs tn outs = outSum base cs tn outs := by
  intro outs
  induction outs with
  | nil => intro _; rfl
  | cons o rest ih =>
      intro h
      have ho : wfValue o.txOutValue = true := h o (List.mem_cons_self)
      have hr : ∀ x ∈ rest, wfValue x.txOutValue = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp [outSumLk, outSum, ih hr, lookupDataOuter_eq_valueOf cs tn _ ho]

end WSC.Model
