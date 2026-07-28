-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Model/GlobalGoldens.lean — DIFFERENTIAL TEST of `WSC/Model/GlobalModel.lean`
against the real compiled `programmableLogicGlobal` bytecode (task Z4 step 2).

WHAT THIS ESTABLISHES.  The model of §11 of `WSC/Model/GlobalModel.lean` is a
hand transcription; the only way to know the transcription is right is to run it
on transactions whose bytecode verdict was measured independently.  The four
global goldens are exactly that: their accept/reject verdicts come from executing
the ACTUAL production-exported `programmableLogicGlobal` script (byte-identical to
`WSC/flats/programmableLogicGlobal.flat`, sha256 in `WSC/flats/PROVENANCE.md`) at
PV11 through `PlutusLedgerApi.V3.evaluateScriptCounting` — see
`WSC/goldens/MANIFEST.md` "Verification method (per golden)".  Nothing in this
file is a Lean re-derivation of that verdict; it is the Haskell/ledger evaluator's
answer, transported as the `accepts` field of `WSC/Goldens/Vectors.lean`.

The highest-value vector is the REJECTING one,
`programmableLogicGlobal.transfer-containment-violation-REJECT`: a genuine
containment violation (the accepting `globalTransferCtx` with the recipient base
output carrying 3 programmable tokens deleted, so `outAtBase = 2 < 5 = inAtBase`).
If the model's containment logic were transcribed too weakly it would accept that
context and the theorem `model_matches_bytecode_containment_violation` below
would fail to compile.

EVALUATION STRATEGY.  `native_decide`, for the reasons given in
`WSC/Goldens/Decode.lean`: the golden→`Data` step goes through PlutusCoreBlaster's
`partial def` CBOR decoder, which the kernel cannot unfold.

SCOPE NOTE (honest).  The goldens are run AS THEY ARE.  They are
benchmark-harness-built, not chain-captured, so they carry the four artifacts
catalogued in `WSC/LR-CTX-AUDIT.md` / `WSC/STATUS.md` §3 D3 (`txInfoFee = 0`
above all).  That is a statement about CLAB's `validRewardingContext`, not about
the bytecode: the real script accepted/rejected these contexts anyway, which is
precisely what makes them usable as a differential oracle for the model.
-/
import WSC.Model.GlobalModel
import WSC.Goldens.Decode

namespace WSC.Model.Goldens

open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol)
open PlutusCore.ByteString (ByteString)

/-! ## Running the model on a golden -/

/-- The single script parameter of `programmableLogicGlobal` is
`PAsData PCurrencySymbol` = the protocol-params NFT policy
(`ProgrammableLogicBase.hs:1176`); it is `paramsHex[0]` of each global golden. -/
def ppCSOf (v : WSC.Goldens.Vector) : Option CurrencySymbol :=
  match v.paramsHex with
  | [h] => WSC.Goldens.byteStringOfHex h
  | _ => none

/-- The model's verdict on a golden: `none` when the golden's parameter or
context does not decode (a build-visible failure, never a silent `false`). -/
def modelVerdict (v : WSC.Goldens.Vector) : Option Bool :=
  match ppCSOf v, WSC.Goldens.ctxOfHex v.scriptContextHex with
  | some ppCS, some ctx => some (WSC.Model.globalModel ppCS ctx)
  | _, _ => none

/-- The differential predicate for ONE golden: the model's verdict is defined and
equals the verdict the real bytecode produced. -/
def agrees (v : WSC.Goldens.Vector) : Bool := modelVerdict v == some v.accepts

/-! ## The four global goldens -/

def globals : List WSC.Goldens.Vector :=
  [ WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy
  , WSC.Goldens.programmableLogicGlobal_transfer_nonmember_covering_node
  , WSC.Goldens.programmableLogicGlobal_transfer_mixed_many_policies
  , WSC.Goldens.programmableLogicGlobal_transfer_containment_violation_REJECT
  ]

/-- Sanity gate: these really are the four `programmableLogicGlobal` goldens of
the suite, and no other (guards against the list above drifting away from
`WSC/Goldens/Vectors.lean`). -/
theorem globals_is_the_global_suite :
    (WSC.Goldens.all.filter (fun v => v.validator == "programmableLogicGlobal")).map
        (fun v => v.scenario)
      = ["transfer-containment-violation-REJECT", "transfer-member-single-policy",
         "transfer-mixed-many-policies", "transfer-nonmember-covering-node"] := by
  native_decide

theorem globals_covers_all :
    (globals.map (fun v => v.scenario)).length = 4 ∧
    globals.all (fun v => v.validator == "programmableLogicGlobal") = true := by
  native_decide

/-! ## Per-golden results (ADDENDUM E9 / task Z4 step 2: report per golden) -/

/-- **ACCEPTING 1 / 3 — `transfer-member-single-policy`.**  The catalogue's
`globalTransferCtx` with redeemer `TransferAct [1] [1] [] 0`: one registered
policy, one positive directory proof, one transfer-logic withdrawal index, no
mint.  Measured bytecode verdict: ACCEPT (ExBudget cpu 62,665,145 / mem 177,810);
K = 3,262 CEK steps (`WSC/goldens/K-MEASUREMENTS.md`).  This vector exercises the
single-asset dispatch path (Path A) of `poutputsContainExpectedValueAtCred`. -/
theorem model_matches_bytecode_member_single_policy :
    modelVerdict WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy
      = some true := by
  native_decide

/-- **ACCEPTING 2 / 3 — `transfer-nonmember-covering-node`.**  The catalogue's
`globalTransferDoesNotExistCtx`: the transferred policy is NOT registered and is
exempted by a covering directory node (`key < cs < next`), the negative-proof
branch of the transfer walk (:891-908).  Measured bytecode verdict: ACCEPT;
K = 1,554 — the cheapest accepting global run in the suite, and the vector P5 is
stated against. -/
theorem model_matches_bytecode_nonmember_covering_node :
    modelVerdict WSC.Goldens.programmableLogicGlobal_transfer_nonmember_covering_node
      = some true := by
  native_decide

/-- **ACCEPTING 3 / 3 — `transfer-mixed-many-policies`.**  The catalogue's
`globalTransferMixedManyCtx`: several policies, a mix of positive and negative
proofs.  Measured bytecode verdict: ACCEPT; K = 3,726 — the most expensive
accepting global run.  This is the vector that exercises the MULTI-asset dispatch
(Paths B/C) and the cons-then-`preverseCurrencyPairs` accumulator order (:935). -/
theorem model_matches_bytecode_mixed_many_policies :
    modelVerdict WSC.Goldens.programmableLogicGlobal_transfer_mixed_many_policies
      = some true := by
  native_decide

/-- **REJECTING 1 / 1 — `transfer-containment-violation-REJECT`** (the
highest-value check).  `globalTransferCtx` with base output #1 — the recipient,
holding 3 programmable tokens — REMOVED, so `outAtBase = 2 < 5 = inAtBase`:
a genuine violation of exactly the property P1 asserts.  Measured bytecode
verdict: REJECT.  The model rejects it too, so the model's containment check is
not vacuously permissive. -/
theorem model_matches_bytecode_containment_violation :
    modelVerdict WSC.Goldens.programmableLogicGlobal_transfer_containment_violation_REJECT
      = some false := by
  native_decide

/-- **AGGREGATE (4/4).**  The model's verdict equals the real bytecode's verdict
on every global golden — 3 accepting and 1 rejecting.  This is the empirical
evidence cited in the docstring of the `globalModel_faithful` axiom
(`WSC/Props/P1_Transfer.lean`). -/
theorem model_agrees_with_bytecode_on_all_global_goldens :
    globals.all agrees = true := by
  native_decide

/-! ## Model-level positive witness (ARCHITECTURE.md Tier 0.2)

The accepting goldens double as the model's non-vacuity witnesses: the model does
accept something, so `globalModel … = true → POST` theorems are not vacuous. -/

/-- Extract a golden's decoded context (total on the four globals; `none` is
impossible there and would be a build failure via the theorems above). -/
def ctxOf (v : WSC.Goldens.Vector) : Option ScriptContext :=
  WSC.Goldens.ctxOfHex v.scriptContextHex

/-- Non-vacuity: at least one context the model ACCEPTS exists, and it is a real
off-chain-produced golden, not a hand-built one. -/
theorem model_is_non_vacuous :
    ∃ (ppCS : CurrencySymbol) (ctx : ScriptContext),
      ppCSOf WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy = some ppCS ∧
      ctxOf WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy = some ctx ∧
      WSC.Model.globalModel ppCS ctx = true := by
  have h : modelVerdict WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy
             = some true := model_matches_bytecode_member_single_policy
  have hp : (ppCSOf WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy).isSome
              = true := by native_decide
  have hc : (ctxOf WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy).isSome
              = true := by native_decide
  obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hc
  refine ⟨p, c, hp', hc', ?_⟩
  simp only [modelVerdict, hp'] at h
  simp only [ctxOf] at hc'
  simp only [hc', Option.some.injEq] at h
  exact h

end WSC.Model.Goldens
