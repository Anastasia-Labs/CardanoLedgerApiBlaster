/-
WSC/Goldens/Audit.lean — machine-checked backing for `WSC/LR-CTX-AUDIT.md`
(task Y4 RESULT A; ADDENDUM E5 axiom LR-CTX).

E5 posits: *for every real script invocation, the ledger-constructed
`ScriptContext` satisfies the matching `validXContext`.*  Every P-theorem takes
that predicate as its hypothesis, so if E5 were false for real transactions the
theorems would be partly vacuous in practice.  This module evaluates the
predicate on all 13 REAL goldens and records the outcome as theorems, so the
audit table in `WSC/LR-CTX-AUDIT.md` cannot drift from the code.

HEADLINE (stated loudly, per the task's instruction not to paper over a FALSE):
**all 13 goldens FAIL their matching `validXContext`.**  Every failure is
localised to a named conjunct below.  They fall into FIVE classes, and — this is
the part that matters — they do not all point the same way.

UPDATE (task Z1): class **D1 below is now FIXED IN CLAB** and no longer appears in
any golden's failing-conjunct list.  `ltScriptPurpose` was corrected to the
ledger's `ConwayPlutusPurpose` order (`CardanoLedgerApi/V3/Contexts.lean`, see its
docstring for the citations), and `ltCredential` to the ledger's
`ScriptHashObj < KeyHashObj` (D2, `CardanoLedgerApi/V1/Credential.lean`).  The two
accepting minting goldens' only remaining failure is the zero fee (A1).  The
D1 paragraph is kept below as the record of what was wrong and why; the
`fail_*` theorems and `order_violations_are_all_A2` state the post-fix truth.
The D2 fix changes no golden verdict — every golden withdrawal/rewarding
credential is a SCRIPT credential, the case where the old and new orders agree —
so the seize goldens' A2 failures are untouched, exactly as A2's attribution
predicted.

* **A1 `txInfoFee = 0`** — 13/13.  HARNESS artifact: a real Cardano transaction
  always pays a positive fee.
* **A2 two script credentials emitted DESCENDING** — 3/13 (the seize goldens),
  breaking `validWithdrawals` and also `validRedeemerMap` at a
  `(Rewarding script, Rewarding script)` pair.  HARNESS artifact: within script
  credentials CLAB's and `cardano-ledger`'s `Credential` orders agree
  (`WSC/STATUS.md` §3 D2), so the context really is mis-ordered.
* **A3 lovelace-free outputs** — 2/13 (the two accepting seize goldens' residual
  seized-token outputs).  HARNESS artifact: Cardano's min-UTxO-ada rule makes an
  output with no lovelace impossible.
* **D1 `validRedeemerMap` at a `(Spending, Minting)` pair** — was 2/13 (the two
  accepting minting goldens), **now 0/13: FIXED, see the UPDATE above.**  **NOT a
  harness artifact — it was a CLAB DEFECT.**  CLAB
  ordered `Minting < Spending` (`ltScriptPurpose`,
  `CardanoLedgerApi/V3/Contexts.lean`, the Plutus constructor order), but
  `cardano-ledger` emits `txInfoRedeemers` in `ConwayPlutusPurpose AsIx` order
  (`ConwaySpending < ConwayMinting < …`) and does NOT re-sort, so a real
  transaction carrying both a spending and a minting redeemer — i.e. **every**
  programmable-token mint — is not CLAB-sorted.  `validMintingContext` is
  therefore was unsatisfiable on P4's target class, making every
  `validMintingContext`-hypothesised theorem vacuous there.  This was found
  independently by task Y3 against the `cardano-ledger` sources, recorded as
  defect D1 in `WSC/STATUS.md` §3, and REPAIRED by task Z1.
  The goldens were ledger-CORRECT here; CLAB was what needed fixing.
* **T1/T2 tamper-intrinsic** — `isBalanced` on the two rejecting goldens that
  tamper by DELETING an output; `validScriptInfo` on the rejecting golden that
  grafts a spending purpose onto a minting transaction's `TxInfo`.

`order_violations_are_all_A2` below is what pins the cause of each remaining
order failure mechanically: it names the adjacent pair that breaks each order
check, and post-fix every such pair is inside ONE purpose kind (A2), never at a
purpose-KIND boundary (D1).

The counter-evidence that CLAB's predicate is not over-strong in its OTHER
clauses is `accepting_goldens_pass_modulo_artifacts` at the bottom: with A1/A3
relaxed and both order checks canonically re-sorted — and with **`isBalanced` and
every other conjunct still checked verbatim** — all 9 accepting goldens satisfy
the predicate.  Post-fix the re-sorting is a no-op on the minting goldens (they
were already in the ledger's order), so it no longer moves any context away from
reality; it now only repairs the genuinely mis-ordered seize contexts.

Every theorem is `native_decide`; kernel `decide` is unavailable because PCB's
CBOR decoder is `partial`.
-/
import WSC.Goldens.Decode

namespace WSC.Goldens.Audit

open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.Integer (Integer)

/-! ## Step 0 — the bridge itself is faithful

Before any verdict means anything, the decode must be lossless.  It is: all 13
`scriptContextHex` fields decode to a `ScriptContext` and RE-ENCODE to the
identical bytes through CLAB's `IsData ScriptContext` instance. -/

/-- All 13 goldens decode; all 13 round-trip byte-identically at the `Data`
level; all 13 round-trip byte-identically through the CLAB `ScriptContext` TYPE;
all 13 redeemer and all 19 params hexes round-trip; and each golden's
separately-exposed `redeemerHex` really is its context's redeemer field. -/
theorem bridge_is_faithful :
    allContextsDecode = true ∧
    allContextsRoundTrip = true ∧
    allCtxTypeRoundTrip = true ∧
    allRedeemersRoundTrip = true ∧
    allParamsRoundTrip = true ∧
    allRedeemersMatchContexts = true := by
  native_decide

/-! ## Step 1 — RESULT A, the verdicts

`auditVerdict v = some false` reads: decoded successfully, matching
`validXContext` is FALSE.  `failingConjuncts v` names exactly which clauses of
`validScriptContext` fail, in source order. -/

/-- **The headline: not one of the 13 real golden contexts satisfies the
precondition our theorems assume.** -/
theorem all_goldens_fail_the_precondition : allContextsValid = false := by
  native_decide

/-- Stronger and per-golden: every one of the 13 is `some false` (decoded, and
the predicate is false) — not a single `none` (decode failure) and not a single
`some true`. -/
theorem every_verdict_is_false :
    all.all (fun v => auditVerdict v == some false) = true := by
  native_decide

/-! ### The exact failing conjuncts, golden by golden

These are the "walk the predicate's components" details the task demands for a
FALSE verdict.  Sub-conjunct names prefixed `scriptInfo.` are the two halves of
`validScriptInfo` (`CardanoLedgerApi/V3/Contexts.lean:1001-1002`). -/

/-- `programmableLogicBase.base-spend-transfer-tx` (ACCEPTING) — the single
failing conjunct is the zero fee. -/
theorem fail_base_spend_transfer_tx :
    failingConjuncts programmableLogicBase_base_spend_transfer_tx
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT`
(rejecting) — besides the fee, `validScriptInfo` fails in BOTH halves: this
golden grafts a `SpendingScript` purpose onto the minting transaction's `TxInfo`
(`sourceTest`), so (i) there is no `Spending` entry in `txInfoRedeemers` to match
and (ii) the claimed own-input `TxOutRef` is not among `txInfoInputs`.  NOTE for
the negative-control story: this rejecting golden is therefore not a well-formed
ledger context at all, so it exercises the bytecode's reject path but cannot be
used as a `validSpendingContext`-carrying counterexample. -/
theorem fail_base_spend_no_global_or_seize_invoked_REJECT :
    failingConjuncts programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT
      = some ["validScriptInfo", "scriptInfo.redeemerConsistent",
              "scriptInfo.purposeWellFormed", "txInfoFee > 0"] := by
  native_decide

/-- `programmableTokenMinting.mint-local-registered-by-ref` (ACCEPTING). -/
theorem fail_mint_local_registered_by_ref :
    failingConjuncts programmableTokenMinting_mint_local_registered_by_ref
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableTokenMinting.mint-local-empty-withdrawals-REJECT` (rejecting):
its tamper (`txInfoWdrl := []`) does NOT break well-formedness, so like the
accepting goldens only the fee fails. -/
theorem fail_mint_local_empty_withdrawals_REJECT :
    failingConjuncts programmableTokenMinting_mint_local_empty_withdrawals_REJECT
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableTokenMinting.mint-burnonly` (ACCEPTING) — the fee (A1) is now the
ONLY failing conjunct.  Before the D1 fix this golden also failed
`validRedeemerMap` at its `(Spending, Minting)` pair; its redeemer order was the
ledger's all along and CLAB's order was wrong (task Z1). -/
theorem fail_mint_burnonly :
    failingConjuncts programmableTokenMinting_mint_burnonly
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableTokenMinting.mint-delegate-transfer-topup` (ACCEPTING) — likewise
fee-only since the D1 fix. -/
theorem fail_mint_delegate_transfer_topup :
    failingConjuncts programmableTokenMinting_mint_delegate_transfer_topup
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableSeize.seize-1-input` (ACCEPTING) — the worst case: lovelace-free
residual output (A3), zero fee (A1), and the descending script-credential pair
breaking BOTH `validWithdrawals` and `validRedeemerMap` (A2 — note this is A2, not
D1: the violating redeemer pair is `(Rewarding script, Rewarding script)`, inside
one purpose kind, where CLAB and the ledger agree).  All harness artifacts;
`isBalanced`, `validInputs`, `validReferenceInputs` and `validScriptInfo` all
HOLD. -/
theorem fail_seize_1_input :
    failingConjuncts programmableSeize_seize_1_input
      = some ["validOutputs", "txInfoFee > 0", "validWithdrawals",
              "validRedeemerMap"] := by
  native_decide

/-- `programmableSeize.seize-2-inputs-partial-with-noise` (ACCEPTING) — same four
clauses, same three causes. -/
theorem fail_seize_2_inputs_partial_with_noise :
    failingConjuncts programmableSeize_seize_2_inputs_partial_with_noise
      = some ["validOutputs", "txInfoFee > 0", "validWithdrawals",
              "validRedeemerMap"] := by
  native_decide

/-- `programmableSeize.seize-1-input-missing-residual-output-REJECT` (rejecting)
— the tamper DELETES the residual output, so `isBalanced` genuinely fails (and,
the deleted output being the lovelace-free one, `validOutputs` now passes). -/
theorem fail_seize_1_input_missing_residual_output_REJECT :
    failingConjuncts programmableSeize_seize_1_input_missing_residual_output_REJECT
      = some ["txInfoFee > 0", "validWithdrawals", "validRedeemerMap",
              "isBalanced"] := by
  native_decide

/-- `programmableLogicGlobal.transfer-member-single-policy` (ACCEPTING). -/
theorem fail_transfer_member_single_policy :
    failingConjuncts programmableLogicGlobal_transfer_member_single_policy
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableLogicGlobal.transfer-nonmember-covering-node` (ACCEPTING) —
the cheapest accepting global run (K = 1,554) and P5's subject shape. -/
theorem fail_transfer_nonmember_covering_node :
    failingConjuncts programmableLogicGlobal_transfer_nonmember_covering_node
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableLogicGlobal.transfer-mixed-many-policies` (ACCEPTING). -/
theorem fail_transfer_mixed_many_policies :
    failingConjuncts programmableLogicGlobal_transfer_mixed_many_policies
      = some ["txInfoFee > 0"] := by
  native_decide

/-- `programmableLogicGlobal.transfer-containment-violation-REJECT` (rejecting)
— the tamper deletes a base output holding 3 of 5 programmable tokens, so
`isBalanced` genuinely fails. -/
theorem fail_transfer_containment_violation_REJECT :
    failingConjuncts programmableLogicGlobal_transfer_containment_violation_REJECT
      = some ["txInfoFee > 0", "isBalanced"] := by
  native_decide

/-! ## Step 2 — root causes, pinned as facts

Each artifact class is asserted directly, so the audit narrative is checked and
not merely asserted in prose. -/

def feeOf (v : Vector) : Option Integer :=
  (ctxOfHex v.scriptContextHex).map fun c => c.scriptContextTxInfo.txInfoFee

/-- **A1.** Every one of the 13 goldens has `txInfoFee = 0`.  This is the single
universal obstruction, and the reason the 9 accepting goldens cannot be
substituted into a `validXContext`-carrying theorem as-is. -/
theorem A1_every_golden_has_zero_fee :
    all.all (fun v => feeOf v == some 0) = true := by
  native_decide

/-- Number of outputs carrying no lovelace entry. -/
def lovelaceFreeOutputs (v : Vector) : Option Nat :=
  (ctxOfHex v.scriptContextHex).map fun c =>
    (c.scriptContextTxInfo.txInfoOutputs.filter
      (fun o => !hasAdaEntry o.txOutValue)).length

/-- **A3.** Exactly the two accepting seize goldens carry a lovelace-free output
(the residual seized-token UTxO); every other golden has none. -/
theorem A3_only_seize_has_lovelace_free_outputs :
    all.all (fun v =>
      lovelaceFreeOutputs v ==
        some (if v.scenario == "seize-1-input"
                 || v.scenario == "seize-2-inputs-partial-with-noise"
              then 1 else 0)) = true := by
  native_decide

/-- **A2 is a pure ORDER failure.** Canonically re-sorting the withdrawal map and
the redeemer map — a permutation that touches no value — makes both clauses hold
in every golden.  Post-Z1 this re-sort is a NO-OP on the two minting goldens
(their redeemer maps are already in CLAB's = the ledger's order), so it is now
only doing work on the mis-ordered seize contexts. -/
theorem order_failures_are_order_only :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          let c := canonicaliseOrder ctx
          CardanoLedgerApi.V3.Contexts.validWithdrawals
            c.scriptContextTxInfo.txInfoWdrl
          && CardanoLedgerApi.V3.Contexts.validRedeemerMap
               c.scriptContextTxInfo.txInfoRedeemers) = true := by
  native_decide

/-- **A2 is now the ONLY order cause (D1 is fixed).** For each golden, the
adjacent pair that breaks `validRedeemerMap` (`none` = the check passes):

* the three SEIZE goldens break at
  `("Rewarding(script)", "Rewarding(script)")` — inside one kind, where CLAB and
  the ledger agree, i.e. harness artifact **A2**;
* **all ten others are sorted**, including the two accepting MINTING goldens,
  which before task Z1's fix broke at `("Spending", "Minting")` — a purpose-KIND
  boundary where CLAB's order, not the transaction, was wrong (defect D1).  That
  `none` is the machine-checked payoff of the fix: no purpose-KIND violation
  survives anywhere in the suite.

The withdrawal-map violations are all `("script", "script")`, confirming A2's
attribution there too — and they are unchanged by the D2 fix precisely because
both credentials are script credentials, the case where the old and new orders
agree. -/
theorem order_violations_are_all_A2 :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          (firstRedeemerOrderViolation ctx ==
            (if v.validator == "programmableSeize"
             then some ("Rewarding(script)", "Rewarding(script)")
             else none))
          && (firstWithdrawalOrderViolation ctx ==
                (if v.validator == "programmableSeize"
                 then some ("script", "script") else none))) = true := by
  native_decide

/-- No golden's redeemer map has a violation at a purpose-KIND boundary any more:
every surviving violation is `Rewarding`-vs-`Rewarding`.  This is the sharpest
statement of "D1 is gone from the suite". -/
theorem no_purpose_kind_order_violation_remains :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          match firstRedeemerOrderViolation ctx with
          | none => true
          | some (a, b) => a == b) = true := by
  native_decide

/-! ## Step 3 — the interpretation, machine-checked

The task's reading of an all-TRUE result would have been "the preconditions are
not over-strong".  We got all-FALSE, so the honest question becomes: *is any
failure evidence that CLAB's predicate excludes a REAL ledger transaction?*  The
theorem below answers no, as sharply as this golden suite permits: once the four
harness artifacts are accounted for — and with `isBalanced` and every other
conjunct still checked verbatim — all 9 accepting goldens satisfy the predicate.

What remains unresolved, and is stated as such in `WSC/LR-CTX-AUDIT.md`: these
contexts are harness-built, so this is evidence about a ledger-SHAPED context
generator, not about the Cardano ledger's own `ScriptContext` construction.
Only contexts captured from a running node (or from `cardano-ledger`'s own
`ScriptContext` builder) can settle E5 outright. -/

/-- **The decisive result.** All 9 ACCEPTING goldens satisfy their matching
`validXContext` modulo the four named harness artifacts (A1 fee dropped, A3
min-ada relaxed, A2/A2′ canonically re-sorted; `isBalanced` and everything else
checked verbatim). -/
theorem accepting_goldens_pass_modulo_artifacts :
    acceptingContextsValidRelaxed = true := by
  native_decide

/-- Per-golden form, including the rejecting ones.  Three of the four rejecting
goldens still fail — correctly: two delete an output (breaking `isBalanced`) and
one grafts a spending purpose onto a minting `TxInfo`.  The fourth
(`mint-local-empty-withdrawals-REJECT`) passes, i.e. it IS a well-formed ledger
context that the bytecode rejects — making it the suite's only clean negative
control. -/
theorem relaxed_verdicts :
    all.all (fun v =>
      relaxedVerdict v ==
        some (v.accepts || v.scenario == "mint-local-empty-withdrawals-REJECT"))
      = true := by
  native_decide

end WSC.Goldens.Audit
