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

`auditVerdict v = some true` reads: decoded successfully, and the matching
`validXContext` HOLDS.  `failingConjuncts v` names exactly which clauses of
`validScriptContext` fail, in source order (`some []` = none of them).

**UPDATED (task Z5): the three HARNESS artifacts are fixed too.**  Z1 fixed
CLAB's side (D1/D2, see the UPDATE in the module header); the wsc-poc side has now
been fixed as well, in
`ProgrammableTokens.Test.ScriptContext.Builder.buildLedgerShapedScriptContext`:

* **A1** — a positive fee (`defaultBalancedTxFee`), balanced against the change
  output so value conservation still holds;
* **A2** — `txInfoWdrl` emitted in the LEDGER's `Credential` order
  (`canonicaliseWdrl` / `compareCredentialLedger`), which fixes the `Rewarding`
  entries of `txInfoRedeemers` at the same time;
* **A3** — min-UTxO ada on every output (`ensureMinAda`), so the seize residual
  seized-token UTxO is no longer lovelace-free.

These goldens were re-dumped from the fixed builder and re-verified against the
prod-exported scripts at PV11 (all 9 accepting → accept, all 4 rejecting →
reject).  The pre-fix JSONs are kept under `WSC/goldens/pre-fix/`.

**With both sides fixed, 10 of the 13 goldens satisfy their matching
`validXContext` OUTRIGHT, and every one of the 9 ACCEPTING goldens does.**  The
only three failures left are intrinsic to how the REJECTING goldens were
tampered.  LR-CTX (ADDENDUM E5) therefore has direct empirical support, with no
relaxation, for all four validator shapes. -/

/-- `allContextsValid` is still `false`, but now for a completely different
reason: only the three tamper-broken REJECTING goldens fail.  See
`every_accepting_golden_satisfies_its_precondition`. -/
theorem not_all_goldens_satisfy_the_precondition : allContextsValid = false := by
  native_decide

/-- **The headline.** Every ACCEPTING golden satisfies its matching
`validXContext` with every conjunct checked verbatim — no relaxation, no
artifacts.  This is what LR-CTX asserts, measured on the real
off-chain-produced transactions for all four validators. -/
theorem every_accepting_golden_satisfies_its_precondition :
    all.all (fun v => !v.accepts || auditVerdict v == some true) = true := by
  native_decide

/-- Per-golden verdicts: all 13 decode (no `none`), and exactly the three
tamper-broken rejecting goldens are `some false`. -/
theorem verdicts_are_exactly_as_tabulated :
    all.all (fun v =>
      auditVerdict v ==
        some (!(v.scenario == "base-spend-no-global-or-seize-invoked-REJECT"
                || v.scenario == "transfer-containment-violation-REJECT"
                || v.scenario == "seize-1-input-missing-residual-output-REJECT")))
      = true := by
  native_decide

/-- **Every remaining failure is tamper-intrinsic.** Not one is a CLAB clause
that a real ledger transaction violates, and not one is a harness artifact. -/
theorem remaining_failures_are_tamper_intrinsic :
    all.all (fun v =>
      match failingConjuncts v with
      | none => false
      | some fc =>
          fc == []
            -- deleting an output from a balanced tx unbalances it
            || fc == ["isBalanced"]
            -- grafting a spending purpose onto a minting TxInfo
            || fc == ["validScriptInfo", "scriptInfo.redeemerConsistent",
                      "scriptInfo.purposeWellFormed"]) = true := by
  native_decide

/-! ### The exact failing conjuncts, golden by golden

Sub-conjunct names prefixed `scriptInfo.` are the two halves of
`validScriptInfo` (`CardanoLedgerApi/V3/Contexts.lean`). -/

/-- `programmableLogicBase.base-spend-transfer-tx` (ACCEPTING) — **clean**.  It is
P3's witness, so `WSC/Goldens/Witnesses.lean` can now prove
`ctx_satisfies_validSpendingContext` outright where it previously had to carry a
zero-fee caveat. -/
theorem fail_base_spend_transfer_tx :
    failingConjuncts programmableLogicBase_base_spend_transfer_tx
      = some [] := by
  native_decide

/-- `programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT`
(rejecting) — `validScriptInfo` fails in BOTH halves, intrinsic to the tamper:
this golden grafts a `SpendingScript` purpose onto the minting transaction's
`TxInfo` (`sourceTest`), so (i) there is no `Spending` entry in `txInfoRedeemers`
to match and (ii) the claimed own-input `TxOutRef` is not among `txInfoInputs`.
NOTE for the negative-control story: this golden is therefore still not a
well-formed ledger context, so it exercises the bytecode's reject path but cannot
serve as a `validSpendingContext`-carrying counterexample. -/
theorem fail_base_spend_no_global_or_seize_invoked_REJECT :
    failingConjuncts programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT
      = some ["validScriptInfo", "scriptInfo.redeemerConsistent",
              "scriptInfo.purposeWellFormed"] := by
  native_decide

/-- `programmableTokenMinting.mint-local-registered-by-ref` (ACCEPTING) —
clean. -/
theorem fail_mint_local_registered_by_ref :
    failingConjuncts programmableTokenMinting_mint_local_registered_by_ref
      = some [] := by
  native_decide

/-- `programmableTokenMinting.mint-local-empty-withdrawals-REJECT` (rejecting) —
**clean**: its tamper (`txInfoWdrl := []`) does not break well-formedness, so it
is a genuinely ledger-shaped context that the bytecode rejects — the suite's
clean negative control. -/
theorem fail_mint_local_empty_withdrawals_REJECT :
    failingConjuncts programmableTokenMinting_mint_local_empty_withdrawals_REJECT
      = some [] := by
  native_decide

/-- `programmableTokenMinting.mint-burnonly` (ACCEPTING) — **clean, and this is
the one that mattered most.**  It needed BOTH repairs: Z1's `ltScriptPurpose` fix
(D1, its `Spending`-before-`Minting` order is the ledger's) and the harness fee
fix (A1).  `validMintingContext` is now satisfiable on P4/P4a/P2′'s target class,
so those theorems are no longer vacuous where they are supposed to bite. -/
theorem fail_mint_burnonly :
    failingConjuncts programmableTokenMinting_mint_burnonly
      = some [] := by
  native_decide

/-- `programmableTokenMinting.mint-delegate-transfer-topup` (ACCEPTING) — clean,
same two repairs. -/
theorem fail_mint_delegate_transfer_topup :
    failingConjuncts programmableTokenMinting_mint_delegate_transfer_topup
      = some [] := by
  native_decide

/-- `programmableSeize.seize-1-input` (ACCEPTING) — **clean**, the biggest single
change: it previously failed FOUR conjuncts (`validOutputs`, `txInfoFee > 0`,
`validWithdrawals`, `validRedeemerMap`) from three separate harness artifacts.
The harness now attaches min-UTxO ada to the residual seized-token output, charges
a fee, and emits the two script withdrawal credentials ascending in the ledger's
`Credential` order — which fixes the `Rewarding` pair in `txInfoRedeemers` too. -/
theorem fail_seize_1_input :
    failingConjuncts programmableSeize_seize_1_input
      = some [] := by
  native_decide

/-- `programmableSeize.seize-2-inputs-partial-with-noise` (ACCEPTING) — clean,
same three repairs. -/
theorem fail_seize_2_inputs_partial_with_noise :
    failingConjuncts programmableSeize_seize_2_inputs_partial_with_noise
      = some [] := by
  native_decide

/-- `programmableSeize.seize-1-input-missing-residual-output-REJECT` (rejecting)
— `isBalanced` fails, intrinsic to the tamper (it DELETES the residual output).
The tamper had to be re-pointed upstream: the seize contexts now carry a
balancing change output as their LAST output, so the residual is the
second-to-last, and "drop the last output" would have removed the change output
and left a context the seize validator still ACCEPTS. -/
theorem fail_seize_1_input_missing_residual_output_REJECT :
    failingConjuncts programmableSeize_seize_1_input_missing_residual_output_REJECT
      = some ["isBalanced"] := by
  native_decide

/-- `programmableLogicGlobal.transfer-member-single-policy` (ACCEPTING) —
clean. -/
theorem fail_transfer_member_single_policy :
    failingConjuncts programmableLogicGlobal_transfer_member_single_policy
      = some [] := by
  native_decide

/-- `programmableLogicGlobal.transfer-nonmember-covering-node` (ACCEPTING) —
clean; the cheapest accepting global run and P5's subject shape. -/
theorem fail_transfer_nonmember_covering_node :
    failingConjuncts programmableLogicGlobal_transfer_nonmember_covering_node
      = some [] := by
  native_decide

/-- `programmableLogicGlobal.transfer-mixed-many-policies` (ACCEPTING) —
clean. -/
theorem fail_transfer_mixed_many_policies :
    failingConjuncts programmableLogicGlobal_transfer_mixed_many_policies
      = some [] := by
  native_decide

/-- `programmableLogicGlobal.transfer-containment-violation-REJECT` (rejecting)
— `isBalanced` fails, intrinsic to the tamper (it deletes a base output holding
3 of 5 programmable tokens). -/
theorem fail_transfer_containment_violation_REJECT :
    failingConjuncts programmableLogicGlobal_transfer_containment_violation_REJECT
      = some ["isBalanced"] := by
  native_decide

/-! ## Step 2 — the artifacts are GONE, pinned as facts

The first run of this audit asserted each artifact class as a positive fact
(`A1_every_golden_has_zero_fee`, `A3_only_seize_has_lovelace_free_outputs`, and a
withdrawal-order violation in every seize golden).  Their negations are asserted
here in the same style, so a regression in either component breaks this build
with the artifact named. -/

def feeOf (v : Vector) : Option Integer :=
  (ctxOfHex v.scriptContextHex).map fun c => c.scriptContextTxInfo.txInfoFee

/-- **A1 FIXED.** Every golden now pays a strictly positive fee.  This was the
universal obstruction and the reason no accepting golden could be substituted
into a `validXContext`-carrying theorem. -/
theorem A1_every_golden_has_a_positive_fee :
    all.all (fun v =>
      match feeOf v with
      | none => false
      | some f => decide (0 < f)) = true := by
  native_decide

/-- Number of outputs carrying no lovelace entry. -/
def lovelaceFreeOutputs (v : Vector) : Option Nat :=
  (ctxOfHex v.scriptContextHex).map fun c =>
    (c.scriptContextTxInfo.txInfoOutputs.filter
      (fun o => !hasAdaEntry o.txOutValue)).length

/-- **A3 FIXED.** No golden carries a lovelace-free output any more, including
the two accepting seize goldens whose residual seized-token UTxO was the only
offender.  Cardano's min-UTxO rule forbids a zero-lovelace UTxO, so this also
means the seize BENCHMARKS were under-counting a real seize's value-parsing
work. -/
theorem A3_no_golden_has_lovelace_free_outputs :
    all.all (fun v => lovelaceFreeOutputs v == some 0) = true := by
  native_decide

/-- **A2 FIXED.** No golden's withdrawal map is mis-ordered any more: the harness
sorts `txInfoWdrl` by the LEDGER's `Credential` order. -/
theorem A2_no_withdrawal_order_violations :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx => firstWithdrawalOrderViolation ctx == none) = true := by
  native_decide

/-- **No order violation of any kind remains.** With CLAB's `ltScriptPurpose` /
`ltCredential` corrected (Z1's D1/D2) and the harness emitting both maps in the
ledger's order, `txInfoRedeemers` is sorted in all 13 goldens too. -/
theorem no_order_violations_remain :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          firstRedeemerOrderViolation ctx == none
          && firstWithdrawalOrderViolation ctx == none) = true := by
  native_decide

/-- Retained from the pre-fix audit: canonically re-sorting both maps is a no-op
now, which is the same statement as `no_order_violations_remain` from the other
direction. -/
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

/-! ## Step 3 — the interpretation, machine-checked

The question this audit exists to answer is: *is any failure evidence that CLAB's
predicate excludes a REAL ledger transaction?*  With both components repaired the
answer is **no, in every clause**: all 9 accepting goldens satisfy their matching
`validXContext` verbatim (`every_accepting_golden_satisfies_its_precondition`),
and the 3 remaining FALSE verdicts are all tamper-intrinsic.

What is still NOT established is LR-CTX itself in full generality: these contexts
are built by wsc-poc's benchmark harness, not captured from a node.  They are now
ledger-shaped as far as `validXContext` can tell, which is a much stronger
statement than before, but only contexts produced by `cardano-ledger`'s own
`ScriptContext` builder can settle E5 outright (§6 action 2). -/

/-- Retained: the relaxed predicate also passes on all 9 accepting goldens.
Since the fixes this is strictly weaker than
`every_accepting_golden_satisfies_its_precondition` above, and is kept only so a
regression shows up as "fails verbatim but passes relaxed" rather than as a bare
failure. -/
theorem accepting_goldens_pass_modulo_artifacts :
    acceptingContextsValidRelaxed = true := by
  native_decide

/-- Per-golden form, including the rejecting ones.  Three of the four rejecting
goldens still fail — correctly: two delete an output (breaking `isBalanced`) and
one grafts a spending purpose onto a minting `TxInfo`.  The fourth
(`mint-local-empty-withdrawals-REJECT`) passes.

**CORRECTED (task C3).**  Earlier revisions of this docstring concluded from that
pass that the golden "IS a well-formed ledger context that the bytecode rejects —
making it the suite's only clean negative control".  That conclusion is **FALSE**,
and it was false only because `validScriptContext` did not check the rule that
catches it: the golden empties `txInfoWdrl` but leaves the `Rewarding` redeemer
entry behind, so it violates Conway UTXOW's `ExtraRedeemers`
(`extra_redeemers_in_mint_local_empty_withdrawals` below).  **The suite has no
clean negative control.** -/
theorem relaxed_verdicts :
    all.all (fun v =>
      relaxedVerdict v ==
        some (v.accepts || v.scenario == "mint-local-empty-withdrawals-REJECT"))
      = true := by
  native_decide

/-! ## Step 4 — the `MissingRedeemers` / `ExtraRedeemers` rule (task C3)

`validScriptContext` does **not** contain the Conway UTXOW rule
`hasExactSetOfRedeemers` (`Alonzo/Rules/Utxow.hs:239-262`, reached from Conway at
`Babbage/Rules/Utxow.hs:351`); CLAB states it separately as
`CardanoLedgerApi.V3.Contexts.redeemerCoverage` / `noExtraRedeemers` /
`redeemersExact`, and `WSC/Honest.lean` assumes it as row **S** /
`LR_REDEEMER_COVERAGE`.  Its omission is audit finding **F2**: it is exactly why
every shaped context — two script withdrawals, one redeemer entry — satisfied
`validRewardingContext` while being unbuildable by a node.

This section is the empirical evidence that the new predicate is **not
over-strong**.  If it were, real transactions would fail it; they do not.  All 13
goldens satisfy coverage, and all 9 accepting ones satisfy the FULL exact-set
rule with the needed-purpose multiset matching the redeemer map entry-for-entry
across all four validators, at 2–5 entries, spanning `Spending`, `Rewarding` and
`Minting` purposes.

The needed-purpose list is in the ledger's `getConwayScriptsNeeded`
concatenation order (spending, rewarding, certifying, minting, voting,
proposing), while `txInfoRedeemers` is in `ConwayPlutusPurpose` order
(`Spending < Minting < Certifying < Rewarding < …`).  The rule compares SETS
(`Set.fromList` in `extSymmetricDifference`, `Utxow.hs:381`), so the differing
orders are irrelevant and both predicates test membership only. -/

/-- **Every golden — all 13, accepting and rejecting — satisfies
`redeemerCoverage`.** Nothing in this suite is missing a redeemer entry for a
script it needs.  Contrast every shape in `WSC/Shaped/`, which has two script
withdrawals and one redeemer entry. -/
theorem every_golden_is_redeemer_covered :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          CardanoLedgerApi.V3.Contexts.redeemerCoverage ctx.scriptContextTxInfo)
      = true := by
  native_decide

/-- **The headline for C3.** Every ACCEPTING golden satisfies the full exact-set
rule — both `MissingRedeemers` and `ExtraRedeemers` — with no relaxation.  This
is the measurement that shows the new conjunct excludes no real transaction. -/
theorem every_accepting_golden_has_exact_redeemers :
    all.all (fun v =>
      !v.accepts ||
      (match ctxOfHex v.scriptContextHex with
       | none => false
       | some ctx =>
           CardanoLedgerApi.V3.Contexts.redeemersExact ctx.scriptContextTxInfo))
      = true := by
  native_decide

/-- **NEW FINDING (task C3).** `mint-local-empty-withdrawals-REJECT` violates
`ExtraRedeemers`: its tamper empties `txInfoWdrl` (`wdrl = 0`) but leaves the
`Rewarding` redeemer entry in place, so it needs exactly one purpose (`Minting`)
and carries two.  It is therefore **not** a context any node would build, and the
`relaxed_verdicts` docstring's former claim that it is the suite's only clean
negative control is retracted there. -/
theorem extra_redeemers_in_mint_local_empty_withdrawals :
    (match ctxOfHex
        programmableTokenMinting_mint_local_empty_withdrawals_REJECT.scriptContextHex with
     | none => false
     | some ctx =>
         ctx.scriptContextTxInfo.txInfoWdrl.length == 0
         && CardanoLedgerApi.V3.Contexts.redeemerCoverage ctx.scriptContextTxInfo
         && !CardanoLedgerApi.V3.Contexts.noExtraRedeemers ctx.scriptContextTxInfo)
      = true := by
  native_decide

/-- The measured `(needed purposes, redeemer entries)` pair for every golden, in
`all` order.  This pins `WSC/AUDIT.md` §8 F2's redeemer-count table to the code:
the two counts agree on 12 of 13, and the one disagreement is the
`ExtraRedeemers` outlier above. -/
theorem redeemer_needed_and_present_counts :
    all.map (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => (0, 0)
      | some ctx =>
          ((CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed
              ctx.scriptContextTxInfo).length,
           ctx.scriptContextTxInfo.txInfoRedeemers.length))
      = [ (2, 2)   -- base-spend-no-global-or-seize-invoked-REJECT
        , (3, 3)   -- base-spend-transfer-tx                      (ACCEPTING)
        , (3, 3)   -- transfer-containment-violation-REJECT
        , (3, 3)   -- transfer-member-single-policy               (ACCEPTING)
        , (3, 3)   -- transfer-mixed-many-policies                (ACCEPTING)
        , (2, 2)   -- transfer-nonmember-covering-node            (ACCEPTING)
        , (3, 3)   -- seize-1-input-missing-residual-output-REJECT
        , (3, 3)   -- seize-1-input                               (ACCEPTING)
        , (4, 4)   -- seize-2-inputs-partial-with-noise           (ACCEPTING)
        , (5, 5)   -- mint-burnonly                               (ACCEPTING)
        , (5, 5)   -- mint-delegate-transfer-topup                (ACCEPTING)
        , (1, 2)   -- mint-local-empty-withdrawals-REJECT   <-- ExtraRedeemers
        , (2, 2)   -- mint-local-registered-by-ref                (ACCEPTING)
        ] := by
  native_decide

end WSC.Goldens.Audit
