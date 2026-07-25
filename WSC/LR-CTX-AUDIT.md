# LR-CTX EMPIRICAL AUDIT — CLAB's `validXContext` on the 13 real goldens

**Task Y4 RESULT A. Machine-checked backing: `WSC/Goldens/Audit.lean` (every
claim below is a `native_decide` theorem there; the tables are generated from the
same functions, so prose and code cannot drift).**

ADDENDUM **E5** posits the axiom **LR-CTX**: *for every real script invocation,
the ledger-constructed `ScriptContext` satisfies the matching `validXContext`.*
Every P-theorem in this library takes that predicate as its only per-transaction
hypothesis (`WSC/Props/P3_Base.lean:69`), so LR-CTX is exactly what stops the
theorems from being about a smaller universe than the chain.

---

## 0. Headline

**All 13 goldens decode. All 13 FAIL their matching `validXContext`.**

That is the serious branch the task flags, and it is reported here without
softening. The rest of this document does the two things that turn it from an
alarm into a finding:

1. **localises** every failure to a named conjunct (§3), and
2. **separates** the two possible causes — "CLAB's precondition excludes real
   transactions" vs "these particular contexts are not ledger-shaped" (§4, §5).

The answer is **both, in different clauses**:

* **Three failure classes are harness artifacts** — zero fee (13/13), a
  descending script-credential pair (3/13), lovelace-free outputs (2/13). Each is
  something the real Cardano ledger independently forbids, so CLAB is right and
  the context generator is wrong.
* **One failure class is a genuine CLAB DEFECT** — `validRedeemerMap` fails at a
  `(Spending, Minting)` pair on the two accepting minting goldens (2/13). There
  the goldens are **ledger-correct** and CLAB's `ScriptPurpose` order is not:
  `cardano-ledger` emits `txInfoRedeemers` in `ConwayPlutusPurpose AsIx` order
  (`ConwaySpending < ConwayMinting < …`) and never re-sorts. Since *every*
  programmable-token mint carries both a spending and a minting redeemer,
  **`validMintingContext` is unsatisfiable on P4's entire target class**, and any
  P4/P4a/P2′ theorem stated against it is vacuous exactly where it matters. This
  is defect **D1** of `WSC/STATUS.md` §3, found independently by task Y3 against
  the `cardano-ledger` sources; this audit reproduces it from the goldens and
  localises it to the offending adjacent pair
  (`Audit.order_violations_split_into_two_causes`).
* Two further failures are intrinsic to how the *rejecting* goldens were tampered
  (§4 T1, T2).

Setting D1 aside, CLAB's other clauses are **not** over-strong on real
transactions: with the three harness artifacts accounted for and both order
checks canonically sorted — and with `isBalanced` and every other conjunct still
checked verbatim — all 9 accepting goldens satisfy the predicate
(`Audit.accepting_goldens_pass_modulo_artifacts`).

**What is therefore NOT established:** LR-CTX itself. These contexts are built by
the repo's benchmark harness, not captured from a node (§1), and D1 shows LR-CTX
is currently *false as stated* for minting invocations. The audit settles the
"is the precondition over-strong?" question clause by clause on the strongest
evidence available today, and leaves LR-CTX standing as an axiom — with one
clause of it now known to need repair — pending node-captured contexts (§6).

---

## 1. Provenance caveat (stated up front, per the task)

The golden contexts are **benchmark-harness-built, not mockchain-captured.**
`WSC/goldens/MANIFEST.md` records the construction: the repo's on-chain benchmark
catalogue (`src/programmable-tokens-test/exe/BenchmarkOnchainScripts.hs`) builds
`PlutusLedgerApi.V3.ScriptContext` values through
`ProgrammableTokens.Test.ScriptContext.Builder.buildBalancedScriptContext`, which
gives them canonical ada-first sorted values (`normalizeValue`), `TxOutRef`-sorted
inputs and reference inputs, and a value-balancing change output. What each
golden *is* backed by is strong: the actual production-exported script was run on
the dumped context at PV11 through
`PlutusLedgerApi.V3.evaluateScriptCounting`, and its accept/reject outcome and
`ExBudget` were recorded (and later reproduced to the unit by PCB's own CEK,
`WSC/goldens/K-MEASUREMENTS.md` §2). So these are real transactions as far as the
*validator* is concerned. They are only "ledger-shaped" as far as the *ledger's
own context builder* is concerned — and §4 shows the harness gets three ledger
invariants wrong (while CLAB gets a fourth wrong).

The rejecting goldens are single-field tampers of accepting ones; two of them
tamper by **deleting an output**, which necessarily breaks value conservation.
That is a property of the tamper, not a discovery about the ledger.

---

## 2. Method

| step | mechanism | source |
|---|---|---|
| hex → bytes | PCB's own hex decoder, the one `#import_uplc … double_cbor_hex` uses | `PlutusCore/UPLC/ScriptEncoding/Basic.lean:42-48` |
| bytes → `Data` | PCB's CBOR decoder, inverse of the `serialiseData` builtin; **whole input must be consumed** | `PlutusCore/Cbor/Basic.lean:770` |
| `Data` → `ScriptContext` | CLAB's own `IsData ScriptContext` instance | `CardanoLedgerApi/V3/Contexts.lean:587` |
| predicate | CLAB `validSpendingContext` / `validMintingContext` / `validRewardingContext`, unmodified | `CardanoLedgerApi/V3/Contexts.lean:1231-1246` |
| evaluation | **`native_decide` throughout** | see below |

**Why `native_decide` and not kernel `decide`/`rfl`.** Two independent reasons:
PCB's CBOR decoder is a `partial def` (`Cbor/Basic.lean:711-766`) and so has no
equational lemmas for the kernel to unfold; and each context is ~1.2 kB of `Data`
whose traversal through `validScriptContext` is orders of magnitude cheaper in
compiled code. `native_decide` adds the Lean compiler and these `Decidable`
instances to the trust base — nothing about the validators or the ledger. Total
cost: the whole audit module elaborates in **2.1 s** (`lake build
WSC.Goldens.Audit`).

**Which predicate per validator** (fixed by script purpose, source-cited in
`WSC/Goldens/Decode.lean`): base → spending (`ProgrammableLogicBase.hs:717-729`);
minting → minting (`Issuance.hs:132`); seize → rewarding
(`ProgrammableLogicBase.hs:1290`); global → rewarding
(`ProgrammableLogicBase.hs:1176`).

### 2.1 The bridge is lossless (prerequisite)

`Audit.bridge_is_faithful` proves, for all 13 goldens:

| gate | result |
|---|---|
| `scriptContextHex` decodes to a `ScriptContext` | **13/13** |
| `Data`-level round-trip (`decode → encode`) byte-identical | **13/13** |
| **CLAB-`ScriptContext`-level round-trip** (`hex → Data → ScriptContext → Data → hex`) byte-identical | **13/13** |
| `redeemerHex` round-trips | 13/13 |
| `paramsHex` (19 payloads) round-trip | 19/19 |
| `redeemerHex` = the decoded context's own `scriptContextRedeemer` | 13/13 |

The third row is the load-bearing one: CLAB's `ScriptContext` reading of a golden
loses **nothing**, so every verdict below is a statement about the real
off-chain-produced transaction, not about a lossy Lean rendering of it.

---

## 3. RESULT A — the table

`validXContext` = purpose gate ∧ `validScriptInfo` ∧ `validTxInfo`. Conjuncts are
listed in source order (`Contexts.lean:979-1002`, `:1197-1211`); the two
`scriptInfo.*` rows are the halves of `validScriptInfo` (`:1001-1002`), split out
for attribution.

| # | golden | accepts | decoded | **verdict** | failing conjuncts |
|---|---|:--:|:--:|:--:|---|
| 1 | `programmableLogicBase.base-spend-transfer-tx` | yes | ✔ | **FALSE** | `txInfoFee > 0` |
| 2 | `programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT` | no | ✔ | **FALSE** | `validScriptInfo`, `scriptInfo.redeemerConsistent`, `scriptInfo.purposeWellFormed`, `txInfoFee > 0` |
| 3 | `programmableTokenMinting.mint-local-registered-by-ref` | yes | ✔ | **FALSE** | `txInfoFee > 0` |
| 4 | `programmableTokenMinting.mint-burnonly` | yes | ✔ | **FALSE** | `txInfoFee > 0`, `validRedeemerMap` |
| 5 | `programmableTokenMinting.mint-delegate-transfer-topup` | yes | ✔ | **FALSE** | `txInfoFee > 0`, `validRedeemerMap` |
| 6 | `programmableTokenMinting.mint-local-empty-withdrawals-REJECT` | no | ✔ | **FALSE** | `txInfoFee > 0` |
| 7 | `programmableSeize.seize-1-input` | yes | ✔ | **FALSE** | `validOutputs`, `txInfoFee > 0`, `validWithdrawals`, `validRedeemerMap` |
| 8 | `programmableSeize.seize-2-inputs-partial-with-noise` | yes | ✔ | **FALSE** | `validOutputs`, `txInfoFee > 0`, `validWithdrawals`, `validRedeemerMap` |
| 9 | `programmableSeize.seize-1-input-missing-residual-output-REJECT` | no | ✔ | **FALSE** | `txInfoFee > 0`, `validWithdrawals`, `validRedeemerMap`, `isBalanced` |
| 10 | `programmableLogicGlobal.transfer-member-single-policy` | yes | ✔ | **FALSE** | `txInfoFee > 0` |
| 11 | `programmableLogicGlobal.transfer-nonmember-covering-node` | yes | ✔ | **FALSE** | `txInfoFee > 0` |
| 12 | `programmableLogicGlobal.transfer-mixed-many-policies` | yes | ✔ | **FALSE** | `txInfoFee > 0` |
| 13 | `programmableLogicGlobal.transfer-containment-violation-REJECT` | no | ✔ | **FALSE** | `txInfoFee > 0`, `isBalanced` |

Theorems: `Audit.all_goldens_fail_the_precondition`,
`Audit.every_verdict_is_false`, and one `Audit.fail_<scenario>` per row asserting
the failing-conjunct list **exactly** (so an added or removed failure breaks the
build).

`validRedeemerMap` fails in **5** goldens (4, 5, 7, 8, 9) — but for two different
reasons, which §4 separates: goldens 4 and 5 break at a `(Spending, Minting)`
pair (defect D1, CLAB's fault) and goldens 7, 8, 9 at a
`(Rewarding script, Rewarding script)` pair (artifact A2, the harness's fault).
`Audit.order_violations_split_into_two_causes` pins the offending pair per
golden.

**Conjuncts that hold in all 13:** purpose gate, `validInputs`,
`validReferenceInputs`, `validMintValue`, `validTxRange`, `validSigners`,
`validDatumMap`, `validVoterMap`, `validTreasuryAmount`,
`validTreasuryDonation` — and `isBalanced` in all 11 goldens that did not have an
output deleted.

---

## 4. Root-cause analysis: three harness artifacts, one CLAB defect, two tamper artifacts

### A1 — `txInfoFee = 0` (13/13, the universal obstruction)

`Audit.A1_every_golden_has_zero_fee`: every golden has `txInfoFee = 0`. CLAB
requires `txInfoFee > 0` (`Contexts.lean:1201`, `[LEDGER-RULE]` 4). A Cardano
transaction cannot have a zero fee — `minFeeA·size + minFeeB > 0` for any
non-empty transaction — so **CLAB is right and the harness is wrong**.

This one cannot be patched away in isolation: `isBalanced` requires
`lovelaceOf(spent) = lovelaceOf(produced) + fee` (`Contexts.lean:1153`), so
raising the fee without moving lovelace would break conservation. That is why the
relaxation in §5 *drops* the clause rather than repairing it, which is the weaker
(more conservative) choice.

### A2 — a descending script-credential pair (3/13: the seize goldens)

The three seize goldens carry
`txInfoWdrl = [(Script 40…40, 0), (Script 14…14, 0)]` — descending, since
`0x40 > 0x14` — and their `txInfoRedeemers` repeat the same two credentials in the
same wrong order as `Rewarding` entries. So **one** harness mistake breaks two
clauses: `validWithdrawals` (`Contexts.lean:923-930`) and `validRedeemerMap` at a
`(Rewarding script, Rewarding script)` pair.

Both credentials are script credentials, and within script credentials CLAB's and
the ledger's `Credential` orders agree (`WSC/STATUS.md` §3 D2), while the ledger
builds the withdrawal map from a sorted `Map RewardAccount Coin` and orders equal
purpose kinds by their argument. **So here CLAB is right and the context is
genuinely mis-ordered: harness artifact.** This is exactly the distinction
`Audit.order_violations_split_into_two_causes` makes machine-checkable — same
failing clause as D1, opposite conclusion, told apart by which adjacent pair
breaks it.

`Audit.order_failures_are_order_only` proves both are **pure order failures**:
canonically re-sorting both maps (`canonicaliseOrder`, a permutation that touches
no value, no fee and no balance) makes both clauses hold in all 13 goldens.

### D1 — `validRedeemerMap` at a `(Spending, Minting)` pair (2/13) — **a CLAB defect, not a harness artifact**

Goldens 4 and 5 (`mint-burnonly`, `mint-delegate-transfer-topup`) carry redeemer
purposes

```
[Spending, Minting, Rewarding(13…13), Rewarding(15…15), Rewarding(16…16)]
```

which is strictly ascending *except* at the very first pair under CLAB's order.
CLAB's `ltScriptPurpose` (`Contexts.lean:65-84`) follows the **Plutus constructor
order** `Minting < Spending < Rewarding < Certifying < Voting < Proposing`, so it
demands `Minting` first.

**The ledger does not produce that order.** `cardano-ledger` builds
`txInfoRedeemers` from a `Map (ConwayPlutusPurpose AsIx era) …` whose derived
`Ord` is `ConwaySpending < ConwayMinting < ConwayCertifying < ConwayRewarding < …`
(`eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs:202-213`), and
`transTxRedeemers` converts it with
`unsafeFromList ∘ mapM … ∘ Map.toList` — **no re-sort**
(`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, used for V3 at
`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:499,512`); citations from
task Y3 at `cardano-ledger` @ `cd8b7fab8`. So a transaction carrying both a
spending and a minting redeemer really does present `Spending` first, and these
two goldens are **ledger-correct**.

**Consequence.** Every programmable-token mint spends at least one UTxO (it must,
to pay a fee) and mints, so every real issuance transaction carries both
redeemers and is therefore *not* CLAB-sorted. `validMintingContext` is
**unsatisfiable on P4/P4a/P2′'s entire target class**, and a theorem of the form
`validMintingContext ctx → accept → POST` is vacuous exactly where it is supposed
to bite. This is the most serious finding in this audit.

**Fix (in CLAB, not in the goldens).** Either change `ltScriptPurpose` to the
ledger's `AsIx` order, or weaken `validRedeemerMap` to duplicate-freeness — which
is all the WSC proofs actually consume. Tracked as `WSC/STATUS.md` §3 defect D1
and quarantined for now in `WSC/Honest.lean`'s `CLABMapOrderAgrees`. The
companion defect D2 (CLAB `Credential` order is `PubKey < Script`, the ledger's
is `ScriptHashObj < KeyHashObj`) does not bite here because WSC's withdrawals are
all script credentials — which is precisely why A2 above is a *harness* artifact
and D1 is not.

### A3 — lovelace-free outputs (2/13: the accepting seize goldens)

`Audit.A3_only_seize_has_lovelace_free_outputs`: exactly `seize-1-input` and
`seize-2-inputs-partial-with-noise` each carry **one** output with no lovelace
entry — the residual seized-token UTxO. Their raw values are

```
a1581c1b1b…1ba142306301        -- {1b…1b: {"0c": 1}}
a1581c1b1b…1ba142306304        -- {1b…1b: {"0c": 4}}
```

`validTxOutValue` demands an ada-FIRST entry with positive quantity
(`V1/Contexts.lean:769-784`), which is the Lean rendering of Cardano's
min-UTxO-ada rule: **no real UTxO can hold zero lovelace.** Harness artifact
again — and a mildly interesting one, because the seize validator's residual
output is exactly where a real deployment must remember to attach min-ada.

### T1 — `isBalanced` fails on the two output-deleting tampers (goldens 9, 13)

`seize-1-input-missing-residual-output-REJECT` removes the residual output and
`transfer-containment-violation-REJECT` removes a base output holding 3 of 5
programmable tokens. Deleting an output from a balanced transaction unbalances
it. Intrinsic to the tamper; not a finding about CLAB. Note the accepting
siblings all satisfy `isBalanced`, so the harness's balancing works.

### T2 — `validScriptInfo` fails on golden 2

`base-spend-no-global-or-seize-invoked-REJECT` grafts a `SpendingScript` purpose
onto the *minting* transaction's `TxInfo` (`sourceTest` field). Both halves of
`validScriptInfo` then fail: there is no `Spending` entry in `txInfoRedeemers` for
`findRedeemer` to match (`:1001`), and the claimed own-input `TxOutRef`
(`f0f0…0d#0`) is not among `txInfoInputs` (which holds `fafa…ce#0`) (`:983`).

**Consequence worth flagging for the polarity story (ADDENDUM E9):** this
rejecting golden is not a well-formed ledger context at all, so it can exercise
the bytecode's reject path but **cannot** serve as a
`validSpendingContext`-carrying counterexample. Of the four rejecting goldens
only `mint-local-empty-withdrawals-REJECT` is a well-formed-modulo-artifacts
context that the bytecode rejects (`Audit.relaxed_verdicts`) — i.e. the suite has
exactly **one** clean negative control.

---

## 5. The interpretation, machine-checked

The task's reading of an all-TRUE result would have been "the preconditions are
not over-strong — they do not silently exclude real transactions". We got
all-FALSE, so the question becomes sharper: *does any failure exhibit a CLAB
clause that a real ledger transaction could violate?*

**No.** `Audit.accepting_goldens_pass_modulo_artifacts` proves

> **all 9 accepting goldens satisfy their matching `validXContext`** when
> evaluated by `validContextRelaxed`, which
> * canonically re-sorts `txInfoWdrl` and `txInfoRedeemers` (A2 and D1 — a
>   permutation only; for the two minting goldens this sorts *away* from the real
>   ledger order, and is used there only to show the failure is order-only), and
> * drops `txInfoFee > 0` (A1) and relaxes the ada-first requirement to
>   "prepend 2 ada if the value has none" (A3 — token-name sortedness, currency
>   sortedness and positivity of the token part are still fully checked),
>
> while checking **`validScriptInfo`, `validInputs`, `validReferenceInputs`,
> `validMintValue`, `validTxRange`, `validSigners`, `validDatumMap`,
> `validVoterMap`, both treasury clauses and `isBalanced` verbatim.**

So the *only* obstructions between a real accepting WSC transaction and the
precondition our theorems assume are the three context-generator defects (each
independently forbidden by the Cardano ledger) plus CLAB's own D1. In particular
**value
conservation, script-info consistency, value canonicity of every ada-bearing
output, input/reference-input sortedness and mint-value well-formedness all hold
on real WSC transactions of all four validators' shapes** — which is the
substantive part of what E5 needed.

### 5.1 What this does and does not license

| claim | status |
|---|---|
| CLAB's `validXContext` is not over-strong in any clause other than `validRedeemerMap` | **supported** (§5) |
| CLAB's `validRedeemerMap` IS over-strong — it excludes every real programmable-token mint | **established** (§4 D1); blocks P4/P4a/P2′ |
| The 9 accepting goldens can be substituted into a P-theorem to re-derive its conclusion | **FALSE** — blocked by A1 (`txInfoFee = 0`) in all 9 |
| P3's non-vacuity rests on a real transaction | **supported**, but via the *bytecode* accept fact, not via the precondition — see `WSC/Goldens/Witnesses.lean` and its `ctx_fails_validSpendingContext_only_on_fee` |
| LR-CTX (E5) holds for ledger-constructed contexts | **still an axiom** — no node-captured context was tested |

---

## 6. Actions and follow-ups

1. **(BLOCKER for P4/P4a/P2′) Fix CLAB's `validRedeemerMap` / `ltScriptPurpose`
   (defect D1, §4).** Until then `validMintingContext` is unsatisfiable for real
   issuance transactions and any minting-side theorem is vacuous on its target
   class. Cheapest correct fix: weaken `validRedeemerMap` to duplicate-freeness
   (all the WSC proofs use); fully correct fix: adopt the ledger's
   `ConwayPlutusPurpose AsIx` order. Coordinate with `WSC/Honest.lean`'s
   `CLABMapOrderAgrees` quarantine.
2. **(fidelity, highest value) Capture contexts from a real ledger.** Until a
   `ScriptContext` produced by `cardano-ledger`'s own builder (or a node/mockchain
   run) is put through this same audit, LR-CTX rests on an argument about the
   harness rather than a measurement. The bridge is now in place
   (`WSC/Goldens/Decode.lean`), so the marginal cost of auditing a captured
   context is one JSON file plus a regenerated `Vectors.lean`.
3. **(upstream, wsc-poc) Fix three ledger invariants in the benchmark
   `ScriptContext` builder** — `buildBalancedScriptContext` should (a) charge a
   positive fee and balance against it, (b) emit the two script withdrawal
   credentials ascending (which also fixes the `Rewarding` pair in
   `txInfoRedeemers`), (c) attach min-ada to the residual seized-token output.
   All three make the benchmark contexts *more* representative of what the
   validators see on chain, and (c) in particular means the seize benchmarks
   currently under-count a real seize's value-parsing work. Do **not** "fix" the
   `Spending`-before-`Minting` redeemer order: that one is already correct (§4
   D1). Filed alongside the existing MANIFEST note about the base bench's arity
   bug.
4. **(this repo) Do not use golden 2 as a precondition-carrying negative
   control** (§4 T2). If a rejecting `validSpendingContext` witness is needed for
   the base validator, build it by tampering the *withdrawal map* of
   `base-spend-transfer-tx`, not by grafting purposes across transactions.
5. **(this repo) When re-generating goldens, re-run this audit.**
   `WSC/Goldens/Audit.lean` is part of `lake build WSC`; a changed context that
   breaks a different conjunct will fail the build with the exact clause named.

---

## 6.1 Independent corroboration

Task Y3 ran the same experiment independently and concurrently, from a throwaway
generated Lean file rather than a library module
(`WSC/goldens/ctx-audit/GenCtxAudit.py`, `…/GenCtxAuditDetail.py`; results
recorded in `WSC/STATUS.md` §3 D1–D3 and in `WSC/Honest.lean`'s `LR_CTX` audit
table). The two agree on every verdict: all 13 FALSE, `txInfoFee = 0` universal,
`validRedeemerMap` false for the accepting minting goldens, `validWithdrawals`
false for the 3 seize goldens, `validOutputs` false for the 2 accepting seize
goldens. Y3 additionally traced the redeemer-order question to `cardano-ledger`
and established that CLAB — not the harness — is wrong there; **this document's
first draft had that attribution backwards and has been corrected accordingly.**
This audit adds, beyond Y3's pass: the `ScriptContext`-type-level byte-identical
round-trip receipt (§2.1), the per-golden failing-conjunct lists as build-breaking
theorems, the mechanical A2-vs-D1 split, and the
`accepting_goldens_pass_modulo_artifacts` result. Both live in `lake build WSC`
now, so neither can silently rot.

---

## 7. Reproduction

```
# regenerate the two generated modules from the golden JSONs (and verify)
python3 WSC/Goldens/gen-vectors.py
python3 WSC/Goldens/gen-vectors.py --check      # -> CHECK OK x3 (Vectors, Terms, TermsCheck)

# the audit itself (2.1 s), and the whole WSC library
lake build WSC.Goldens.Audit
lake build WSC
```

`lake build WSC` on a warm `.lake`: **9.1 s** for the seven `WSC/Goldens/*`
modules (`Vectors` 0.45 s, `Decode` 2.5 s, `Terms` 3.3 s, `TermsCheck` 1.6 s,
`RedeemerGate` 1.8 s, `Audit` 2.1 s, `Witnesses` 3.0 s), 356 jobs,
`Build completed successfully`.
