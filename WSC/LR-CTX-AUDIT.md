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

The evidence comes down decisively on the second: **all 9 accepting goldens
satisfy `validXContext` once four named benchmark-harness artifacts are
accounted for, with `isBalanced` and every other conjunct still checked
verbatim** (`Audit.accepting_goldens_pass_modulo_artifacts`). Each of the four
artifacts is something the real Cardano ledger independently forbids. No failure
was traced to a CLAB clause that a real transaction could violate.

**What is therefore NOT established:** LR-CTX itself. These contexts are built by
the repo's benchmark harness, not captured from a node (§1). The audit closes the
"is the precondition over-strong?" question against the strongest evidence
available today, and leaves LR-CTX standing as an axiom pending node-captured
contexts (§6, follow-up 1).

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
own context builder* is concerned — and §3 shows the harness gets four ledger
invariants wrong.

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

**Conjuncts that hold in all 13:** purpose gate, `validInputs`,
`validReferenceInputs`, `validMintValue`, `validTxRange`, `validSigners`,
`validDatumMap`, `validVoterMap`, `validTreasuryAmount`,
`validTreasuryDonation` — and `isBalanced` in all 11 goldens that did not have an
output deleted.

---

## 4. Root-cause analysis: four harness artifacts + two tamper artifacts

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

### A2 — withdrawal map not credential-sorted (3/13: the seize goldens)

The three seize goldens carry
`txInfoWdrl = [(Script 40…40, 0), (Script 14…14, 0)]` — descending, since
`0x40 > 0x14`. CLAB requires ascending (`validWithdrawals`,
`Contexts.lean:923-930`). The ledger builds the withdrawal map from a
`Map RewardAccount Coin`, i.e. sorted. **Harness artifact.**

### A2′ — redeemer map not `ScriptPurpose`-sorted (4/13)

Goldens 4, 5, 7, 8 carry `txInfoRedeemers` beginning
`[Spending …, Minting …, …]`. CLAB's order is
`Minting < Spending < Rewarding < Certifying < Voting < Proposing`
(`ltScriptPurpose`, `Contexts.lean:65-84`), which is exactly PlutusLedgerApi's
derived `Ord ScriptPurpose` (same constructor order,
`PlutusLedgerApi.V3.Contexts`). So the harness emits the pair in the wrong order
and **CLAB matches the ledger**. Note the two `mint-local-*` goldens pass this
clause — their `TxInfo` happens to contain no `Spending` redeemer — which is why
the failure is 4/13 rather than all the minting/seize goldens.

`Audit.A2_ordering_only` proves A2 and A2′ are **pure order defects**: canonically
re-sorting both maps (`canonicaliseOrder`, a permutation that touches no value,
no fee and no balance) makes both clauses hold in all 13 goldens.

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
> * canonically re-sorts `txInfoWdrl` and `txInfoRedeemers` (A2/A2′ — a
>   permutation only), and
> * drops `txInfoFee > 0` (A1) and relaxes the ada-first requirement to
>   "prepend 2 ada if the value has none" (A3 — token-name sortedness, currency
>   sortedness and positivity of the token part are still fully checked),
>
> while checking **`validScriptInfo`, `validInputs`, `validReferenceInputs`,
> `validMintValue`, `validTxRange`, `validSigners`, `validDatumMap`,
> `validVoterMap`, both treasury clauses and `isBalanced` verbatim.**

So the *only* obstructions between a real accepting WSC transaction and the
precondition our theorems assume are four defects of the context generator, each
independently forbidden by the Cardano ledger. In particular **value
conservation, script-info consistency, value canonicity of every ada-bearing
output, input/reference-input sortedness and mint-value well-formedness all hold
on real WSC transactions of all four validators' shapes** — which is the
substantive part of what E5 needed.

### 5.1 What this does and does not license

| claim | status |
|---|---|
| CLAB's `validXContext` is not over-strong in any clause these 9 real accepting transactions exercise | **supported** (§5) |
| The 9 accepting goldens can be substituted into a P-theorem to re-derive its conclusion | **FALSE** — blocked by A1 (`txInfoFee = 0`) in all 9 |
| P3's non-vacuity rests on a real transaction | **supported**, but via the *bytecode* accept fact, not via the precondition — see `WSC/Goldens/Witnesses.lean` and its `ctx_fails_validSpendingContext_only_on_fee` |
| LR-CTX (E5) holds for ledger-constructed contexts | **still an axiom** — no node-captured context was tested |

---

## 6. Actions and follow-ups

1. **(fidelity, highest value) Capture contexts from a real ledger.** Until a
   `ScriptContext` produced by `cardano-ledger`'s own builder (or a node/mockchain
   run) is put through this same audit, LR-CTX rests on an argument about the
   harness rather than a measurement. The bridge is now in place
   (`WSC/Goldens/Decode.lean`), so the marginal cost of auditing a captured
   context is one JSON file plus a regenerated `Vectors.lean`.
2. **(upstream, wsc-poc) Fix four ledger invariants in the benchmark
   `ScriptContext` builder** — `buildBalancedScriptContext` should (a) charge a
   positive fee and balance against it, (b) sort `txInfoWdrl` by credential,
   (c) sort `txInfoRedeemers` by `ScriptPurpose` (`Minting < Spending <
   Rewarding`), (d) attach min-ada to the residual seized-token output. All four
   make the benchmark contexts *more* representative of what the validators see
   on chain, and (d) in particular means the seize benchmarks currently
   under-count a real seize's value-parsing work. Filed alongside the existing
   MANIFEST note about the base bench's arity bug.
3. **(this repo) Do not use golden 2 as a precondition-carrying negative
   control** (§4 T2). If a rejecting `validSpendingContext` witness is needed for
   the base validator, build it by tampering the *withdrawal map* of
   `base-spend-transfer-tx`, not by grafting purposes across transactions.
4. **(this repo) When re-generating goldens, re-run this audit.**
   `WSC/Goldens/Audit.lean` is part of `lake build WSC`; a changed context that
   breaks a different conjunct will fail the build with the exact clause named.

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
