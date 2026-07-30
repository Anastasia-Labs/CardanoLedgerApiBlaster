# `#prep_uplc` benchmark: the UNSHAPED P1 and P2 obligations

> **Cross-reference note.** This file ships in two trees. Prose citations to
> `WSC/ARCHITECTURE.md`, `WSC/AUDIT.md` and `WSC/IMPACT-PR112.md` resolve in the
> canonical `CardanoLedgerApiBlaster` tree; citations to `docs/METHOD.md`,
> `docs/LIMITATIONS.md` and `docs/RESULTS.md` resolve in the published mirror.
> `WSC/goldens/K-MEASUREMENTS.md` and every `WSC/**.lean` path resolve in both.

**Audience: the Blaster team.** This document hands you two deliberately
non-building Lean modules as an optimisation target, together with everything we
measured about why they do not build.

**We are NOT claiming any of this as a result.** Nothing below is a proof about
the WSC validators. P1 and P2 *are* proved against the production bytecode — over
SHAPED contexts, at the same budgets, in
`WSC/Props/Shaped/P1ShapedR.lean` and
`WSC/Props/Shaped/P2ShapedR.lean` /
`P2ShapedR2.lean`. Those are the results. This
directory is the *wish*: the same properties over a fully symbolic
`ScriptContext`, which is what we would publish if `#prep_uplc` scaled.

---

## 1. What the artifact is

| file | builds? | what it is |
|---|---|---|
| `WSC/Benchmark/P1UnshapedStatement.lean` | **yes** | the P1 statement, parametric in the accept predicate; 4 kernel-checked specialisation theorems; the executable non-vacuity certificate |
| `WSC/Benchmark/P1Unshaped.lean` | **no, by design** | `#prep_uplc … 300000` (mainnet ex-unit ceiling, §4.0) over the unshaped inputs function + the P1 obligation |
| `WSC/Benchmark/P2UnshapedStatement.lean` | **yes** | the same for P2, both conjuncts; 5 `rfl` audits + 3 specialisation theorems + non-vacuity |
| `WSC/Benchmark/P2Unshaped.lean` | **no, by design** | `#prep_uplc … 300000` (same ceiling) + both P2 obligations |
| `WSC/Benchmark/EqDataTranslationFAILS.lean` | **no, by design** | 17-second reproducer (16.85 s measured, §6.4) for the SECOND blocker |

The split exists so that the intractable prep does not take the *statement* down
with it: a benchmark whose statement nobody can check is worse than no benchmark.

**Nothing imports any of the five.** `lake build WSC WSC.ShapeBridge` — what CI
runs — does not see them, and its census is unchanged (451 jobs, 126 `✅ Valid` +
75 `✅ Expected Falsified`, 0 errors). Run them deliberately:

```
lake build WSC.Benchmark.P1UnshapedStatement    # ≈1.3 s warm, 0 errors
lake build WSC.Benchmark.P2UnshapedStatement    # ≈1.4 s warm, 0 errors
lake build WSC.Benchmark.P1Unshaped             # does NOT terminate
lake build WSC.Benchmark.P2Unshaped             # does NOT terminate
lake build WSC.Benchmark.EqDataTranslationFAILS # errors in 16.85 s (§6.4)
```

Always time with `lake build`, never `lake env lean`: the latter omits
`--load-dynlib`, runs the solver interpreted and is 15–50× slower. An earlier
prep-cost table in this repository was taken that way and was 6–57× pessimistic.

---

## 2. The properties, in one line each

**P1 (transfer containment).** For every ledger-valid transaction, every asset
`(cs, tn)` whose policy is REGISTERED — no authenticated directory node in the
reference inputs covers `cs`, so the transfer walk's only exemption route is shut
— and the mini-ledger base credential `plc` the transaction's own protocol-params
datum publishes: if the compiled `programmableLogicGlobal` accepts, then

```
outAtBase(plc, cs, tn)  ≥  inAtBase(plc, cs, tn)  +  mintSigned(cs, tn)
```

The mint is **SIGNED**. The ledger's `mint` field is one signed integer per asset
(minted − burned) and the `max(mint, 0)` variant is machine-refuted on a burn:
`WSC.P1RShapedWitness.mintPos_form_REFUTED` exhibits a ledger-legal,
redeemer-covered, bytecode-ACCEPTED burn where the signed requirement holds
(`1 ≥ 5 − 4`) and `mintPos` fails (`1 ≥ 5 + 0`). Do not "repair" it.

**P2 (seize), both conjuncts.** (a) *structure preservation* — walking the
inputs in order, each input at the mini-ledger base credential is paired with the
next output of the redeemer's paired-output cursor, and that pair has the same
address (staking credential included), datum and reference script, and identical
holdings of every policy other than the seized one and other than ada; ada may
only be TOPPED UP. (b) *containment of the seized delta* — for every token name,
the seized policy's total at base outputs is at least its total at base inputs
plus the signed net mint.

---

## 3. Statement correctness — what to check, and the one thing that changed

The unshaped statements were written by mirroring the shaped ones clause for
clause. A reviewer should diff:

* `WSC.Benchmark.P1UnshapedForm` against `WSC.P1R_T1_stmt`;
* `WSC.Benchmark.P2aUnshapedForm` against `WSC.P2a_R_structure`;
* `WSC.Benchmark.P2bUnshapedForm` against `WSC.P2b_R_containment`.

Every `<shape> <~40–50 leaves>` becomes a single universally quantified
`(ctx : ScriptContext)`, and the `isSuccessful (applied…Shaped….prop …)`
hypothesis becomes `accept ppCS ctx`. The ledger-validity hypothesis, the
registration hypothesis and the ground-truth postconditions are unchanged.

**One clause had to be ADDED per statement, and it is not optional.** The shaped
statements quantify `plc` (the mini-ledger base credential) and `dirCS` (the
directory policy) as leaves, and the SHAPE ties both to the transaction by
construction — `p1ShapedParamsIn` / `seizeShapedParamsIn` put a protocol-params
reference input in the context whose inline datum publishes them, and the shaped
redeemer's `paramsRefIdx` is the literal index of that input.

Quantifying `plc` and `dirCS` freely over an arbitrary `ctx` does not give a
weaker P1 — **it gives a FALSE statement.** Take any accepted transfer that mints
a positive quantity of `(cs, tn)` at a pubkey address; instantiate `plc` to a
credential the transaction never mentions and `dirCS` to a policy no reference
input carries. Then `coveringNodeExists dirCS cs … = false` holds vacuously,
`outSum = inSum = 0`, and the conclusion reads `0 ≥ 0 + q` with `q > 0`. So the
unshaped statements carry, as a hypothesis, exactly the by-construction fact the
shape supplied:

```lean
-- P1
paramsPublishedBy ctx = some (dirCS, IsData.toData (Credential.ScriptCredential plc))
-- P2
SeizeModel.seizedPolicyOf ctx            = some key
progLogicCredPublishedBySeize ctx        = some (IsData.toData (Credential.ScriptCredential plc))
SeizeModel.pairedOutputsOf ctx           = some pairedOuts
```

All of these are **ground truth only** — functions of the redeemer `Data`, the
reference-input list and one inline datum, with no validator-computed accumulator
(ARCHITECTURE.md D3 / Tier 0.1). `seizedPolicyOf` and `pairedOutputsOf` are the
audited projections of `WSC/Model/SeizeModel.lean` §6 reused BY NAME — they are
the quantities ARCHITECTURE.md §3-P2 writes P2 over. Nothing touches
`SeizeModel.seizeModel`, whose fidelity axiom was retracted at task R1.

Both `paramsPublishedBy` and `progLogicCredPublishedBySeize` deliberately OMIT
the `phasCSH ppCS` authentication gate that `SeizeModel.paramsAtRefIdx` applies
(`ProgrammableLogicBase.hs:832`). That makes the hypothesis weaker and the
statement STRONGER: the extra contexts it admits are ones the bytecode errors on,
so they are discharged by the `accept` hypothesis, not by an assumption. It also
keeps the specialisation theorems free of a `pCS = ppCS` side condition —
compare `WSC.shapeR_progLogicCred`, which needs one, and
`WSC.P2_R_gates_are_earned`, which proves the accept path forces it.

### 3.0 The statements are NOT new — they are the published model-level ones

Note on P2's conjunct 2: the model-level reduction carries an open obligation
(`WSC/Props/P2_Seize.lean:671-690`, its §5 "B2": canonicity propagated through
the validator's own combinators into `checkBalanceInvariant`). The unshaped
statement here is over the BYTECODE, so it does not inherit that obligation as a
hypothesis — a `✅ Valid` verdict on `P2b_unshaped` would discharge it by
symbolic execution, exactly as the shaped classes already do.

Before reading §3.1, note that this repository already publishes unshaped,
fully-symbolic versions of both properties, and the benchmark statements are those,
re-pointed at the bytecode:

| benchmark statement | already published as | status of the published one |
|---|---|---|
| `P1UnshapedForm` | `WSC.Model.P1_model` (`WSC/Props/P1_Transfer.lean:362`) | a `def`; its links L1.1a/b–L1.6 are open |
| `P2aUnshapedForm` | `WSC.P2.P2a_seizeModel_preserves_structure` (`WSC/Props/P2_Seize.lean:254`) | **PROVED, unconditionally, in the Lean kernel, for arbitrary `ctx`** |
| `P2bUnshapedForm` | `WSC.P2.P2b_seized_delta_contained` (`WSC/Props/P2_Seize.lean:300`) | a `def`; the conjunct the model route could not close |

The differences, in full:

* the accept hypothesis names the **compiled program's prepped residual** instead
  of the hand transcription (`globalModel` / `seizeModel`). That is the whole
  point: both transcriptions' fidelity axioms were REFUTED at wsc-poc `2306678`
  and retracted at task R1 (`WSC/Model/GlobalModelRefuted.lean`,
  `WSC/Model/SeizeModelRefuted.lean`), so the published model-level statements
  imply nothing about production;
* `base` is a general `Credential` in the benchmark statements *because it is one
  in the published ones*; the shapes instantiate it to `.ScriptCredential plc`;
* P2a's postcondition is `seizeStructurePreservedAdaTopUp`, not
  `seizeStructurePreserved`. Mandatory: the ada-EQUALITY version is ❌ FALSIFIED
  against the post-#112 bytecode, with a measured counterexample whose sole defect
  is an ada top-up;
* `P1_model`'s `cs ≠ ByteString.mk ""` (the asset is not ada) is DROPPED — the
  shaped bytecode theorems are `✅ Valid` without it, so carrying it would weaken
  the benchmark for no reason;
* `P1_model`'s `∀ o ∈ outs, validTxOutValue o.txOutValue = true` is subsumed by
  `validRewardingContext ctx`, which the shaped theorems already carry;
* the params hypothesis uses the validator's own INDEXED read
  (`paramsPublishedBy` / `progLogicCredPublishedBySeize`) rather than
  `P1_model`'s ∀-scan `paramsPinned` or `P2_Seize`'s authenticated
  `progLogicCredDataOf`. The scan and the indexed read are INCOMPARABLE in
  general (the scan is vacuously true when no reference input carries the params
  NFT; the indexed read can name a pair another authenticated input contradicts)
  — but UNDER `accept` they coincide, because the validator authenticates
  exactly the input at the redeemer's index. The indexed read is used because
  it mirrors the bytecode's own access pattern, and it keeps §3.1's
  specialisations free of a side condition (`paramsPinned` would need
  `nCS ≠ ppCS` at every P1 shape, `progLogicCredDataOf` would need `pCS = ppCS`).

That `P2a_seizeModel_preserves_structure` is already a KERNEL THEOREM at exactly
this generality is the single most useful fact for judging the benchmark: it shows
the unshaped P2a statement is provable at full generality about *something*, with
no shape and no well-formedness side conditions. What is missing is a route to the
same statement about the compiled program — which is what `#prep_uplc` would give.

### 3.1 The specialisation certificates — the strongest available evidence

`WSC/Benchmark/P1UnshapedStatement.lean` §3 and
`WSC/Benchmark/P2UnshapedStatement.lean` §3–§4 prove, **in the kernel, with no
solver and no `sorry`**, that the unshaped statement instantiates to the shaped
one:

| theorem | gives, at the same `accept` | axioms |
|---|---|---|
| `P1_unshaped_specialises_T1R` | body of `WSC.P1R_T1_stmt` (pure transfer) | `propext, Quot.sound` |
| `P1_unshaped_specialises_T2R` | body of `WSC.P1R_T2_stmt` (**mint/burn**, `q` free) | `propext, Quot.sound` |
| `P1_unshaped_specialises_T6R` | body of `WSC.P1R_T6_stmt` (output aggregation) | `propext, Quot.sound` |
| `P1_unshaped_specialises_T7R` | body of `WSC.P1R_T7_stmt` (aggregation **and** mint) | `propext, Quot.sound` |
| `P2a_unshaped_specialises_S1R` | `WSC.P2a_R_structure`'s conclusion | `propext, Quot.sound` |
| `P2b_unshaped_specialises_S1R` | `WSC.P2b_R_containment`'s conclusion | `propext, Quot.sound` |
| `P2b_unshaped_specialises_S1R2` | `WSC.P2b_R2_containment`'s conclusion (**two token names**) | `propext, Quot.sound` |

and nine `rfl` lemmas (`paramsPublishedBy_T1R/T2R/T6R/T7R`,
`seizedPolicyOf_S1R/S1R2`, `pairedOutputsOf_S1R`,
`progLogicCredPublishedBySeize_S1R/S1R2`) discharge the added hypotheses at every
leaf assignment. Those nine **depend on no axioms at all**.

Note what falls out: ONE unshaped P1 statement covers all four shaped P1 theorems
including both mint shapes, and ONE unshaped P2b statement covers both the
single- and the two-token-name shape. That is direct evidence the form is right —
the shaped family needs four theorems where the unshaped statement needs one.

**The one gap, stated plainly.** §3 abstracts the accept predicate, so it does
not derive the shaped THEOREMS from a hypothetical unshaped theorem. The two
accept predicates are `isSuccessful (appliedGlobalUCeiling.prop ppCS ctx)` and
`isSuccessful (appliedGlobalShapedT1R.prop ppCS <leaves>)`: the same program at
the same budget on the same context, but two different `Optimize.main` outputs,
and this repository has measured that prep residuals are not definitionally
interchangeable (`WSC/Shaped/Probe/BridgeProbe2FAILS.lean`; audit F8;
`docs/LIMITATIONS.md` §5). That gap is pre-existing and
published, not something the benchmark introduces.

### 3.2 What we are and are NOT claiming about the statements' TRUTH

We claim the three statements are **well-formed, non-vacuous at their budgets, and
identical in form to the shaped theorems that are proved**. We do **not** claim
they are true.

They might not be, and if they are not that is a genuine finding rather than a
malformed benchmark. The reason to keep the possibility open is concrete: both
source-model fidelity axioms were REFUTED at wsc-poc `2306678`, so the model and
the bytecode are known to disagree *somewhere*. One disagreement has been located
and is already reflected above — PR #112's ada top-up, which is why P2a's
postcondition is `seizeStructurePreservedAdaTopUp` and not `seizeStructurePreserved`
(the latter comes back ❌ Falsified against production, with a counterexample whose
sole defect is `i0Ada = 23101` against `o0Ada = 36307`). Whether any *further*
divergence shows up once the shape is removed is exactly what this benchmark would
settle, and it cannot be settled by inspection.

So the honest reading of a future run is:

* `✅ Valid` — P1/P2 hold of the production bytecode unshaped. The single largest
  caveat on the whole campaign (docs/LIMITATIONS.md §4, "every result is doubly
  bounded") is gone.
* `❌ Falsified` — there is a real transaction class outside the shapes on which
  the property fails. That is a **security finding about the validators**, and the
  counterexample must be canonicity-checked before it is believed: this repository
  has already retracted one "refutation" whose witnesses were ledger-impossible
  (negative quantities, unsorted token lists — `WSC.P2.counterexample_witnesses_are_not_canonical`).
* `⚠️ Undetermined` — no information. It never admits; the build fails.

---

## 4. The budget: the mainnet ex-unit ceiling, and the non-vacuity floor


### 4.0 THE RUNGS — set at the mainnet ex-unit ceiling

The benchmark's budget is not a tuning knob: a verdict at budget N proves the
property for exactly those accepting runs that fit in N CEK steps. So the rung
that makes the artifact mean *"P1/P2 hold for every transaction mainnet can
carry"* is the mainnet ex-unit ceiling, and that is what both modules are set to.

**Derivation.** From `maxTxExecutionUnits` and the per-step rates measured over
all nine accepting goldens and all four validators (§5.1a and
`WSC/goldens/K-MEASUREMENTS.md` §2, where PCB's metered CEK reproduces the
ledger's own ExBudget **to the unit** — CPU/step 18,132–21,759, mem/step
54.1–56.3):

| limit | budget | ÷ cheapest measured per-step | max CEK steps |
|---|---:|---:|---:|
| CPU | 10,000,000,000 | 18,132 | ≈ 551,500 |
| **memory** | **14,000,000** | **54.1** | **≈ 258,780  ← BINDS FIRST** |

**The memory budget, not the CPU budget, is the binding constraint** — a fact
worth stating on its own, since ex-unit discussions default to CPU. No accepting
run of these validators inside mainnet limits exceeds ≈259k CEK steps.

**Both modules are set to 300,000** = that ceiling plus ≈16% margin, so a step
mix cheaper than any measured golden is still covered. The bound is honest about
its own basis: 54.1 is the *cheapest observed* memory-per-step on this validator
family (band 54.1–56.3, tight across nine goldens, and the two seize goldens are
the two cheapest). A run built from cheaper steps than any measured one would
raise the ceiling; the margin absorbs a 16% drop and no more. Re-derive if
`maxTxExecutionUnits` or the cost model changes.

**The rungs, as coverage of that ceiling.** Each is a real proof obligation
reached by editing the single budget literal on the `#prep_uplc` line:

| rung | budget | coverage | meaning |
|---|---:|---:|---|
| floor | 4,400 / 3,800 | 1.7% / 1.3% | smallest NON-VACUOUS rung (the shaped theorems' own budget). Prep already does not terminate here. **Do not go below.** |
| 2 | 26,000 | 10% | intermediate progress marker |
| 3 | 65,000 | 25% | |
| 4 | 130,000 | 50% | |
| **GOAL** | **300,000** | **100% + margin** | **what both modules are set to: a verdict here IS the property for every transaction mainnet can carry — no shape family, no residual, no budget caveat** |

**Non-vacuity is preserved a fortiori.** Raising the budget only admits more
accepting runs, so every two-sided witness pin in §4 still applies: cheapest
accepting registered transfer 2288, P1's shapes 2343/2567/2777/2567, seize
2301/2412/2739, real goldens 1,453–3,441 and 2,305/2,905 — all ≤ 300,000. The
executable certificates in the two `…Statement.lean` modules certify an accepting
context AT the floor rung and NONE below it; that lower pin is what rules out
vacuity and the raise does not touch it.

**Scale of the ask.** Unshaped prep dies today at ≈3,300 (§5). The goal rung is
300,000. The required improvement is therefore roughly **two orders of
magnitude**, not a constant-factor tune — which is the single most useful number
in this document for deciding whether `prep_uplc` needs an optimization or an
algorithm.

## 5. The measured cost curve

All rows measured on **2026-07-29** in a `cp -a` of the tree, one row = one COLD
re-elaboration of exactly one module (its `.olean` / `.ilean` / `.trace` / `.c`
removed first), dependency oleans warm, `--load-dynlib` supplied by `lake`,
`maxHeartbeats 0`, nothing else competing. Lean 4.24.0, Z3 4.15.2, 32-core box,
61 GB RAM. Command per row:

```
rm -f .lake/build/lib/lean/WSC/<path>.olean .lake/build/lib/lean/WSC/<path>.ilean \
      .lake/build/lib/lean/WSC/<path>.trace .lake/build/ir/WSC/<path>.c
/usr/bin/time -f 'EXIT=%x WALL=%e RSS=%M' timeout -s KILL <cap> lake build <MODULE>
```

**A cap that fires IS the measurement.** `timeout -s KILL` was used, so a killed
row means the elaborator was still inside `#prep_uplc` with no output and no
error when the cap hit.

### 5.1 `programmableLogicGlobal` (transfer), UNSHAPED — `globalInputs1600`

| budget | module | wall | outcome |
|---|---|---|---|
| 600 | `WSC.Prep.Global` | **2.42 s** | completed, 1.24 GB peak RSS |
| 1600 | `WSC.Prep.Global1600` | **217.23 s** | completed, 4.35 GB peak RSS |
| 2600 | `WSC.Benchmark.CostG2600` (temporary) | **> 894 s** | **KILLED at the 15-min cap**, 7.18 GB and still climbing |
| 3300 | `WSC.Benchmark.CostG3300` (temporary) | **> 893 s** | **KILLED at the 15-min cap** |
| **4400** | **`WSC.Benchmark.P1Unshaped`** at its floor rung (module now asks 300000) | **> 894 s** | **KILLED at the 15-min cap**, 8.88 GB and still climbing |

### 5.2 `programmableSeize` (clawback), UNSHAPED — `WSC.seizeInputs`

| budget | module | wall | outcome |
|---|---|---|---|
| 600 | `WSC.Prep.Seize` | **1.75 s** | completed, 1.21 GB peak RSS |
| 2000 | `WSC.Benchmark.CostS2000` (temporary) | **> 892 s** | **KILLED at the 15-min cap** |
| **3800** | **`WSC.Benchmark.P2Unshaped`** at its floor rung (module now asks 300000) | **> 887 s** | **KILLED at the 15-min cap** |

### 5.3 The SHAPED control — same flats, same budgets, same postconditions

| budget | module | wall | note |
|---|---|---|---|
| 4400 | `WSC.Shaped.GlobalShapedP1RPrep` | **1.51 s** | the prep the four proved P1 theorems are stated over |
| 3800 | `WSC.Shaped.SeizeShapedR` | **7.22 s** | shape definitions + prep; P2a/P2b's prep |
| 3800 | `WSC.Shaped.SeizeShapedR2` | **84.11 s** | the two-token-name shape — the most expensive shaped prep in the library |

**This is the whole argument in three numbers: 1.51 s shaped at 4400, against a
15-minute cap firing at 2600.** Shaping is not a small constant factor; it changes
the regime. And note §5.3's last row: shaped preps are *not* uniformly ≈1 s —
S1R2 costs 84 s — so the cheapness comes from the closed `Data` skeleton, not from
the shape being small.

### 5.4 Reading the curve

* The measured points that complete are 600 → 2.42 s and 1600 → 217.23 s for
  global: a factor **90** for a factor 2.7 in budget, i.e. the marginal cost
  doubles roughly every **150** budget steps in that range.
* Extrapolating that slope to 2600 predicts ≈ 5.5 h, and the cap firing at 15 min
  is consistent with it. **We deliberately do not publish an extrapolated cost for
  2600 / 3300 / 3800 / 4400.** This repository's earlier extrapolations
  (`WSC/goldens/K-MEASUREMENTS.md` §5.1a) were shown to be optimistic by 15× in one
  case, because the slope steepens; every such figure is a LOWER BOUND on cost and
  none of them was ever confirmed.
* **VARIANCE IS LARGE and must not be smoothed away.** `WSC.Prep.Global1600` has
  now been measured at **37.8 s**, **44 s**, **271 s**, **594 s** and (this run)
  **217.23 s** on the same class of machine — a 16× spread on one module. The CI
  workflow's own comment records the 271/594 pair and warns against tightening
  timeouts on the strength of one green run. Treat 217 s as a sample, not a
  constant, and treat the killed rows as "not reachable in 15 minutes", which is
  the only claim they support.
* **The nearest wall is at ≈2600 — two orders of magnitude below the goal rung.** Budget 2600 already
  fails, and 2600 is *below* the 2777 needed to cover every P1 witness — though
  above the 2288 minimum. So the first target is not "make the goal rung work", it is
  "make anything at or above 2288 work at all".

### 5.5 Peak memory

`/usr/bin/time` reports the `timeout` wrapper's RSS on a killed row, not the
elaborator's, so the figures for killed rows come from `ps` sampling every 30 s and
are **observations, not peaks** — each was still rising when sampling stopped:

| run | RSS trajectory |
|---|---|
| global @4400 | 3.11 GB @2.5 min → 6.38 @5 min → 7.09 @7.5 min → 7.96 @10 min → 8.62 @11.5 min → **8.88 GB @12.5 min** |
| global @2600 | 6.85 GB @6.5 min → 6.96 @7 min → 7.07 @7.5 min → **7.18 GB @8 min** |

Growth is roughly linear in wall time at ≈200 MB/min once past the first few
minutes, with no sign of a plateau. A 16 GB CI runner would OOM on these before
any of them finished. `WSC.Prep.Global1600` at 4.35 GB is already the peak-RSS
owner of the whole existing build.

---

## 6. What the diagnostics show

Method: `#blaster` options on the goal, at budgets where the prep DOES complete.
`only-optimize: 1` stops after `Optimize.main`; `only-smt-lib: 1` stops after
SMT-LIB translation; `verbose: 1` prints per-phase wall times. Timed with
`lake build`; deps warm.

### 6.1 The phase table

| goal | budget | prep exists? | Optimization | Translation | verdict |
|---|---|---|---|---|---|
| `WSC.P1R_T1_stmt` — the **PROVED SHAPED** theorem (control) | 4400 | yes, ≈1 s | **0.053 s** | **0.008 s** | translates; solves `✅ Valid` in ≈1 s on the normal path |
| `P1UnshapedForm` at `appliedGlobal.prop` | 600 | yes, 2.42 s | **0.246 s** | not reached | `✅ Valid` **in the optimizer** ⇒ VACUOUS |
| `P2aUnshapedForm` at `appliedSeize.prop` | 600 | yes, 1.75 s | **0.245 s** | not reached | `✅ Valid` in the optimizer ⇒ VACUOUS |
| `P2bUnshapedForm` at `appliedSeize.prop` | 600 | yes, 1.75 s | **0.243 s** | not reached | `✅ Valid` in the optimizer ⇒ VACUOUS |
| `WSC.global_vacuity_probe_600` (library's own, no added clause) | 600 | yes | **0.214 s** | not reached | `✅ Valid` in the optimizer ⇒ VACUOUS |
| `P1UnshapedForm` at `appliedGlobal1600.prop`, `only-optimize: 1` | 1600 | yes, 217.23 s | **13.259 s** | skipped | — |
| `P1UnshapedForm` at `appliedGlobal1600.prop`, `only-smt-lib: 1` + `dump-smt-lib: 1` | 1600 | yes | **12.346 s** | **FAILS** | no SMT-LIB emitted |
| same, NORMAL path, `(timeout: 240)` | 1600 | yes | **11.006 s** / **13.219 s** | **FAILS** | build error, no verdict |
| same, params hypothesis DELETED (control) | 1600 | yes | **10.453 s** / **12.762 s** | **FAILS** | identical error |
| `P1UnshapedForm` at `appliedGlobalUCeiling.prop` | 300000 (ceiling) | **no** | not reached | not reached | prep killed at the 15-min cap |
| `P2a/bUnshapedForm` at `appliedSeizeUCeiling.prop` | 300000 (ceiling) | **no** | not reached | not reached | prep killed at the 15-min cap |

Rows 2–3 double as a TYPE CHECK: `P2aUnshapedForm` and `P2bUnshapedForm` are
instantiated at a prep that exists, so the benchmark module's two `def`s are known
to elaborate — the only thing `WSC/Benchmark/P2Unshaped.lean` changes is the prep's
name and budget. The same holds for P1 via row 2 and the `only-optimize` row.

Four things fall out, in increasing order of importance.

### 6.2 The per-goal optimization cost is ~250× worse unshaped

0.053 s shaped at budget 4400 against 10.5–13.3 s unshaped at budget 1600 — and
the unshaped figure is at a *lower* budget. `#prep_uplc` does the bulk of
`Optimize.main`'s work once, at prep time, so this residual per-goal cost is a
direct measure of how much irreducible branching the shape removed. It is also why
adding stanzas to an unshaped module is expensive in a way that adding stanzas to a
shaped one is not.

### 6.3 The SMT-LIB axiom-count metric CANNOT be taken on these goals

`docs/METHOD.md` §2's diagnostic — dump the query and count the quantified
`isList`/`isData` well-formedness axioms, 3–4 shaped versus 14 unshaped — is
inapplicable here, because **no query is produced**. That measurement was taken on
the P4a/P3 unshaped goals, which do translate. It does not extend to P1/P2
unshaped. Recording this so nobody re-derives the 14-axiom figure and attributes
it to these goals.

### 6.4 ⚠️ THE SECOND BLOCKER: the unshaped residual is UNTRANSLATABLE

At budget 1600 — where the unshaped prep terminates — the P1 goal dies in the
TRANSLATION phase, not in the solver and not in the prep:

```
[Start]: Optimization
[End]:   Optimization (11.006000s)
[Start]: Translation
error: translateRecFun: function body expected for
  Lean.Expr.const `PlutusCore.Data.PlutusCore.DataInternal.eqData []
```

**Mechanism.** `PlutusCore.Data.eqData` is declared inside a Lean `mutual` block
with `eqDataList` / `eqDataMap` / `eqDataConstr`
(`PlutusCore/Data/Basic.lean:73-95`; the `BEq Data` instance is at :98-99), so the
surviving constant is the mutual-block internal
`PlutusCore.Data.PlutusCore.DataInternal.eqData`, and
`Blaster/Smt/Translate/Application.lean:672` throws when `getFunBody` returns
`none` for it. Over a SHAPED context the `Data` skeleton is closed, so every
`eqData` application has constructor-headed arguments, the optimizer reduces it to
`equalsByteString` / `equalsInteger` on the leaves, and the constant never reaches
the translator. Over a symbolic `ScriptContext` the arguments are variables and it
survives.

**What was ruled out** (each by a measured control, all in the table above):

1. not the benchmark's added params hypothesis — deleting it changes nothing;
2. not an artefact of `only-smt-lib` — the normal `#blaster` path fails the same
   way;
3. not the postcondition vocabulary — the shaped control uses the same
   `Model.outSum` / `Model.inSum` / `Model.mintSigned` and translates in 8 ms;
4. not the budget as such — at 600 the goal is discharged by the optimizer before
   translation is reached, because 600 is vacuous. The failure appears exactly when
   the accept hypothesis stops being trivially false.

**Consequence for the benchmark, and it is good news.** There are TWO independent
blockers:

* **(BLOCKER-PREP)** the `#prep_uplc` cost wall — §5, the headline;
* **(BLOCKER-TRANSLATE)** this translation gap.

**(BLOCKER-TRANSLATE) can be worked on today, at a 17-second turnaround, with no progress on (BLOCKER-PREP)
at all.** `WSC/Benchmark/EqDataTranslationFAILS.lean` is exactly that reproducer:
both stanzas, the control, the full mechanism in its header, and a banner warning
that budget 1600 is provably vacuous so neither stanza is ever a P1 result.

```
lake build WSC.Benchmark.EqDataTranslationFAILS     # 16.85 s wall, exit 1
```

A benchmark that only exhibited (BLOCKER-PREP) would have been misleading: it would have
suggested that a faster unroller is sufficient. It is necessary, not sufficient.

---

## 7. The upstream issue this corroborates

`input-output-hk/Lean-blaster#138`. The numbers recorded there for the symbolic
CEK unroller — fuel 51 → 5.5 s, fuel 501 → 171 s, fuel 10000 → killed at 628 s,
with the hot path in `CekMachine.runSteps.match_1`, `step.match_3` and
`evalBuiltin.match_1` — are the same shape of curve this benchmark exhibits on a
production validator: super-linear in the fuel/budget with a cliff, and the cost
concentrated in the CEK step dispatch rather than in the solver.

What this artifact adds to that issue:

1. a **real production workload** rather than a synthetic one — the compiled
   `programmableLogicGlobal` (3444 term nodes, 282 builtin occurrences, 46 of
   them CIP-153 `Value` builtins) and `programmableSeize`, both exported from
   `input-output-hk/wsc-poc` `main` @ `2306678`, sha256-pinned in
   `WSC/flats/PROVENANCE.md`;
2. a **real proof obligation on top of it**, so "the prep completed" is not the
   finish line — the residual still has to be translatable and solvable;
3. a **two-sided non-vacuity floor** (§4), so there is a principled answer to
   "how fast is fast enough". A budget below **2288** makes the P1 statement empty
   and below **2301** makes P2 empty; to cover every accepting witness this
   repository has measured you need **2777** (P1) and **2739** (P2), and to cover
   every accepting off-chain GOLDEN you need **3441** (P1) and **2905** (P2).
   Optimising the unroller to, say, budget 2000 buys nothing at all here, because
   the theorem would still be vacuous;
4. an **already-fast control** — the same flats, the same budgets, the same
   postconditions, over shaped contexts: **1.51 s** (global @4400) and **7.22 s**
   (seize @3800), against a 15-minute cap firing at global @2600. Whatever makes
   the shaped case cheap is what the unshaped case is missing, and §6 says what it
   is at the term level: 0.053 s versus 10.5–13.3 s of residual optimization, and
   `eqData` reducing away versus surviving.

---

## 8. Substrate — what these numbers are measured against

* Lean `4.24.0`, Z3 `4.15.2`, `maxHeartbeats 0`, 32-core box, deps warm.
* `Blaster` @ `4d320dd5f70ac953945b5126f5cfd45128da8131`
  (`Anastasia-Labs/Lean-blaster`, branch `wsc-d6-dite-branch-retype`) — public
  `input-output-hk/Lean-blaster` `59db213` plus the one D6 fix
  (`Optimize/Rewriting/OptimizeITE.lean`: rebuild both `Blaster.dite'` branch
  binder types from the final condition). **Without that fix the unshaped global
  prep at 1600 fails in the kernel after ~8 minutes** (defect D8,
  `WSC/IMPACT-PR112.md` §6.2) and the shaped seize prep fails too (D6) — so the
  benchmark cannot even be posed on the unpatched Blaster.
* `PlutusCore` @ `3fdd3fb5cb259f039b60cc584cd954de18c819dc`
  (`Anastasia-Labs/PlutusCoreBlaster`, branch `cip153-value-builtins`) — adds the
  CIP-153 `Value` builtins (flat tags 94–99) and `ScaleValue` (tag 100). Without
  tags 94–99 the global flat does not decode; without `ScaleValue` the seize flat
  does not decode.
* Both pins are full 40-hex SHAs in `lakefile.lean`; `lake update` fetches
  exactly them.
