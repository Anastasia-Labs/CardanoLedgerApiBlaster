# SHAPED-CONTEXT UPLC VERIFICATION — measurement ladder and results (task Z2)

**Headline.** Shaping the `ScriptContext` breaks the Z3 wall that blocked every
UPLC-level property except P3. Two obligations that previously returned **no
verdict** are now **`Valid` theorems against the real compiled bytecode**:

| obligation | before (fully symbolic ctx) | after (shaped ctx) |
|---|---|---|
| **P4a** — an accepted mint runs the token's minting-logic script | `Undetermined`; 296 s / 1,748 s / 3,208 s of Z3 all identical (`WSC/Props/P4_Minting.lean`) | **`✅ Valid` in ≈1 s** — `WSC/Props/Shaped/P4Shaped.lean:121` |
| **P4-burn** — an accepted `BurnOnly` mint is a genuine pure burn | not attempted (weaker P4a already Undetermined) | **`✅ Valid` in ≈1 s** — `WSC/Props/Shaped/P4Shaped.lean:147` |
| **P5** (escape-critical) — accept + `NonMember` ⟹ an authentic directory node covers `cs` | **killed at 5,241 s ≈ 87 min, NO verdict** (`WSC/Props/P5_NonMember.lean`) | **`✅ Valid` in ≈2 s** — `WSC/Props/Shaped/P5Shaped.lean:209` |

Same flats, same budgets (900 and 1600), same postconditions, full control set
(negative control `Valid`, tightness `Falsified`, **vacuity probe at the shape**
`Falsified`), plus a concrete accepting witness of each exact shape run through
the real CEK by `native_decide`. Nothing was weakened except the class of
transactions quantified over, and that class is published in full.

Everything below was measured on 2026-07-25, 32-core box, warm `.lake`,
`maxHeartbeats 0`, **under `lake build`** (never `lake env lean` — see §5),
Lean 4.24.0, Z3 4.15.2, CLAB @ `fc44f3d` + this work, PCB
`cip153-value-builtins` @ `9f9ca8c`, Blaster
`beta-lambda-cache-optimization` @ `59db213`.

---

## 1. What "shaping" means here, precisely

A **shape** is a Lean function `σ : leaves → ScriptContext` whose entire `Data`
SKELETON is closed — every list length, constructor tag, `Option` and nesting
depth fixed — while every SCALAR LEAF (a `ByteString` or an `Integer`) is a free
variable. The prep's inputs function is `… :: purposeInputs (σ leaves)`, so
`#prep_uplc` bakes the skeleton in and the theorem quantifies over the leaves.
Vocabulary and doctrine: `WSC/Shaped/Shape.lean`.

Mechanism used: **(i)** shape inside the `#prep_uplc` inputs function.
Mechanism (ii) (unshaped prep + shape hypotheses) was not used: it leaves the
residual as large as before, which is the opposite of the point.

Why it works: over a symbolic `Data` context every `unConstrData` / `unListData`
/ `headList` / `chooseList` leaves a residual branch, and Z3 must reason about
the validator's whole branch structure. A closed skeleton collapses all of those
at prep time; what reaches the solver is a boolean combination of
`equalsByteString` / `lessThanByteString` / `equalsInteger` over the leaves.

**What shaping costs.** A shaped theorem covers exactly the transaction shapes σ
ranges over. It is honest bounded verification in a SECOND dimension, on top of
the CEK step budget of ADDENDUM E1, and must always be quoted with both bounds.
Every shape's fixed dimensions are listed in the header of its prep module.

**What shaping must not do.** Security-relevant content stays symbolic. In
particular every shape below keeps free exactly the objects its postcondition
talks about — see §3 for the two places where getting this wrong would have made
a theorem true by construction, and §6 for the one place a careless index choice
produced a genuine falsification.

---

## 2. The measurement ladder

### 2.1 Rung 1 — calibration on the already-proven P3 (budget 600)

Purpose: prove the mechanism works end to end before spending it on hard goals.
Files: `WSC/Shaped/BaseShaped.lean` (SHAPE B1),
`WSC/Shaped/Calib/P3Unshaped.lean` (control),
`WSC/Shaped/Calib/P3Shaped.lean`.

| module | stanzas | wall (module, `lake build`) |
|---|---|---|
| `Calib/P3Unshaped` — symbolic ctx | P3 `Valid`, vacuity `Falsified` | **2.4 s** |
| `Calib/P3Shaped` — SHAPE B1 | P3 `Valid`, negative control `Valid`, tightness `Falsified`, vacuity `Falsified` | **1.6 s** |

Prep: unshaped base @600 = **1.2 s** (`WSC/Shaped/Probe/BasePrepUnshaped.lean`),
shaped @600 = **0.95 s**.

Reading: P3 is cheap either way — it was never solver-bound — so rung 1 is a
mechanism check, not a speedup demonstration. It gives 2× more stanzas in 2/3 the
time, and it confirms the two things that had to be true before going further:
the shaped prep elaborates, and **the vacuity probe at the shape is `Falsified`**,
i.e. shaping did not accidentally produce an accept-UNSAT class.

### 2.2 Rung 2/3 — P4a and the BurnOnly scan (budget 900), SHAPE M1

Files: `WSC/Shaped/MintingShaped.lean` (SHAPE M1),
`WSC/Props/Shaped/P4Shaped.lean`.

| obligation | ctx | Z3 cap | outcome | wall |
|---|---|---|---|---|
| P4a | symbolic | 300 s | `Undetermined` | 296 s |
| P4a | symbolic | 3,300 s | `Undetermined` | 3,208 s |
| P4a | symbolic | uncapped | `Undetermined` (killed) | >1,748 s |
| vacuity probe @900 | symbolic | 3,300 s | `Undetermined` | 3,207 s |
| **P4a** | **SHAPE M1** | 300 s | **`✅ Valid`** | **≈1 s** |
| **P4-burn** (`mintPos = false`) | **SHAPE M1** | 300 s | **`✅ Valid`** | **≈1 s** |
| **`BurnOnlyOk`** (arm 4 of P4) | **SHAPE M1** | — | **`✅ Valid`** | ≈1 s |
| negative control | SHAPE M1 | — | `✅ Valid` | ≈1 s |
| tightness | SHAPE M1 | — | `✅ Falsified` (expected) | ≈1 s |
| **vacuity probe @900** | **SHAPE M1** | — | **`✅ Falsified`** (non-vacuous) | ≈1 s |

The three symbolic-context rows are quoted from `WSC/Props/P4_Minting.lean`'s
SOLVER COST table (measured in task Y2); the shaped rows were measured here.
Whole shaped module including four `native_decide` witnesses: **3.5 s**.

Prep: minting @900 unshaped = 1.5 s, shaped = **0.88 s**.

### 2.3 Rung 4 — P5, the escape-critical property (budget 1600), SHAPE G1

Files: `WSC/Shaped/GlobalShaped.lean` (SHAPE G1),
`WSC/Props/Shaped/P5Shaped.lean`.

| obligation | ctx | Z3 cap | outcome | wall |
|---|---|---|---|---|
| P5 indexed + controls | symbolic | uncapped | **no verdict** (killed) | 5,241 s |
| vacuity probe @1600 | symbolic | uncapped | **no verdict** (killed) | 5,241 s |
| vacuity probe @1600 | symbolic | 120 s | `Undetermined` | 120 s |
| **P5 indexed** | **SHAPE G1** | — | **`✅ Valid`** | **≈2 s** |
| negative control | SHAPE G1 | — | `✅ Valid` | ≈2 s |
| tightness | SHAPE G1 | — | `✅ Falsified` (expected) | ≈2 s |
| **vacuity probe @1600** | **SHAPE G1** | — | **`✅ Falsified`** (non-vacuous) | ≈2 s |

The symbolic rows are quoted from `WSC/Props/P5_NonMember.lean`'s OBLIGATION
STATUS table (task Y1). Whole shaped module including the composition corollaries
and the concrete witness: **2.3 s**.

Prep: global @1600 unshaped = **51 s** (re-measured this session), shaped =
**1.2 s** (42×).

The shaped bytecode rung then composes with the reduction ladder that
`WSC/Props/P5_NonMember.lean` already proved, giving two further theorems in
`WSC/Props/Shaped/P5Shaped.lean`:

* `P5_shaped_exists` — ADDENDUM E3's **∃-form** postcondition ("the transaction
  really references an authentic covering directory node"), via
  `P5_exists_of_indexed`;
* `P5_shaped_groundtruth` — the same in `WSC/Honest.lean`'s vocabulary
  (`authenticDirNode`, full 5-field `dirNodeKey`/`dirNodeNext`), via
  `P5_groundtruth_of_indexed`, consuming exactly one extra assumption, `TS3`.

### 2.4 Loosening rung — are concrete redeemer indices load-bearing?

The task's doctrine permits fixing the redeemer's index fields. Measured answer
for the minting policy: **no, they are not needed.**

| shape | difference from M1 | outcome |
|---|---|---|
| **M2** (`WSC/Shaped/MintingShapedIdx.lean`) | `pboMintingLogicWdrlIdx` a free `Integer` | P4a **`Valid`**, P4-burn **`Valid`**, negative control `Valid`, tightness + vacuity `Falsified` — **2.1 s** (`WSC/Props/Shaped/P4ShapedIdx.lean`) |

So for the issuance policy the SMT wall is broken by fixing the `Data` SKELETON
alone. `WSC/Props/Shaped/P4ShapedIdx.lean` therefore SUPERSEDES the M1 theorems
in strength; `P4Shaped.lean` is kept for the concrete witness, the arm-scope
discussion and the control set.

For the global validator the analogous loosening splits (see §6):

| shape | difference from G1 | outcome |
|---|---|---|
| **G2** | BOTH `paramsRefIdx` and the `NonMember` node index free; postcondition index-free (`hasCoveringNode`) | **`❌ Falsified`** with a genuine counterexample (§6) — 6.6 s |
| **G3** | node index free, `paramsRefIdx` pinned to 0; postcondition index-free (`hasCoveringNode`) | main obligation **`⚠️ Undetermined`** after a 906 s Z3 query; vacuity probe at the shape **`✅ Falsified`** (so the class is NON-empty — this is a solver limit, not an empty shape). Module wall 14 m 38 s. See §6.2 |

So the two validators differ: for the ISSUANCE policy the concrete redeemer index
is dispensable, for the GLOBAL validator it is load-bearing.

### 2.5 Prep-cost ceiling — shaping also removes the prep wall

`WSC/goldens/K-MEASUREMENTS.md` §5.1 reports symbolic `#prep_uplc` cost growing
exponentially in the BUDGET with a cliff (minting never completed at 2000; seize
never at 2000 or 9000). Shaped preps are **essentially budget-independent**:

| validator | budget | unshaped prep | shaped prep |
|---|---|---|---|
| base | 600 | 1.2 s | 0.95 s |
| minting | 900 | 1.5 s | **0.88 s** |
| minting | 1700 | 92.7 s | **1.2 s** |
| minting | 2000 | **never completed** (killed at 1,800 s) | — |
| minting | 2500 | — | **1.3 s** |
| global | 1600 | **51 s** | **1.2 s** |
| global | 2500 | — | **1.2 s** |
| global | 4000 | — | **1.3 s** |

Probe files: `WSC/Shaped/Probe/{MPrep1700,MPrep2500,GPrep2500,GPrep4000}.lean`.

Explanation: with a closed skeleton the symbolic run follows ONE concrete
control-flow path and halts well inside the budget, so raising the budget adds
nothing to the residual. **This matters beyond Z2:** the budgets P1 (K = 3,262 /
3,726), P2 (K = 2,570) and P6 need — previously extrapolated at "7 to 182 years"
of prep (K-MEASUREMENTS §5.2) — are now 1.3 s of prep away. Whether their
*postconditions* close is untested; the prep barrier that made them
"NOT-REACHABLE-AT-UPLC" is gone.

---

## 3. Why the shaped theorems are not true by construction

Two places where a lazy shape would have handed over the postcondition, and what
was done instead.

**P4a / SHAPE M1.** The conclusion is about the withdrawal map. SHAPE M1 fixes its
LENGTH (2) and that both entries are script credentials, but both script HASHES
`w0`, `w1` are free variables, and `validMintingContext` constrains them only to
be sorted. So "the minting-logic credential is in the map" is earned from the
bytecode. Likewise SHAPE M1 carries an OUTPUT holding the policy's own token, so
the ledger balance rule admits `q = qOut − qIn > 0`: a `q > 0` shape-M1 context is
ledger-valid, and `P4_burn_only_shaped` says the bytecode rejects it. Had the
shape had no output, `q < 0` would have been forced by the balance rule and the
theorem would have been hypothesis-implied.

**P5 / SHAPE G1.** The conclusion has two conjuncts and both are free:

* `coversCS cs node` = `key < cs && cs < next`, with `key`, `next`, `cs` three
  independent free variables;
* `dirNodeAuthH dirCS node` = `nCS == dirCS`, where `nCS` is the directory node's
  first non-ada value policy and `dirCS` is the policy published by the params
  datum. **These are DIFFERENT variables.** A shape that reused one variable for
  both would have made this conjunct `rfl`-true and half of P5 vacuous.

The params node's own authentication is likewise not pre-satisfied: its first
non-ada policy `pCS` is a different variable from the script parameter `ppCS`, so
`pparamsAtRefIdx`'s `phasCSH` gate (ProgrammableLogicBase.hs:832) has to be
cleared by the accept path.

`WSC/Props/Shaped/P5Shaped.lean`'s `§P5 hypothesis audit` additionally proves, by
`rfl`, that SHAPE G1 satisfies every hypothesis of
`P5_nonmember_covering_node_indexed` with `pIdx = 0`, `nodeIdx = 1`,
`paramsIn` = reference input 0, `node` = reference input 1 — so the shaped
theorem is that statement specialized, not a different one.

---

## 4. Concrete witnesses — non-vacuity without the solver

Both shapes carry a fully concrete accepting instance, executed by the real CEK
machine and closed by `native_decide`.

| | SHAPE M1 witness | SHAPE G1 witness |
|---|---|---|
| where | `WSC/Props/Shaped/P4Shaped.lean` `P4ShapedWitness` | `WSC/Props/Shaped/P5Shaped.lean` `P5ShapedWitness` |
| `validXContext` | `true` | `true`, and CLAB's per-conjunct report lists **zero** failures |
| accepted by real bytecode | at 900 (shaped exec) and 800 (unshaped exec) | at 1600 (shaped **and** unshaped exec) |
| rejected (budget) | at 600 | at 600 |
| **exact K** | **784** | **1541** |

`K = 784` is *exactly* the measured step count of the off-chain golden
`programmableTokenMinting.mint-burnonly` (K-MEASUREMENTS §3) — the shape
reproduces the real transaction's cost to the step. `K = 1541` sits 13 steps
below the cheapest accepting global golden (1554).

Both K values were obtained by binary search over `cekExecuteProgram`
(`WSC/Shaped/Probe/{M1K,G1K}.lean`) and `K = 1541` is pinned as a theorem
(`P5ShapedWitness.K_is_1541`: halts at 1541, budget-errors at 1540).

### 4.1 Excluded-case witness — the positive-mint case is real, and rejected

`P4_burn_only_shaped` ("an accepted `BurnOnly` mint has no positive quantity of
its own policy") is only interesting if a shape-M1 context WITH a positive mint is
ledger-valid at all. It is, and the bytecode rejects it —
`WSC/Props/Shaped/P4Shaped.lean` `P4ShapedWitness.ctxPos_valid_and_positive` and
`exec_rejects_positive_mint`:

| leaf assignment | `validMintingContext` | `mintPos` | real CEK @900 |
|---|---|---|---|
| mint **+3** of `OWNCS.TOK`; input holds 2, output holds 5; 100 lovelace in, 60 out, 40 fee | `true`, **zero** failing conjuncts | `true` | **REJECT** |

This is a sharper control than the tightness stanza: tightness only says some
accepting context satisfies the postcondition, whereas this exhibits the specific
ledger-legal context the postcondition EXCLUDES and shows the real CEK rejecting
it. Without it, "accept ⟹ pure burn" could have been hypothesis-implied.

**Note on D3 (updated after task Z5).** When Z2 ran, all 13 goldens failed
`validXContext` (`txInfoFee = 0` plus the CLAB order defects, `WSC/STATUS.md` §3
D3), so the SHAPE G1 witness was then the ONLY fully-normalized accepting
`ScriptContext` in the repo for the global validator. Task Z5 has since fixed the
upstream builder and re-dumped the goldens, and D3 is CLOSED — all 9 accepting
goldens now satisfy their matching `validXContext`. The shaped witnesses are
therefore no longer unique in that respect; what they still add is (a) an
accepting instance of the EXACT shape the theorems quantify over, and (b) for
P5, a genuine MINT-side `NonMember` claim, which no golden exercises (§2.3).

---

## 4.2 Axiom audit — what the shaped theorems actually rest on

`#print axioms` on every shaped theorem (`WSC/Shaped/Probe/Axioms.lean`):

| theorem | axioms |
|---|---|
| `P3_base_requires_global_or_seize` (pre-existing baseline) | `propext, sorryAx, Classical.choice, Quot.sound` |
| `P4a_shaped_mint_runs_minting_logic` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `P4_burn_only_shaped` | same |
| `P4a_shapedIdx_mint_runs_minting_logic` (SHAPE M2) | same |
| **`P5_shaped_indexed`** | same |
| `P5_shaped_exists` | same |
| `P5_shaped_groundtruth` | same **+ exactly `WSC.Deployed, WSC.OnChain, WSC.TS3`** |
| `P5.nthFrom_mem` (pure reduction lemma) | `propext` only |
| `P5ShapedWitness.exec_accepts_at_1600`, `K_is_1541`, `P4ShapedWitness.exec_rejects_positive_mint` | `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler` (no `sorryAx`) |

Three things to read off this table:

1. **No `WSC/Honest.lean` axiom is used by any shaped bytecode theorem.** The only
   WSC axioms anywhere in the layer are the three the ground-truth corollary
   advertises, and `#print axioms` confirms there is nothing else hiding.
2. **`sorryAx` is `blaster`'s `admit`**, not a gap left by this task: it appears
   identically on the pre-existing, reviewed `P3_base_requires_global_or_seize`
   (SPIKE-FINDINGS: "Valid closes via `admit`, so every blaster-proved theorem
   carries a `declaration uses 'sorry'` warning"). Contrast the source-model route
   (tasks Z3/Z4), whose theorems are `sorry`-free but carry a `<model>_faithful`
   transcription axiom instead. **The two routes trade different things:** shaped
   theorems trust the solver+`admit` pipeline and the shape; source-model theorems
   trust a hand transcription. Neither dominates; a reviewer should know which
   they are reading.
3. The concrete witnesses depend on `native_decide`'s `ofReduceBool` /
   `trustCompiler` and NOT on `sorryAx` — they are independent of both the solver
   and `admit`.

## 5. Methodology warnings (both re-confirmed here)

1. **Always time with `lake build`, never `lake env lean`.** The latter passes no
   `--load-dynlib`, so Blaster's precompiled `libBlaster.so` runs interpreted.
   Re-confirmed: unshaped base prep @600 is **1.2 s** under `lake build` against
   the 11 s recorded from `lake env lean`. `WSC/goldens/K-MEASUREMENTS.md` §5.1's
   prep-cost table remains 15–53× pessimistic and should be read only for its
   shape, not its numbers.
2. **`#prep_uplc` needs `maxHeartbeats 0`** and is not covered by
   `(timeout: n)`, which caps Z3 only.
3. `blaster` closes `Valid` goals via `admit`, so every proved theorem carries a
   `declaration uses 'sorry'` warning; the shaped modules set
   `warn.sorry false` as the rest of the tree does.
4. `#prep_uplc <name>` defines a ROOT-level constant, not one inside the
   surrounding `namespace`. `open WSC (appliedX)` fails; write `appliedX`.

---

## 6. The one falsification, and what it teaches

### 6.1 SHAPE G2 — free `paramsRefIdx` breaks the postcondition's NAMING

Over SHAPE G2 (both redeemer indices free, index-free postcondition
`accept ⟹ hasCoveringNode dirCS cs refInputs`) `blaster` returned
**`Falsified`** in 6.6 s with the counterexample (probe:
`WSC/Shaped/Probe/G2Probe.lean`; abridged assignment):

```
pIdx = 1, nIdx = 1
ppCS = "\x00",  pCS = "\x00",  nCS = "\x00"
dirCS = "",     key  = "\x00", next = "\x1b21d",  cs = "\x2000"
q = 1, inAda = 2, outAda = 1, qOut = 1, fee = 1
```

**This is not a validator defect.** With `paramsRefIdx = 1` the validator
resolves its protocol-params UTxO at reference index 1 — the *directory node* —
authenticates it with `phasCSH ppCS` (which passes because `nCS = ppCS` here) and
then reads position 0 of THAT datum as `directoryNodeCS`. So the policy the
bytecode authenticated the node against is `key`, while the postcondition's
`dirCS` came from the params datum at reference index 0, which the validator never
read. The theorem named the wrong object.

Two consequences worth keeping:

* it is a positive argument for the INDEXED form of P5 that
  `WSC/Props/P5_NonMember.lean` already uses: `dirCS` must be named through the
  redeemer's own `paramsRefIdx`, never through a chosen reference position;
* on chain the counterexample is excluded by `TS2` (params-NFT uniqueness,
  `WSC/Honest.lean`), which is deliberately NOT available to a bytecode theorem.

It is also a live demonstration that the shaped setting has real refutation
power: the same solver that gives no verdict on the symbolic context produced a
concrete counterexample here in seconds.

### 6.2 SHAPE G3 — free node index, pinned params index

G3 keeps `paramsRefIdx = 0` (so reference input 0 IS the params UTxO the
validator reads) and frees only the `NonMember` node index, with the index-free
`hasCoveringNode` postcondition. Prep: 1.2 s. Measured
(`WSC/Shaped/Probe/G3Probe.lean`, `lake build`, Z3 capped at 900 s per query):

| stanza | outcome | wall |
|---|---|---|
| index-free P5 at SHAPE G3 | **`⚠️ Undetermined`** | 906 s (the Z3 cap fired) |
| vacuity probe at SHAPE G3 | **`✅ Falsified`** | — |
| module total | — | 14 m 38 s |

Read the two rows together: **the shape class is NOT empty** — accepting shape-G3
contexts exist inside 1600 steps — so this is a genuine solver limit, not a
vacuous class. The mechanism is visible in the term: the symbolic `dropList`
inside the mint walk's `PNonMember` branch (ProgrammableLogicBase.hs:998) puts
the branch structure back into the residual, which is exactly what shaping was
removing. So for the GLOBAL validator the concrete node index IS load-bearing,
in contrast to the minting policy (§2.4), where SHAPE M2 closes in 2.1 s with its
index free.

Recorded as an open issue, not a property failure: `P5_shaped_indexed` at SHAPE
G1 stands, and the honest reading is that P5 is proved for the node index the
redeemer actually witnesses, one index at a time. Enumerating the (finite,
shape-bounded) index range as separate shapes would close the gap mechanically
and is the obvious next step.

---

## 7. Where this leaves the campaign

| property | state before Z2 | state after Z2 |
|---|---|---|
| P3 | PROVEN-AT-UPLC (K=600), symbolic ctx | unchanged; additionally proven over SHAPE B1 |
| P4a | statement + measured `Undetermined` | **PROVEN-AT-UPLC over SHAPE M1 and M2 (K=900)** |
| P4 (arm 4 / `BurnOnlyOk`) | statement only | **PROVEN-AT-UPLC over SHAPE M1 and M2 (K=900)** |
| P4 (arms 1–3) | unreachable at 900 | unchanged (need K ≥ 1,257 / 1,681 — now prep-affordable, §2.5, but no shape written) |
| P5 | statement + reduction ladder; bytecode rung had NO verdict | **PROVEN-AT-UPLC over SHAPE G1 (K=1600)**, plus the ∃-form and ground-truth corollaries |
| P1, P2, P6 | NOT-REACHABLE-AT-UPLC (prep extrapolated at years) | **prep barrier removed** (§2.5); shapes and postconditions not attempted |

### Honest limits of what was achieved

1. Every new theorem is bounded twice: by its CEK budget AND by its shape. A
   shaped theorem is a statement about a named finite family of transaction
   shapes. It is not a statement about all transactions, and the composition
   layer cannot use it as one without a shape-coverage argument that does not
   exist yet.
2. P5's strength is still exactly `DirWF`'s strength (ADDENDUM E4). Nothing here
   touches U10.
3. Defect D1 (`validRedeemerMap` order) is dodged, not fixed: SHAPE M1/M2 have a
   ONE-entry redeemer map, so they are sorted under either order — but that is
   precisely the mixed spending+minting map that every real programmable-token
   mint carries. A 2-entry shaped redeemer map would hit D1 head on.
4. The three `Local` / `DelegateTransfer` / `DelegateSeize` arms of P4 are still
   unexercised, and P1 / P2 / P6 are untested at any shape.
5. **P5 is proved one node index at a time.** Freeing the `NonMember` node index
   (SHAPE G3) returns `Undetermined` after 906 s even though the shape class is
   non-empty (§6.2). SHAPE G1 pins it at 1. Enumerating the index range as
   separate shapes is mechanical but was not done.
5. Substrate reproducibility caveat E11 is unchanged: the global validator's flat
   decodes only against the unpushed PCB branch `cip153-value-builtins`.

### What to do next, in order

1. **Shape the remaining arms of P4** at budget 1700 (prep is 1.2 s):
   `Local` (K = 1,681) is the one that would make the no-escape custody scan a
   theorem rather than an assumption.
2. **Attempt a shaped P1** — one mini-ledger input, one mini-ledger output, one
   policy, one token name, `Member` proof, budget 3,300. Prep is affordable now;
   the open question is whether the containment subtract-walk's residual is
   solver-tractable at a fixed spine.
3. **Attempt a shaped P2** (seize, K = 2,570), which the E2 spike abandoned for
   prep reasons that no longer apply. NOTE: E2 reported that shaping SPINES alone
   did not make seize's prep complete at 3000/9000; the difference here is that
   the SKELETON is closed all the way down to scalar leaves, including datums and
   the redeemer — E2's shaped inputs fn left those symbolic `Data`.
4. **A shape-coverage argument**, or the honest alternative: publish the shaped
   results as a *bounded model-checking* layer beneath the axiomatic one, and
   state in `WSC/Honest.lean` which axioms they replace ON THEIR SHAPES only.
5. Fix D1/D2 in CLAB so shaped theorems can use realistic multi-entry redeemer
   maps.

---

## 8. Reproduction

```
cd <CLAB checkout>

# rung 1 — calibration on P3
lake build WSC.Shaped.Calib.P3Unshaped     # 2.4 s: Valid + Falsified
lake build WSC.Shaped.Calib.P3Shaped       # 1.6 s: Valid, Valid, Falsified, Falsified

# rung 2/3 — P4a + BurnOnly over SHAPE M1 / M2
lake build WSC.Props.Shaped.P4Shaped       # 3.5 s
lake build WSC.Props.Shaped.P4ShapedIdx    # 2.1 s

# rung 4 — P5 over SHAPE G1
lake build WSC.Props.Shaped.P5Shaped       # 2.3 s

# exact step counts of the two concrete witnesses (784 and 1541)
lake build WSC.Shaped.Probe.M1K
lake build WSC.Shaped.Probe.G1K

# the G2 falsification, with counterexample
lake build WSC.Shaped.Probe.G2Probe

# the G3 negative result (Undetermined at 906 s; vacuity probe Falsified) — 15 min
lake build WSC.Shaped.Probe.G3Probe

# axiom audit of every shaped theorem
lake build WSC.Shaped.Probe.Axioms

# prep-cost ceiling sweep
lake build WSC.Shaped.Probe.MPrep1700 WSC.Shaped.Probe.MPrep2500 \
           WSC.Shaped.Probe.GPrep2500 WSC.Shaped.Probe.GPrep4000

# everything, including the pre-existing tree
lake build WSC
```

File map:

```
WSC/Shaped/Shape.lean             shaping vocabulary + doctrine
WSC/Shaped/BaseShaped.lean        SHAPE B1  (base spend, budget 600)
WSC/Shaped/MintingShaped.lean     SHAPE M1  (issuance BurnOnly, budget 900)
WSC/Shaped/MintingShapedIdx.lean  SHAPE M2  (= M1, symbolic withdrawal index)
WSC/Shaped/GlobalShaped.lean      SHAPE G1  (transfer, mint-side NonMember, budget 1600)
WSC/Shaped/GlobalShapedIdx.lean   SHAPE G2 / G3 (symbolic indices)
WSC/Shaped/Calib/*.lean           rung-1 calibration pair
WSC/Shaped/Probe/*.lean           exploration probes, K measurements, prep sweep,
                                  the G2 falsification, the G3 negative result and
                                  the `#print axioms` audit
WSC/Props/Shaped/P4Shaped.lean    P4a + BurnOnly at M1, controls, concrete witness
WSC/Props/Shaped/P4ShapedIdx.lean P4a + BurnOnly at M2 (supersedes in strength)
WSC/Props/Shaped/P5Shaped.lean    P5 at G1, controls, corollaries, concrete witness
```
