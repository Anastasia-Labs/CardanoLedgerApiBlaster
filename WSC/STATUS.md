# WSC containment campaign — AUTHORITATIVE STATUS

**Read this first, then `WSC/AUDIT.md`.** Everything below is machine-checked or
measured *in this repository*, with the file/line or the measurement cited. Where a
result is not there yet, this table says so in those words.

**AMENDED BY TASK A1 (2026-07-25).** The U3 body below is unchanged except where a
row became FALSE; every A1 change is collected in **§0.0** and cross-marked
`(A1)` in the row it touches. A1 was mechanical restatement plus five non-vacuity
theorems — it moved nothing in the top-claim column, and §0.0 says so first.

**This revision (2026-07-25, task U3) was reconciled against an independent
clean-room rebuild, not against the task fragments that claimed the results.** All
six `WSC/status-fragments/*.md` are merged here and superseded; they remain as the
per-task record. Any disagreement between a fragment and this file is resolved in
favour of this file, and the disagreements are itemised in `WSC/AUDIT.md` §7.

* Top claim being pursued (plain English): *in an honest deployment, programmable
  tokens cannot exist outside the mini-ledger (the `programmableLogicBase` payment
  credential).*
* Status of that claim in one sentence: **NOT PROVED — machine-checked REDUCTION
  to four named leaf obligations plus 26 project axioms** (`WSC/Composition.lean`
  `top_claim`; axiom list in `WSC/AUDIT.md` §3.1). The `LeafSet` bundle it consumes
  is **never constructed** anywhere in the library.
  **(A2) AMENDED:** a `LeafSet` term now exists —
  `WSC.Composition.containedLeaves` — and `containment_on_contained_class` is the
  top claim with no `LeafSet` hypothesis, but only over the `ContainedTx` class
  (§0.0a), whose defining property is that containment holds of it for ACCOUNTING
  reasons; no UPLC result is used, and for the general class the sentence above
  still stands. A2 also proved that instantiating `Shape` with a SHAPED class gives
  a theorem about an EMPTY class (§0.0a item 2).
* Method: leaf properties proved `by blaster` against the **actual compiled
  production UPLC bytecode**, under a per-validator **CEK step budget** and — in
  the shaped layer — over a fixed `Data` **shape**; a composition theorem lifts the
  leaves; a closed, audit-mapped axiom set (`WSC/Honest.lean`,
  `WSC/Composition.lean`) carries "honest deployment" + "trust the Cardano ledger".
* Verified state of the build at U3: **401 jobs, 93.7 s wall, 98 solver verdicts
  (64 `✅ Valid` + 34 `✅ Expected Falsified`), 0 `⚠️`, 0 `❌`, 0 errors, 21 expected
  `sorry` warnings** (`WSC/AUDIT.md` §1-§2).
  **(A1) AFTER TASK A1: 404 jobs, 79.8 s wall, 101 solver verdicts (66 `✅ Valid` +
  35 `✅ Expected Falsified`), 0 `⚠️`, 0 `❌`, 0 errors, 20 expected `sorry`
  warnings.** The delta reconciles exactly: **+4** from the new
  `WSC/Props/P3_BaseRun.lean` (3 Valid + 1 Expected Falsified) and **−1** because
  `Composition.mintingNonVacuous` no longer calls `blaster` (which also removes its
  `sorry` warning, 21 → 20).
* Companion documents: `WSC/AUDIT.md` (the five censuses and what not to believe),
  `WSC/ARCHITECTURE.md` (binding; ADDENDUM v3 overrides the base text),
  `WSC/SHAPING-RESULTS.md`, `WSC/SHAPE-BRIDGE.md`, `WSC/SPIKE-FINDINGS.md`,
  `WSC/LR-CTX-AUDIT.md`, `WSC/goldens/K-MEASUREMENTS.md` (**read §0.5 below before
  believing its §5.1 prep numbers**).
* HEAD when the U3 body was written: `a8d95a7` on `wsc-containment-proofs`;
  task A1 started from `54a6545` on the same branch.

## 0.0 TASK A1 — what changed, and what deliberately did not

**THE ONE-LINE ANSWER: the composition is now wired to the kernel-checked bridge
instead of to a solver verdict, every non-vacuity obligation in the library is
discharged, and the top claim is exactly as open as it was.** `top_claim` still
consumes an un-instantiated `LeafSet` (audit **F1**), still depends on the SAME 26
project axioms (re-measured, list identical), and still carries `sorryAx`
(audit **F4**). Shape coverage (audit **F2**) is untouched. A1 closed the audit's
mechanical findings; it closed none of its critical ones.

WHAT CHANGED:

| # | change | audit finding |
|---|---|---|
| 1 | The four `LR_BUDGET_*` axioms are restated against **`Runs.XRun K`** (new leaf module `WSC/Runs.lean`) instead of `appliedX_K.prop`. The right-hand side is now a plain Lean definition — imported flat + audited `WSC/Prep` inputs fn + `cekExecuteProgram` — so the connective from a shaped theorem to the ledger side is `ShapeBridge.exec_<S>`, a kernel-checked `rfl` with no `sorryAx`, rather than a `blaster` verdict. | **F3 HIGH — CLOSED** |
| 2 | **`GlobalPreppedAt` DELETED.** It was U2's abstract "the term you handed me really is the prep of that flat at that budget" side condition; `Runs.globalRun K` exhibits flat, inputs fn and budget in its own definition. `WSC/Honest.lean` 38 → 37 axioms; library 51 → 50. | F3 sub-item — CLOSED |
| 3 | **All five open non-vacuity obligations DISCHARGED** as theorems, `native_decide` on the real CEK, **no `sorryAx` and no project axiom**: `GlobalNonVacuous` at 1600 / 3300 / 4400, `SeizeNonVacuous` at 3800, `MintingNonVacuous` at 2500 (`WSC/Props/Shaped/NonVacuity.lean`). With `Composition`'s base/minting-900 pair the set is COMPLETE. | **F7 — CLOSED**, and more |
| 4 | **Three new published K constants**, each ≥ a named witness's measured accepting step count: `K_mint_custody = 2500` (L1, K=1681), `K_global_member = 3300` (G6, K=2837), `K_seize = 3800` (S1, K=3004). `K_seize` REVERSES a "DELIBERATELY UNAVAILABLE" entry — the reasoning behind it was about `#prep_uplc` cost and does not apply to a run term. | F12 last bullet — CLOSED |
| 5 | **P3 restated on the run term** (`WSC/Props/P3_BaseRun.lean`, `✅ Valid`, with its own vacuity probe `✅ Expected Falsified` **at the run term**), so `Composition.p3_lifted` mentions no `#prep_uplc` output and `PropExecFaithful` is off the keystone path. | F8 — narrowed, not closed |
| 6 | `baseNonVacuous` and `mintingNonVacuous` no longer carry `sorryAx`: their accept component is now a `native_decide` witness on the term the predicate names, not a `blaster` verdict on a `.prop`. | — |
| 7 | **K-MEASUREMENTS §5.1's prep table marked SUPERSEDED with a re-measured §5.1a.** Measured with `lake build`, cold, one module at a time: base 600 = **1.35 s**, minting 900 = **1.53 s**, global 1600 = **37.8 s** against **2,143 s** published — 6–58× overstatement, cause = `lake env lean` without `--load-dynlib`. | **F5 — CLOSED** |
| 8 | `WSC/Props/P5_Witness1600.lean` given a banner naming what is and is not a theorem, and its two `#eval` facts PROMOTED to `native_decide` theorems so the file can be cited safely at all. | **F11 — CLOSED** |

WHAT DELIBERATELY DID NOT CHANGE, and each is a decision a reviewer may disagree
with:

* **`WithinBudget` still quotes only `K_base` / `K_mint` / `K_global`.** The 2500
  minting bridge now exists, but consuming it widens `HonestTx`, which strengthens
  `top_claim`'s statement and correspondingly hardens its OPEN `LeafSet`
  obligations. That is a change to the composition's core transaction class, not a
  restatement. Recorded at `K_mint_custody` and `Composition` §5.
* **No `LeafSet` value is constructed.** A1 added none of the four fields.
* **`PropExecFaithful` still binds the SHAPED layer.** Every shaped P-theorem is
  still stated on `appliedXShaped.prop` and reaches the ledger via
  `ShapeBridge.bridge_<S>` (Tier B, `blaster`, health warning in
  `SHAPE-BRIDGE.md` §5.2). A1 removed it from ONE path and MEASURED that the same
  removal works at keystone grade; the other 14 theorem groups (and 14 fresh vacuity
  probes) are real work and were not done.
* **Nothing about shape coverage.** Audit F2 stands verbatim.
* **The seize bridge now exists and is used by nothing.** `LeafSet.p2` is open,
  `WithinBudget` has no seize clause, and 3800 does not cover the 2-input accepting
  seize golden (4,647 steps).

MEASUREMENT DISCREPANCY REPORTED, not silently corrected: `WSC/AUDIT.md` §2
publishes "**47** `axiom` declarations — `Honest.lean` (35), `Composition.lean`
(10), `P1_Transfer.lean` (1), `SeizeModel.lean` (1)". At the audited revision
`grep -c '^axiom '` gives **51** — Honest **38**, Composition 10, P1_Transfer **2**,
SeizeModel 1. The audit's per-file split and its central conclusion ("no `axiom`
hides in any `Prep/*`, `Shaped/*` or `Props/Shaped/*` module") both reproduce; only
the totals are 4 low. After A1: 50 / 37 / 10 / 2 / 1.

## 0.0a TASK A2 — a `LeafSet` exists; and the shaped classes are EMPTY

**Read this before anything below that says "the `LeafSet` bundle is never
constructed".** Task A2 (2026-07-25) actioned audit finding **F1**. Two results, and
the second is the more important one.

1. **A `LeafSet` term now exists and the top claim is instantiated at it** —
   `WSC.Composition.containedLeaves : LeafSet hp (ContainedTx hp)` (§11 of that
   file), all four fields PROVED, and
   `WSC.Composition.containment_on_contained_class` is `top_claim` with **no
   `LeafSet` hypothesis**. `#print axioms containedLeaves` carries **no `sorryAx`,
   no `blaster` verdict, no `<model>_faithful` axiom and no `native_decide`**.
   THE CLASS: transactions no output of which sends a non-ada policy off-base
   (`InertOffBase`) and which produce no directory node (`NoRegistration`).
   Everything else is free — inputs, outputs, mint/burn, spending of mini-ledger
   UTxOs, redeemer, withdrawals, quantities. The class is proved INHABITED, by a
   transaction that really moves 5 `MMM.TOK` at a base output
   (`containedTx_witness`, `contained_witness_moves_tokens`).
   **THE HONEST LIMIT:** the class excludes exactly the transactions for which
   containment is a property of the BYTECODE, so the four fields are discharged from
   `LR_BALANCE_SLOT` + `WSC.NONNEG` + the class definition and **no UPLC result is
   used**. What is now closed end to end is the LEDGER-LEVEL half (branch analysis,
   registry-monotonicity quantifier, trace induction) against a constructed
   antecedent. A variant, `containment_on_inert_class_of_nopre`, drops
   `NoRegistration` and carries `LeafSet.nopre` as the single remaining hypothesis.

2. **Every SHAPED class is EMPTY as a class of ledger transactions, so a `LeafSet`
   instantiated at a shaped `Shape` is a VACUOUS theorem.**
   `WSC/Props/Shaped/ShapeRealizability.lean`. Cause: a tractable `#prep_uplc` needs
   the redeemer map baked into the `Data` skeleton, so every shape bakes a ONE-entry
   redeemer map (two for DS1) — while every shape also bakes a TWO-entry withdrawal
   map whose entries are both SCRIPT credentials. Conway UTXOW (`MissingRedeemers`)
   requires one redeemer entry per script witness.
   * `t1_class_is_empty` is **UNCONDITIONAL** and uses only axioms this library
     already has (`WSC.LR_SPEND_RUNS_VALIDATOR` + `WSC.LR_CTX`): SHAPE T1 spends a
     mini-ledger input, which requires a `Spending` redeemer entry that T1's
     singleton `Rewarding` map does not have. **No `sorryAx`.**
   * L1 / DT1 / M1 / G1 / S1 (and T1 again, by the withdrawal route) are empty under
     `RedeemerCoverage` — the `MissingRedeemers` rule, stated as a **`Prop`, NOT an
     axiom**, so no library result becomes stronger because of a negative finding.
   * `t1VacuousLeaves` builds the shaped `LeafSet` and `t1_no_honest_step` proves no
     `Reachable.step` can fire in that class. The trap is exhibited, not described.
   * This **refutes no P-theorem**: `P1_T1`, `P4_disjunction_at_L1`,
     `P2b_shaped_containment`, `P5_shaped`, `P6` are as true as before. What it
     refutes is composing a shaped leaf THROUGH a `Shape` restriction.
   * COST TO FIX, sized in that module: re-cut the shapes with ledger-realistic
     redeemer maps (a new `#prep_uplc` per shape, ≈1 s each and budget-independent,
     plus re-verification of every theorem over them). NOT attempted by A2.

**Build after A2 (clean-room, same method as §5): 405 jobs, 83.4 s, 1.65 GB,
101 solver verdicts (66 `✅ Valid` + 35 `✅ Expected Falsified`), 0 `⚠️`, 0 `❌`,
0 errors, 20 expected `sorry` warnings, 67 WSC modules.** A2 adds **zero** solver
verdicts and **zero** `sorry`s — everything it proves is ordinary Lean. `top_claim`'s
26 project axioms are **unchanged**, verified by `#print axioms`.

**Sentence 2 of §0 below is SHARPENED by A2, not replaced:** the shaped layer is not
merely bounded by its shape — for the purposes of COMPOSITION its classes are empty.
Any future coverage argument must make the classes inhabited first.

## 0. The five sentences that must never be dropped

1. **Everything is BOUNDED BY A CEK BUDGET.** `#prep_uplc … n` bakes a finite step
   budget into the term the theorems quantify over; exceeding it evaluates to
   `Error`, which makes `isSuccessful` false and any `accept → POST` theorem vacuous
   past the bound. Every UPLC result below is bounded-transaction model checking of
   the real bytecode (ADDENDUM E1). **No result here covers unboundedly large
   transactions.**
2. **The shaped results are ALSO bounded by their SHAPE, and there is no coverage
   argument.** A shaped theorem quantifies over the scalar leaves (every
   `ByteString`, every `Integer`) of a *fixed* `Data` skeleton — list lengths,
   constructor tags and `Option`s all pinned. `WSC/SHAPE-BRIDGE.md` §10 enumerates
   three routes to a coverage theorem and offers none; `ShapeBridge.M1Covers` is
   recorded **false as stated**. And the shape bound is not incidental: P2b is
   provable at SHAPE S1 precisely because S1's one-policy/one-token-name values
   evade the two counterexamples that defeat the general statement
   (`WSC/AUDIT.md` §5.2). **Honest framing of the whole shaped layer: bounded model
   checking beneath the axiomatic layer.** Never quote a budget without its shape.
3. **`DirWF` / `DIRWF_L` is the single escape-critical assumption.** P5 is exactly
   as strong as it. U10 (`mkDirectoryNodeMP` at UPLC) is what would turn it from
   ASSUMED into PROVEN. Task V4 added its missing fourth (interval) conjunct and
   made the two bridges that consume it PROVED THEOREMS
   (`WSC.covering_node_excludes_registration`,
   `WSC.Composition.covering_excludes_ledger_registration`, both
   `[propext, Classical.choice, Quot.sound]` only), so the surface is the same size
   but discharging it is now an implication rather than a gap.
4. **"`sorry`-free" is FALSE for this library, including for the top theorem.** 62
   theorem-position results are closed by `blaster`'s `admit`; what certifies them
   is the `✅ Valid` verdict in the build log, not the Lean kernel.
   `WSC.Composition.top_claim` inherits `sorryAx` through P3 (`WSC/AUDIT.md` §3.1,
   correcting `status-fragments/V4.md`).
5. **`WSC/goldens/K-MEASUREMENTS.md` §5.1's prep-cost table must not be used for
   numbers.** Re-measured in the U3 clean-room rebuild: the module that table
   prices at **2,143 s (35.7 min)** elaborated in **44 s** — 48.7x out. It is a
   `lake env lean` artifact plus substrate drift, and it has already cost the
   campaign work (task U2 declined to build half the library on the strength of it).
   Time with `lake build`, and re-measure before concluding anything is
   unaffordable.

## 1. Property status table

State vocabulary (only these are used; "PROVEN-BY-DESIGN" and any unbounded claim
are banned):

* `PROVEN-AT-UPLC-WITHIN-BUDGET-K` — a `by blaster` theorem over the real bytecode
  at a named budget, with a non-vacuity witness, quantified over **all**
  `ScriptContext`s.
* `PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE` — the same, but quantified over the
  scalar leaves of a named SHAPE. **BOTH bounds binding.** Adds no faithfulness
  axiom. Strictly weaker than the row above; versus a source-model result it is
  stronger on the axiom count and weaker on the quantifier — neither dominates.
* `PROVEN-ON-SOURCE-MODEL-modulo-faithfulness-axiom` — a `sorry`-free Lean theorem
  about a clause-by-clause hand transcription (`WSC/Model/*.lean`), with ONE
  explicit `<model>_faithful` axiom bridging to the bytecode, backed by source-line
  citations and a golden differential test.
* `STATED-NOT-PROVED` — a `Prop` definition exists with its status recorded; no
  proof.
* `DEFERRED` — not started.

| Prop | Plain English | State (verified in the U3 rebuild) | Budget K + SHAPE / non-vacuity evidence | Honest caveat |
|---|---|---|---|---|
| **P1** | *Transfers conserve programmable tokens inside the mini-ledger: for a non-exemptable `(cs,tn)`, the amount at base outputs is at least the amount at base inputs plus the SIGNED net mint.* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `WSC/Props/Shaped/P1Shaped.lean` `P1_T1` `:223`, `P1_T2` `:273`, `P1_T6` `:794`, `P1_T7` `:839`, all ✅ Valid, **0 project axioms** (`[propext, sorryAx, Classical.choice, Quot.sound]`). **The `NOT-REACHABLE-AT-UPLC` verdict of earlier revisions is WITHDRAWN.** The source-model route (`WSC/Props/P1_Transfer.lean`) is retained as the only statement quantifying over ALL contexts; `P1_model` there is STATED-NOT-PROVED. | **K = 4400** over **SHAPES T1/T2/T6/T7**. Vacuity probes at all four shapes: Falsified (`:380`, `:403`, `:861`, `:884`). Concrete accepting instances through the real CEK: K = **2603** (T1), **3572** (T2), **3150** (T6), **3572** (T7). Excluded-case witness `exec_rejects_escape` (a ledger-legal containment violation, REJECTED by the bytecode). | Bounded twice. **Only 1 of 3 containment dispatch paths** is covered at UPLC (Path A); Paths B/C and input-side aggregation (≥2 mini-ledger inputs) are blocked by Blaster defect **D6**. Path C is proved at Lean level (`pathC_sound`). The exemption hypothesis is carried explicitly as `Model.coveringNodeExists … = false`; bridging it to ground truth costs `TS3` (`Composition.lean` §7.1). **FINDING: ARCHITECTURE §3-P1's `mintPos` form is REFUTED against the bytecode** (`P1ShapedWitness.mintPos_form_REFUTED`); the true form, and the one §5.2's Preservation consumes, is the SIGNED one. |
| **P2** | *An accepted seizure relocates only the seized policy and it stays in the mini-ledger.* | **BOTH conjuncts PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `WSC/Props/Shaped/P2Shaped.lean` `P2a_shaped_structure` `:232`, `P2b_shaped_containment` `:288`, joint `P2_shaped` `:370`, all ✅ Valid, **0 project axioms**. **`NOT-REACHABLE-AT-UPLC` WITHDRAWN.** Conjunct (a) is additionally `PROVEN-ON-SOURCE-MODEL-modulo-faithfulness-axiom` (`P2a_bytecode`, + `seizeModel_faithful`), which is the version that quantifies over all contexts and all step counts. | **K = 3800** over **SHAPE S1** (shaped prep 3.0 s; the unshaped prep never completed — 77 min @2000, 62 min @9000). Vacuity probe at S1: Falsified `:630`. The 600 and 1000 probes are `Valid`, i.e. **every earlier UPLC P2 statement was provably vacuous**. Witnesses K = **3004** / **3328**, plus two rejecting controls. Model fidelity gate: **13/13** golden agreement incl. a rejecting vector. | **Conjunct (b) is the sharpest shape-dependence in the library**: it is FALSE-in-general on the source model (obligation B1, two machine-checked counterexamples — `ptokenPairsContain` is unsound with duplicate token names or unsorted maps) and closes at S1 only because S1's values are structurally canonical. Do not generalize it by inspection. P2 does NOT claim the directory node the redeemer points at is authentic (ARCHITECTURE L2.5). Three by-construction equalities forced by a `#prep_uplc` limitation — see the module header. |
| **P3** | *You cannot spend a mini-ledger UTxO unless the global (transfer) or seize validator runs in the same transaction.* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K** — the only UNSHAPED leaf. `WSC/Props/P3_Base.lean:67`, ✅ Valid, 0 project axioms; negative control `:83`, tightness `:100` Falsified, vacuity probe `:112` Falsified, concrete accepting witness `:202`/`:209`. | **K = 600**, no shape. Golden `programmableLogicBase.base-spend-transfer-tx` halts accepting in **208** steps; in-library `P3Witness.ctx` accepted at 600 on **both** `.exec` and `.prop`. | Covers base-spend runs halting within 600 steps. Its conclusion is "the credential is in `txInfoWdrl`"; upgrading that to "the validator actually ran" is `LR_WDRL_RUNS_VALIDATOR`, not part of the proof. This is the one leaf `top_claim` actually consumes (via `p3_lifted`), and the reason `top_claim` carries `sorryAx`. |
| **P4** | *Every accepted mint routes tokens into the mini-ledger or is a pure burn (Local / DelegateTransfer / DelegateSeize / BurnOnly).* | **ALL FOUR ARMS PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE, SHAPE BY SHAPE** — arm 1 `Local`: `P4LocalShaped.lean` `P4_local_noEscape_shaped` `:203`, `P4_local_arm_shaped` `:299`, `P4_disjunction_at_L1` `:349`, plus the index-loosened `P4_local_noEscape_shapedIdx` `:407` (SUPERSEDES the L1 form); arm 2: `P4_disjunction_at_DT1` `:244`; arm 3: `P4_disjunction_at_DS1` `:406`; arm 4: `P4Shaped.lean:165` + `P4ShapedIdx.lean:59`. All ✅ Valid, **0 project axioms**. The disjunction over a FULLY SYMBOLIC redeemer tag remains `Undetermined`. | Arm 4: **K = 900**, SHAPES **M1/M2**, witness K = **784**. Arms 1-3: **K = 2500**, SHAPES **L1/L2, DT1, DS1**, witnesses K = **1681**, **1257**, **1466** — each EXACTLY the step count of its production golden. Vacuity probes at every one of those shapes: Falsified (`P4Shaped:247`, `P4ShapedIdx:103`, `P4LocalShaped:455`/`:545`, `P4DelegateShaped:360`/`:530`). | Four theorems over four pairwise-disjoint shape classes is **not** one theorem over a symbolic redeemer. Arm 1 is the strong one: the policy's OWN no-escape scan over every output, in ground-truth `noEscape` vocabulary. **Arms 2 and 3 prove strictly less** — only that a sibling validator RUNS (`credentialInWithdrawals`). The registration conjunct at SHAPE L2 is `Undetermined`. **Budget-bridge gap: `LR_BUDGET_minting` is published at 900 only**, below the 1257/1466/1681 that arms 1-3 cost; `WithinBudget`'s `K_mint` clause must be raised in step with a 2500 bridge. |
| **P4a** | *Every accepted mint invokes the token's own minting-logic script (common corollary of all four arms).* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P4Shaped.lean:121` (M1), `P4ShapedIdx.lean:42` (M2, symbolic withdrawal index — strictly more general), `P4a_local_shaped` `:235` (L1). ✅ Valid, 0 project axioms. Fully symbolic: `Undetermined` after 3,208 s. | Same as P4's arms. Full control set at each shape (negative control Valid, tightness Falsified, vacuity Falsified). | Same as P4. |
| **P5** | *A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ an authentic directory node covers `cs` (`key < cs < next`).* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P5Shaped.lean` `P5_shaped_indexed` `:209`, ✅ Valid, 0 project axioms; composed with the pure-Lean ladder in `WSC/Props/P5_NonMember.lean` this yields ADDENDUM E3's ∃-form `P5_shaped_exists` `:239` and the ground-truth `P5_shaped_groundtruth` `:276` (**+`TS3`, `Deployed`, `OnChain` only — `TS5` is NOT needed**). Over a FULLY SYMBOLIC context the same obligation still returns NO verdict (killed at 5,241 s). | **K = 1600**, **SHAPE G1**. Vacuity probe at G1: Falsified `:398`. Witness K = **1541** (halts at 1541, budget-errors at 1540), `validRewardingContext` with ZERO failing conjuncts, accepted by the shaped AND the unshaped executable term. | Escape-critical: P5's strength = `DirWF`'s strength. The postcondition is the covering-node witness, **not** `¬ IsRegistered`; the bridge to "not registered" is now proved (§0.3). Requires the CIP-153 PlutusCoreBlaster branch, which is **unpushed** (§3 D5). Honest falsification on the record: the index-FREE variant (SHAPE G2) is `Falsified` with `pIdx = nIdx = 1` — not a validator defect (on chain `TS2` excludes it), and a positive argument for the indexed form (`SHAPING-RESULTS.md` §6). |
| **P6** | *Claiming Member is self-penalizing: an accepted Member classification adds the positive minted amount to the value that must remain at base outputs.* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P6Shaped.lean` `P6_shaped_member_adds_to_requirement` `:234`, `P6_shaped_member_mint_stays_at_base` `:259`, ✅ Valid, 0 project axioms; `P6_shaped_noBaseInputs` `:209` is pure Lean (**no `sorryAx` at all** — the only headline theorem the kernel fully checks). Bridged to `Composition.lean`'s vocabulary by `P6Bridge.lean`. `NOT-REACHABLE-AT-UPLC` WITHDRAWN. Source-model core retained: `P6_Member.lean` `mintWalk_sublist`, `mintWalk_member_retains`. | **K = 3300**, **SHAPE G6**. Vacuity probe at G6: Falsified `:363`. Witness K = **2837**, plus `exec_rejects_escape_under_member` and the discriminating pair `exec_accepts_same_escape_under_nonmember`. | **⚠️ THE CAUTIONARY ROW OF THE WHOLE CAMPAIGN.** P6 was first stated at **2500**, returned `✅ Valid`, and was **genuinely VACUOUS** — the shape class was accept-UNSAT and only the mandatory vacuity probe caught it. Preserved as `WSC/Shaped/Probe/G6Vacuous2500.lean` (a stanza that *expects* `Valid`). No accept-hypothesis theorem in this library may be quoted without its probe. |
| **P2′** | *A seized-policy mint cannot bypass the seize: the issuance `DelegateSeize` arm binds that mint to this seize.* | **PARTIALLY SUBSUMED, binding claim DEFERRED** — the arm is proved at SHAPE DS1 (`P4_delegateSeize_arm_shaped`), but it concludes only `seizeScopedToNodeOf` / "the seize validator runs". | — | Its postcondition names the seize redeemer, so it needs P2 and P4-arm-3 in the SAME statement; nobody has written it. See also `LeafSet.p4`'s `LR5` gap below. |

### Composition (`WSC/Composition.lean`, tasks V4 + U2)

| Item | State | Note |
|---|---|---|
| `top_claim`, `no_programmable_tokens_outside_mini_ledger`, `preservation`, `nonEscape_of_registered` | **PROVED AS A REDUCTION.** Real Lean theorems, green in the clean-room rebuild — but stated over an explicit `leaves : LeafSet hp Shape` hypothesis bundle, and they carry `sorryAx` (through P3). **Never quote as "the claim is proved"; quote as "the claim reduces to exactly these four obligations plus 26 axioms".** | Ledger vocabulary exists: `UTxO`/`Ledger`/`OutOfBase`/`RegisteredIn`/`I`/`Reachable`. Per-theorem `#print axioms` in `WSC/AUDIT.md` §3. |
| **`LeafSet` instantiation** | **OPEN — no `LeafSet` value is constructed anywhere in the library** (grep-verified; `WSC/AUDIT.md` §3.1 item 2). | This is precisely the gap between "reduction" and "proof". |
| `LeafSet.p1` (exit via transfer, P6 folded in) | **INGREDIENT PROVED, RESIDUE OPEN** — `leafP1_of_shapedGlobalContainment` (§10.2) gives the field's exact type from `ShapedGlobalContainment hp Shape`, whose single field is the two remaining non-vocabulary obligations: the **shape bridge instantiated at the 4400 prep** and `LR_BUDGET_global` at 4400. The vocabulary bridges (§10.1) are PROVED: `outSum ≡ sumOutsIf`, `inSum ≡ sumInsIf`, `contain_iff_modelSums`; `mintSigned ≡ mintOf` definitionally. | Costs `TS3`, `Deployed`, `OnChain`, `NodeAcceptsGlobal`. |
| `LeafSet.p4` (entrance) | **INGREDIENT PROVED, RESIDUE OPEN** — `p4_disjuncts_of_custody` (§10.3) derives the field from the full four-way `LocalCustodyOk ∨ DelegateTransferOk ∨ DelegateSeizeOk ∨ BurnOnlyOk`, which is what the four shaped arm theorems conclude. Residues: shape coverage, the shape bridge, and a minting budget bridge at 2500. | Carries U2's finding that **`WSC.LR5` does NOT entail `seizeCred ∈ txInfoWdrl`** from `seizeScopedToNodeOf` (`validScriptInfo` constrains the RUNNING script's purpose only) — isolated as `SeizeWdrlOfScoped`; needs a strengthened `LR5` or a new `LR_REDEEMER_PURPOSES_REAL` with a `Conway/TxInfo.hs transTxRedeemers` audit row. |
| `LeafSet.p2` (exit via seize) | **OPEN** — the shaped P2 theorems exist but nothing connects them to the field. | Needs the shape bridge plus "structure preserved ⟹ `Contain` for a non-seized policy", an unwritten lemma. |
| `LeafSet.nopre` (`L-mint-needs-reg`) | **OPEN, the weakest leaf.** Nobody has started it. | Needs the FULL P4 over a symbolic redeemer plus trace induction. |
| `L-monotone` (registration is insert-only) | **ASSUMED** — `DirWF` conjunct (i) per-tx; `lr_registration_source` + `DIRWF_L` at ledger level. | Discharged by U10. |
| `LR_BALANCE_SLOT` | **AXIOM, but its exact statement is now DERIVED** — `LR_BALANCE_SLOT_of_valueAlgebra` proves it from `WSC.LR7` plus two named `CardanoLedgerApi`-only residues (`ValueAlgebra`, 3 fields; `LedgerCanon`). Instantiating both deletes the axiom. | U2 finding: **`valueOf` is NOT additive over `merge`** without canonicity (`merge_not_additive_without_canonicity`, a `native_decide` counterexample), and CLAB has **zero** `Value` algebra — so "mechanical" was wrong. Template is PCB's `PlutusCore/Value/Algebra.lean` (~330 lines) and it is not reusable as-is. |

### The shape bridge (`WSC/ShapeBridge.lean`, task U1)

| Item | State |
|---|---|
| `isSuccessful (appliedXShaped.prop args) ↔ isSuccessful (appliedX.prop (shapedCtx args))` | **PROVED for all 16 shaped preps, no axiom.** 25 verdicts re-verified in the U3 rebuild (19 Valid + 6 Expected-Falsified controls). The `exec`-level form (`XRun K`) is **kernel-checked `rfl`** — `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — and holds at every budget; `inputs_M1` "does not depend on any axioms". |
| Tier A (6 shapes: B1@600, M1/M2@900, G1/GIdx/GNIdx@1600) | RHS is the unshaped prep's `prop` at the same budget — complete, no residual. |
| Tier B (10 shapes: G6@3300, L1/L2/DT1/DS1@2500, S1@3800, T1/T2/T6/T7@4400) | RHS is `Runs.XRun K`; **no unshaped prep exists at those budgets and none is affordable.** Inherits the `PropExecFaithful` warning (`SHAPE-BRIDGE.md` §5). |
| **Is it consumed?** | **(A1) PARTLY — YES by `Honest.lean`, still NO by `Composition.lean`'s `LeafSet`.** Task A1 restated the four `LR_BUDGET_*` axioms against `Runs.XRun K` (the definitions moved to the leaf module `WSC/Runs.lean` to break the import cycle), so the ledger side now names exactly the term the 16 kernel-checked `exec_<S>` `rfl`s land on, at EVERY budget. What is still unconsumed is the `LeafSet`: no field is instantiated, so no `bridge_<S>` is applied to anything. See §0.0. |
| **(A1) Does the Tier A/B split still matter?** | For the LEDGER bridge, no — both tiers' right-hand sides are now what `LR_BUDGET_*` names. For OPTIMIZER evidence, yes: Tier A's RHS went through `Optimize.main` on a symbolic context and Tier B's did not go through it at all, so only Tier A's verdict says anything about shaping-commutes-with-the-optimizer. `PropExecFaithful` is unchanged in substance and scope for the shaped layer. |
| In the default build target? | **Yes, since U3** — `WSC.lean` imports it (36 s). `lake build WSC` did not check it before. |

## 2. Axiom base — what is assumed

**(A1) 50 `axiom` declarations** by `grep -c '^axiom '` (51 before A1 deleted
`GlobalPreppedAt`; `WSC/AUDIT.md` §2's "47" is 4 low — see §0.0's measurement
note), and **no `axiom` anywhere in `Prep/*`, `Shaped/*` or `Props/Shaped/*`** — the shaped layer really does add no assumption, which is its
central claim and is now machine-verified. `top_claim` reaches **26** of the 47;
read that as a **floor**, since instantiating the open `LeafSet` fields adds the
other 21. Full per-theorem census: `WSC/AUDIT.md` §3. **Read the
numbering-collision table at the top of `WSC/Honest.lean` before citing a name** —
the file-local `TS1…TS5` / `LR1…LR7` do not mean ARCHITECTURE §5.3's.

| Group | Axioms | Reached by `top_claim`? | Discharged by |
|---|---|---|---|
| Modelling boundary | `OnChain`, `Deployed` | yes | Never — they are the model/chain bridge. |
| TRUSTED-SETUP | `TS1`, `TS2`, `TS_MINTING_IDENTITY`, `mlhPolicyId` | only `mlhPolicyId` | Deployment audit of the one-shot params anchor; U10 for the registration side. `TS_SCRIPT_HASH_BINDING` is **checked, not assumed** (E7, `WSC/flats/PROVENANCE.md`). |
| LEDGER-RULE (per-tx) | `LR1`–`LR7`, `LR_CTX` | only `LR_CTX` | Trusting the Cardano ledger; every `LR_CTX` conjunct is mapped to a cited ledger rule (`WSC/LR-CTX-AUDIT.md`). |
| LEDGER-RULE (triggers) | `LR_MINT_RUNS_POLICY`, `LR_WDRL_RUNS_VALIDATOR`, `LR_SPEND_RUNS_VALIDATOR` | yes | Trusting the ledger (Conway UTXOW scripts-needed). |
| Non-negativity | `NONNEG`, `NONNEG_L` | yes | Trusting the ledger. |
| Node-accept / step abstractions | `NodeAccepts{Base,Minting,Global,Seize}`, `nodeSteps{Base,Minting,Global,Seize}` | all but `nodeStepsSeize` | Never — they ARE the "a node ran this script for this many steps" interface. |
| Budget bridge | `LR_BUDGET_base` (K=600), `LR_BUDGET_minting` (**900**), `LR_BUDGET_global` (prep-parametric, gated on `GlobalPreppedAt`), `LR_BUDGET_seize` (**no K — unusable by construction**) | only `LR_BUDGET_base` | A budget-monotonicity meta-theorem about `runSteps` that the substrate does not provide. `K_global` was republished at **4400** (P1's witnesses cost up to 3572) with `K_global_nonmember = 1600` as P5's sub-bound. `BaseNonVacuous` and `MintingNonVacuous` are DISCHARGED (`Composition.baseNonVacuous`, `Composition.mintingNonVacuous`); `GlobalNonVacuous` is PROVED in `ShapeBridge` but still recorded open in `Honest.lean` (`WSC/AUDIT.md` F7); `SeizeNonVacuous` is unreachable at any affordable budget. |
| DIRECTORY | `DIRWF` (**4** conjuncts since V4), `TS3`, `TS4`, `TS5` | none — they enter with the leaves | **U10** — `mkDirectoryNodeMP` at UPLC. **Escape-critical.** Measured: the raw↔ground-truth reconciliation costs `TS3` only, **not** `TS5`. |
| LEDGER-LEVEL (`Composition.lean`) | `LedgerStep`, `Genesis` (declared, not defined); `lr_utxo_semantics`, `lr_inputs_in_ledger`, `lr_registration_source`, `LR_BALANCE_SLOT`, `ts_genesis`, `ts_minting_identity_L`, `NONNEG_L`, `DIRWF_L` | **all 10** | Trusting the ledger (the `lr_*` four + `NONNEG_L`); deployment audit (`Genesis`/`ts_genesis`/`ts_minting_identity_L`); **U10** (`DIRWF_L`, escape-critical). `LR_BALANCE_SLOT` is derivable — see the Composition table. |
| FAITHFULNESS (deliberately NOT in `Honest.lean` — a different KIND of assumption) | `Model.globalModel_faithful`, `SeizeModel.seizeModel_faithful` | no | Source-line citations + golden differential (global 4/4, seize 13/13, both including rejecting vectors). Each is a whole-validator model↔bytecode equivalence. |
| NOT EXPRESSIBLE | ARCHITECTURE §5.3 `lr_collateral_pubkey_only` | — | PlutusV3 `TxInfo` has no collateral field; the collateral exit route must be closed outside this model. |

## 3. Defects — current ledger

**D1 (`validRedeemerMap` ordering) — ✅ FIXED (Z1), and now EXERCISED.** CLAB used
the Plutus constructor order for `ScriptPurpose`; the ledger emits
`ConwayPlutusPurpose AsIx` order and does not re-sort (`Conway/Scripts.hs:202-213`,
`Babbage/TxInfo.hs:217-221`). `ltScriptPurpose` (V3 and V1/V2) now uses the ledger
order with citations. SHAPE **DS1** carries a real 2-entry `[Minting, Rewarding]`
redeemer map that `validMintingContext` accepts, with a Falsified vacuity probe and
a concrete accepted witness — so the fix is exercised, not merely asserted.
`P4Shaped.lean`'s D1 stanza is stale on this point (V3 finding, not yet corrected).

**D2 (`validWithdrawals` credential order) — ✅ FIXED (Z1).** `ltCredential` is now
`ScriptCredential < PubKeyCredential` (`Credential.hs:96-99`). Changed no golden
verdict, as predicted, which confirms the seize goldens' earlier
`validWithdrawals` failure was a harness artifact.

**D3 (no golden satisfied `validXContext`) — ✅ FIXED (Z5).** All 9 ACCEPTING
goldens satisfy `validXContext` verbatim; 10 of 13 are TRUE and the 3 FALSE are
tamper-intrinsic. Machine-checked in `WSC/Goldens/Audit.lean`. Pre-fix JSONs kept
under `WSC/goldens/pre-fix/`.

**D4 — CLAB does not assert the PV11 rule
`txInfoInputs ∩ txInfoReferenceInputs = ∅`** (`Conway/TxInfo.hs:492, 811-822`). A
*missing* conjunct, i.e. the precondition is weaker than reality, which
strengthens the theorems. Recorded, not a problem. (Note: `SeizeShaped.lean`'s
header uses "D4" for an unrelated `#prep_uplc` limitation — the numbering collides;
read in context.)

**D5 — the substrate is not reproducible off this machine.** `lakefile.lean` pins
PlutusCoreBlaster by **absolute local path** to the unpushed branch
`cip153-value-builtins` @ `9f9ca8c` (ARCHITECTURE E11). Every "proved against
production bytecode" claim for the global/seize validators inherits this.
**Highest operational risk in the repository.**

**D6 — Blaster `#prep_uplc` emits kernel-ill-typed `Blaster.dite'` terms** when a
CIP-153 `Value` builtin result stays symbolic (the motive is not updated after De
Morgan / Bool-polarity rewrites). Reproductions:
`WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` (deliberately non-building; not
imported anywhere — verified in the U3 rebuild). **Blocks P1's containment dispatch
Paths B/C and input-side aggregation at UPLC.** Needs an upstream fix.

**D7 (task U3) — `WSC/goldens/K-MEASUREMENTS.md` §5.1's prep costs are ~49x
pessimistic.** See §0.5. Not a code defect; a measurement defect that has already
misdirected work.

**D8 (task U3) — `set_option warn.sorry false` in 15 modules makes the build-log
`sorry` census incomplete** (~42 `admit`s hidden, so the "19 expected sorries"
whitelist is a count of *unsuppressed* warnings only). Use `#print axioms` →
`sorryAx`; reproducible in one command via `WSC/Shaped/Probe/U3Census.lean`.

## 4. What would move the needle, in order

1. ~~**Restate `LR_BUDGET_*` against `ShapeBridge.XRun K`**~~ — **DONE (task A1)**,
   see §0.0. It delivered items (a) the kernel-checked bridge, (c) no more
   `GlobalPreppedAt`, and (d) the Tier A/B dissolution for the ledger bridge; it
   delivered (b) `PropExecFaithful` removal only on the base/keystone path, not
   campaign-wide, and it did NOT by itself unblock `LeafSet.p1`/`p4`, whose binding
   residues turned out to be the shape bridge and shape COVERAGE. **The replacement
   item at this priority: restate the 14 shaped P-theorem groups on `Runs.XRun K`**
   (measured feasible at keystone grade in `WSC/Props/P3_BaseRun.lean`: `✅ Valid`,
   3.7 s), each with a FRESH vacuity probe at the run term — that is what would
   delete `PropExecFaithful` from the campaign. Real proving, with real risk that a
   probe returns `Valid` (i.e. vacuous), as happened to P6 at 2500.
2. **Instantiate the `LeafSet`.** `p1` and `p4` need only their residues (item 1 +
   coverage); `p2` needs "structure preserved ⟹ `Contain`"; `nopre` needs the full
   P4 plus trace induction. Until one `LeafSet` value exists, the top claim is an
   implication with an open antecedent.
3. **Decide the shape-coverage question, and say so in public** — either produce an
   argument (`SHAPE-BRIDGE.md` §10 lists three routes, all costly) or publish the
   shaped layer explicitly as a bounded-model-checking tier and record in
   `Honest.lean` which axioms it replaces ON THOSE SHAPES ONLY. Doing neither is
   the current state and the biggest presentational risk.
4. **U10 — `mkDirectoryNodeMP` at UPLC**, discharging `DirWF`/`DIRWF_L`. The only
   escape-critical assumption; highest assurance ROI.
5. **Push the PCB `cip153-value-builtins` branch and re-pin `lakefile.lean` to a
   full rev** (D5). Cheap, and without it nothing here is independently checkable.
6. **Fix D6 upstream** — that is what would extend P1 to dispatch Paths B/C and to
   ≥2 mini-ledger inputs.
7. **Instantiate `ValueAlgebra` + `LedgerCanon`** to delete `LR_BALANCE_SLOT`;
   budget it as a ~330-line `Value`-algebra development, not a mechanical step.
8. ~~**Minting budget bridge at 2500**~~ — **the BRIDGE half is DONE (task A1)**:
   `LR_BUDGET_minting` at `K_mint_custody = 2500`, non-vacuity proved from SHAPE L1
   (K = 1681). What remains is raising `WithinBudget`'s `K_mint` clause to match,
   which is a widening of `HonestTx` and therefore a composition-core decision
   (§0.0).

## 5. Reproduction

```
# the whole library, clean-room
#   U3: 401 jobs, 93.7 s, 98 ✅ markers, 0 errors, 21 sorry warnings
#   A1: 404 jobs, 79.8 s, 101 ✅ markers, 0 errors, 20 sorry warnings
cp -a <CLAB checkout> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge

# the axiom census behind §2 and WSC/AUDIT.md §3 (2.7 s warm)
lake build WSC.Shaped.Probe.U3Census

# (A1) prep-cost RE-MEASUREMENT, the F5 repair -- WSC/goldens/K-MEASUREMENTS.md §5.1a
for m in Base Minting Minting800 Minting900 Minting1300 Seize Global Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.olean .lake/build/lib/lean/WSC/Prep/$m.ilean \
        .lake/build/lib/lean/WSC/Prep/$m.trace .lake/build/lib/lean/WSC/Prep/$m.*.hash
  /usr/bin/time -f "$m %e s %M KB" lake build WSC.Prep.$m > /dev/null
done

# CEK step counts K of the 13 goldens (3.2 s)  -- WSC/goldens/K-MEASUREMENTS.md §6
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure   # git log -1 == 9f9ca8c
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# per-conjunct golden validXContext audit (§3 D1/D2/D3)
python3 WSC/goldens/ctx-audit/GenCtxAudit.py       && lake env lean CtxAudit.lean
python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py && lake env lean CtxAuditDetail.lean
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib` and is 15-53x slower, which is the source of D7.
