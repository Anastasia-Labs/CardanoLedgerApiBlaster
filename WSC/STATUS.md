# WSC containment campaign — AUTHORITATIVE STATUS

**Read this first, then `WSC/AUDIT.md`.** Everything below is machine-checked or
measured *in this repository*, with the file/line or the measurement cited. Where a
result is not there yet, this table says so in those words.

**Revision: rewritten at task E5 (2026-07-25) from three independent clean-room
rebuilds, and RE-MEASURED at task G3 from two more at HEAD `f4486ca` — never from a
task report.** It supersedes the C4 revision and the E1/E3/E4 fragments, which are
folded in and kept as the per-task record. **G3 checked the G-stage units' work
EXISTED before believing any of it** (`AUDIT.md` §7.6); that check is now mandatory
for any unit gating another's, and it is why finding F20 exists. Any disagreement between a fragment and
this file is resolved in favour of this file, and the disagreements are itemised in
`WSC/AUDIT.md` §7 and §8.

---

## 0. THE SEVEN SENTENCES THAT MUST NEVER BE DROPPED

1. **The top claim is NOT PROVED.** *In an honest deployment, programmable tokens
   cannot exist outside the mini-ledger (the `programmableLogicBase` payment
   credential).* What exists is (a) a machine-checked **reduction** of it to four leaf
   obligations plus **26 project axioms** (`WSC.Composition.top_claim`); (b) that
   reduction **discharged outright over one inert accounting class**
   (`containment_on_contained_class`, over `ContainedTx`); and (c) — completed in
   stage 11 — that reduction **discharged with NO remaining leaf hypothesis over TWO
   node-realizable shape classes**, `RealizableLeaves.containment_on_realizable_class`
   (transfer, `T1RShapeNS`) and `RealizableLeaves.containment_on_seize_class`
   (seize, `S1RShape`), each depending on **28** project axioms.
2. **"N = 0" IS NOT THE MEASURE. THE RATIO IS.** In (b) the class does all the work
   and **no UPLC result is used** (Lean's own five `unused variable` warnings at
   `Composition.lean:2442-2446` prove the acceptance hypotheses are unused). In (c),
   **one of four leaves is the production bytecode with its acceptance hypothesis
   genuinely consumed, and three of four are the shape** — on *each* side:

   | class | `p1` | `p2` | `p4` | `nopre` |
   |---|---|---|---|---|
   | `T1RShapeNS` (transfer) | **BYTECODE** (`P1R_T1` @ 4400) | shape + ledger rule | shape | shape |
   | `S1RShape` (seize) | shape + ledger rule | **BYTECODE** (`P2b_R_containment` @ 3800) | shape | shape |

   Closing the last leaf hypothesis cost **zero** axioms — the axiom sets of the
   hypothesis-free result and the C4 result that assumed `p2` are *set-equal*,
   measured. It removed an assumption by **restricting the class**, not by proving
   more about the code. **Quoting "N = 0" without this table is an overclaim.**
3. **Everything about the bytecode is BOUNDED BY A CEK BUDGET.** `#prep_uplc … n`
   bakes a finite step budget into the term the theorems quantify over; exceeding it
   evaluates to `Error`, which makes `isSuccessful` false and any `accept → POST`
   theorem vacuous past the bound. **No result covers unboundedly large
   transactions.**
4. **The shaped results are ALSO bounded by their SHAPE — and coverage is now PROVED
   FALSE.** This sentence changed twice and both changes must be quoted precisely.
   *At A3:* every shape was **proved empty** as a class of ledger transactions (a
   one-entry redeemer map alongside two script withdrawals; Conway
   `hasExactSetOfRedeemers`), so the six properties were true statements about empty
   sets.
   *At C4:* **11 of 12 shapes were re-cut** to carry exactly the redeemer entries the
   rule demands, every property was re-proved over them, and each re-cut shape has a
   certified inhabitant satisfying `validXContext` **and both halves** of the Conway
   rule. *At G1 (`f4486ca`):* the twelfth, SHAPE L2, was re-cut as **L2R** — so
   **all 13 re-cut shapes now carry the full four-item bar** and no property in the
   library ranges over an unrepaired shape. (The roster module
   `RealizableShapes.lean` was not extended with an `l2r_realizable` alias; L2R's
   realizability theorem is `WSC.L2RWitness.ctx_realizable` in `P4LocalShapedR.lean`.
   Cosmetic, noted so nobody greps the roster and concludes L2R lacks one.)
   *Caveat carried since G2 (F18):* the rule the re-cut is checked against is the
   **all-Plutus specialisation** of Conway's, not Conway's rule itself. That is
   conservative for these positive inhabitation claims and only for those.
   *Now:* coverage is stated in Lean (`WSC/Coverage.lean`) and **refuted** —
   `not_covers_at_T1R_size` exhibits three ledger-valid, redeemer-exact transactions
   that the real bytecode accepts in **exactly 2,603 steps** (the certified
   inhabitant's own K) and that lie outside **all twelve** re-cut shapes named in
   `Coverage.lean` (`rangeG1R`, `rangeG6R`, `rangeT1R/T2R/T6R/T7R`, `rangeM1R/M2R`,
   `rangeL1R`, `rangeDT1R`, `rangeDS1R`, `rangeS1R`). Two differ by a list length,
   one by a constructor tag; none is repairable by adding a shape parameter.
   **0 project axioms, no `sorryAx`.** **Not re-proved for L2R:** `Coverage.lean` was
   written before SHAPE L2R existed and was **not** extended with a `rangeL2R`
   disjunct, so the refutation is literally about those twelve. This weakens nothing —
   the refutation is a *negative* result, and adding a thirteenth disjunct could only
   ever make it harder to hold, never easier — but the theorem as stated does not
   mention L2R and should not be quoted as if it did.
   **Honest label for the whole shaped layer: exhaustive symbolic checking of the real
   compiled code over named bounded families of `Data` skeletons that are
   node-realizable, and that are now known NOT to cover the transactions the claim is
   about.** Never quote a budget without its shape.
5. **`DirWF` / `DIRWF_L` is the single escape-critical assumption.** P5 is exactly as
   strong as it. `mkDirectoryNodeMP` at UPLC is what would turn it from ASSUMED into
   PROVEN. Task V4 added its missing fourth (interval) conjunct and made the two
   bridges that consume it PROVED THEOREMS
   (`WSC.covering_node_excludes_registration`,
   `WSC.Composition.covering_excludes_ledger_registration`), so the surface is the
   same size but discharging it is now an implication rather than a gap.
6. **"`sorry`-free" is FALSE for this library, including for every top-level
   theorem.** **101** theorem-position results are closed by `blaster`'s `admit`; what
   certifies them is the `✅ Valid` verdict in the build log, not the Lean kernel. Every
   top-level theorem inherits `sorryAx` — the older ones through P3, the two shaped
   ones through P3 *and* through `P1R_T1`/`bridge_T1R` or
   `P2b_R_containment`/`bridge_S1R`. **And the build log's `sorry` warning count is
   NOT a census:** 38 modules set `warn.sorry false`, and a line-oriented grep of
   `#print axioms` undercounts `sorryAx` as 17 when the true figure is **37**. The
   instrument is `#print axioms`, parsed **across newlines** *and* for **both output
   forms** — 5 results print "does not depend on any axioms" with no brackets, and a
   bracket-only parser reports 169 results instead of the true **174**.
7. **This checkout now builds elsewhere — but only after two manual steps, and the
   substrate branch is still unpublished.** `WSC/substrate/` carries a verified
   incremental `git bundle` reconstructing PlutusCoreBlaster
   `9f9ca8c76baf3b5efdb63c33ca0091efa606b474` byte-identically (HEAD, tree and a full
   `diff -r` re-checked at E5), the revision is recorded in `lakefile.lean`,
   `lake-manifest.json` and `WSC/ARCHITECTURE.md`, and `WSC/REPRODUCE.md` is the
   third-party recipe. Without its CIP-153 `Value` builtins
   `programmableLogicGlobal.flat` does not decode (verified negative control against
   PCB `main`: *"Could not decode program!"*). **Still open:** the branch is not on
   the public remote, so custody of the bundle is the trust anchor; the `require` is
   still an absolute path, needing a two-file edit; and lake does not enforce the
   recorded revision for a path dependency.

---

## 1. VERIFIED BUILD STATE (task G3 clean-room rebuild, two runs, HEAD `f4486ca`)

*E5's three-run figures at `7039cdb` are given in parentheses where they differ.*

| measurement | value |
|---|---|
| command | `rm -rf .lake/build/lib/lean/WSC*` then `lake build WSC WSC.ShapeBridge` |
| exit status | 0 — **432 jobs**, both runs (E5: 431) |
| wall clock | **1 m 46.22 s / 2 m 09.91 s** — two independent runs. **Quote the range 1:46–2:10**, never a point value (E5, quiet box: 1:39–1:57) |
| user + sys CPU | 466.7–515.0 s + 64.3–70.3 s (450–499 %) |
| max RSS | **1.652–1.658 GB**. **This is NOT an instrument** — it tracks machine load, not the library: a clean-room build of *unmodified* `7039cdb` under the same concurrent load also measures 1.64 GB. Quote **1.50–1.66 GB, load-dependent** |
| WSC modules re-elaborated | **94** (E5: 93; +1 = `WSC.Shaped.MintingLocalShapedRIdx`) |
| solver verdicts | **162** = **103 `✅ Valid`** + **59 `✅ Expected Falsified`** (E5: 159 = 102 + 57) |
| `⚠️ Undetermined` / `❌` | **0**, both runs |
| `error:` lines | **0** (hard requirement — met, both runs). *Caveat F21: two `Error:`-prefixed lines from a `panic!` in CLAB's `Recursor.all` macro DO appear; pre-existing, benign, exit 0* |
| `declaration uses 'sorry'` | **20** (19 blaster `admit` in `ShapeBridge`, 1 pre-existing in PCB `CekMachine.lean:299`) — **not a census**, §0.6 |
| `unused variable` | **5**, all at `Composition.lean:2442-2446` — Lean's own confirmation of §0.2 |
| source reconciliation | **101** `blaster` tactics + 2 `solve-result: 0` + **59** `solve-result: 1` = **162**, exact — and now checked **per verdict**, by reading the source line each `file:line:col` marker points at, rather than by comparing totals |
| `#print axioms` results | **174** distinct (E5: 173); **37** carry `sorryAx` (unchanged); 72 use `native_decide`; **124** carry zero project axioms (unchanged). The single new result is `g6_class_is_empty_nonNative` |
| `axiom` declarations | **51** (Honest 38, Composition 10, P1_Transfer 2, SeizeModel 1) — unchanged by stage 11 **and by the G stage** |
| `axiom` under `Prep/`, `Shaped/`, `Props/Shaped/` | **0** — the shaped layer adds no assumption; survives G1's new SHAPE L2R module intact |

Stage-by-stage reconciliation from the C4 baseline: **429 → 431 → 432 jobs**,
**158 → 159 → 162 verdicts**. E1 `+1 module / +1 verdict` (`bridge_S1R`, 1 Valid);
E4 `+1 / +0` (`WSC/Coverage.lean` runs no solver); E2 `+0 / +0` (**produced
nothing** — see `AUDIT.md` §7.2); E5 `+0 / +0` (documents and the substrate
artifact); **G2 `+0 / +0`** (F18 — every new result is ordinary Lean); **G1
`+1 module / +3 verdicts`**, pinned to source lines: `P4LocalShapedR.lean:597`
(1 Valid, the L2R negative control), `:677` and `:708` (2 Expected Falsified, the
L2R tightness and vacuity stanzas). F17's paste adds **0** — it is `native_decide`
throughout. `102 + 1 = 103` Valid, `57 + 2 = 59` Expected Falsified.

**Both G-stage units delivered artifacts; neither is an E2.** G3's first action was
the existence check, before any rebuild — `AUDIT.md` §7.6.

---

## 2. PROPERTY STATUS TABLE

All six are **PROVED at UPLC against the production bytecode**, over the **re-cut**
shapes. The pre-re-cut theorems are retained, still `✅ Valid`, but range over classes
proved empty and **must not be quoted** — this now includes
`P4_local_noEscape_shapedIdx` (SHAPE L2), superseded by `P4_local_noEscape_RIdx`
(SHAPE L2R). Note the emptiness proofs themselves were downgraded at G2: six of them
now carry an explicit `RedeemerCoverageAt w` side condition, because CLAB's coverage
predicate is the **all-Plutus** reading of Conway's rule and is therefore too strong
to use negatively without it (F18).

| # | Status | Theorem(s) | Budget / shape | Witness K | Realizability | 4-point bar |
|---|---|---|---|---|---|---|
| **P1** | PROVED, Path A only | `P1R_T1/T2/T6/T7` (`P1ShapedR.lean`) | 4400 / T1R, T2R, T6R, T7R | 2603 / 3572 / 3150 / 3572 | `t1R…t7R_realizable` | **4/4** each |
| **P2** | PROVED, both conjuncts | `P2a_R_structure`, `P2b_R_containment`, `P2_R_gates_are_earned` (`P2ShapedR.lean`) | 3800 / S1R | 3004 (accept) / 3328 | `s1r_realizable(Exact)` | **4/4** |
| **P3** | PROVED, unshaped | `P3_base_requires_global_or_seize_run` (`P3_BaseRun.lean`) | 600 / — | golden 208 | n/a (unshaped) | n/a |
| **P4** | PROVED, all four arms | `P4_disjunction_at_{L1R,DT1R,DS1R}`, `P4_burnonly_arm_R`, **`P4_local_noEscape_RIdx` (L2R)** | 900 / M1R, M2R; 2500 / L1R, **L2R**, DT1R, DS1R | 784 / **784** / 1681 / **1681** / 1257 / 1466 | `m1r,m2r,l1r,dt1r,ds1r_realizable`; L2R via `L2RWitness.ctx_realizable` | **4/4 — every row, M2R included** (F17 landed at `f4486ca`) |
| **P4a** | PROVED | `P4a_R_*`, `P4a_RIdx_*`, `P4a_local_R` | as P4 | as P4 | as P4 | as P4 |
| **P5** | PROVED | `P5R_shaped_indexed/_exists/_groundtruth` (`P5ShapedR.lean`) | 1600 / G1R | 1541 | `g1R_realizable` | **4/4** |
| **P6** | PROVED | `P6R_shaped_member_adds_to_requirement`, `_mint_stays_at_base`, `_noBaseInputs` | 3300 / G6R | 2837 | `g6R_realizable` | **4/4** |

The four-point bar is: theorem `✅ Valid`; vacuity probe at **its own** prep term and
**its own** shape reporting `✅ Expected Falsified`; concrete accepting CEK witness;
shape realizability theorem. **Every one of the now-13 re-cut shapes meets it in full
in the library** (T1R, T2R, T6R, T7R, G1R, G6R, M1R, M2R, L1R, **L2R**, DT1R, DS1R,
S1R). There is no longer a 3/4 row.

**M2R (F17) — LANDED at `f4486ca`, and G3 verified the landing.** The real compiled
`programmableTokenMinting` bytecode **accepts** `M2RWitness.ctx` through
`appliedMintRShapedIdx900.exec` — the same shaped applied term the module's five
property theorems quantify over — and the exact step count is **K = 784, pinned
TWO-SIDED** (halts at 784, budget-errors at 783), **byte-identical to SHAPE M1R's**.
Both carry `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler,
Quot.sound]`: **0 project axioms, no `sorryAx`**. `WSC/Props/Shaped/P4ShapedRIdx.lean:174-194`.
G3 checked, by unfolding `mintingPolicyInputs900` and `mintRInputsIdx`, that the
K-measurement and the acceptance are about the **same run** — see `AUDIT.md` §7.6.1.
Zero solver verdicts added.

**L2R (F19) — NEW at `f4486ca`.** `WSC/Shaped/MintingLocalShapedRIdx.lean` is SHAPE
L1R with the `Local` arm's registration reference-input index left **symbolic**, cut
over the node-realizable two-entry redeemer map. It **definitionally contains** SHAPE
L1R (`localRCtxIdx_at_one`, by `rfl`), so `P4_local_noEscape_RIdx` strictly
strengthens `P4_local_noEscape_R` and **supersedes** the retired
`P4_local_noEscape_shapedIdx`. **Cite `P4_local_noEscape_RIdx`.** Two riders travel
with the citation, both stated in-source:

* The headline is **derived** from `P4_local_RIdx_negative_control` (`✅ Valid` at a
  300 s Z3 cap) via `halt_not_error`, because the *direct* goal is
  `⚠️ Undetermined`. The negative control is strictly **stronger** — `isSuccessful`
  and `isUnsuccessful` are `True` on disjoint `State` constructors — so nothing is
  lost, but a reviewer should know which statement the solver saw.
* **C1 at SHAPE L2R is `⚠️ Undetermined` at the 300 s cap and is NOT asserted as a
  theorem.** C1 at the concrete-index SHAPE L1R (`P4a_local_R`) is unaffected.

The loosened index is demonstrably **live**: `L2RWitness.ctxIdx0` at `regIdx = 0` is
ledger-valid, redeemer-covered, satisfies `noEscape`, and is **rejected** by the real
bytecode.

**Every witness K is unchanged by the re-cut** — evidence that the validators never
dereference `txInfoRedeemers`, except `DelegateSeize`, whose K was re-measured (1466).

Scope caveats per property are in `WSC/README.md` §2.2 and are binding.

---

## 3. COMPOSITION

Four `LeafSet` terms now exist. They are not interchangeable, and the table is the
whole point:

| term | class | class empty? | bytecode leaf | acceptance used? | leaf hyps | project axioms at the top |
|---|---|---|---|---|---|---|
| `ShapeRealizability.t1VacuousLeaves` | SHAPE T1 (pre-re-cut) | **PROVED EMPTY** | `absurd` | — | — | worth nothing; `t1_no_honest_step` proves no step can fire |
| `Composition.containedLeaves` | `ContainedTx` (inert accounting) | no | **none** | **NO** (5 linter warnings) | 0 | **26** |
| `RealizableLeaves.realizableLeavesNS` | **`T1RShapeNS`** (re-cut, realizable) | **no — certified inhabitant** | **`p1` = `WSC.P1R_T1`** | **YES** | **0** | **28** (= 26 + `LR_BUDGET_global` + `TS3`) |
| `RealizableLeaves.realizableLeavesS1R` | **`S1RShape`** (re-cut, realizable) | **no — 2 of 3 conjuncts certified** | **`p2` = `WSC.P2b_R_containment`** | **YES** | **0** | **28** (= 26 + `LR_BUDGET_seize` + `nodeStepsSeize`) |

**The two-axiom delta is the price of making the bytecode load-bearing** and is the
most informative number in the audit. `realizable_inhabitant{,_NS,_S1R}` prove the
classes non-empty with **0 project axioms and no `sorryAx`**.

**How the shape leaves are discharged — a real ledger argument, not hand-waving.**
`NoSeizeWdrl hp ctx := credentialInWithdrawals hp.seizeLogicCred …txInfoWdrl = false`
makes `p2`'s hypotheses *contradictory* through `validScriptInfo`'s `RewardingScript`
clause (`CardanoLedgerApi/V3/Contexts.lean:1014`, transcribing Conway rewarding
`scriptsNeeded`, `Alonzo/UTxO.hs:375-384`): a rewarding script runs only for a
credential the transaction actually withdraws at. `p2_of_noSeizeWdrl` carries **no
`sorryAx` and no `native_decide`** — machine-checkable evidence that no seize
bytecode is reachable from it. `NoGlobalWdrl`/`p1_of_noGlobalWdrl` is the mirror.

**Three restrictions a reader must carry with the "N = 0":**

* `T1RShapeNS` is strictly **smaller** than `T1RShape` — it excludes transfers whose
  second script withdrawal *is* the seize script. That exclusion is the entire content
  of "discharged by the shape".
* `S1RShape`'s `SeizeWithinBudget` conjunct is about the **opaque**
  `WSC.nodeStepsSeize` and therefore **cannot be checked at the witness** — the class
  is certified inhabited for two of its three conjuncts, and the module says so.
* `S1RShape`'s `mlCS = key` / `mCS = key` conjuncts restrict to the **seized** policy.
  `P2b_R_containment` is about that policy alone while `LeafSet.p2` demands containment
  for *every* policy; without those conjuncts `p2` is **false** on seize acceptance
  alone, for a positive mint of a non-seized policy sent off-base.

**The honest limit on "non-empty":** `WSC.OnChain` is an opaque axiom, so no term in
this library can prove any concrete context genuinely on-chain, and `HonestTx`
requires that. For SHAPE T1 emptiness is a **theorem**; for the re-cut shapes there is
no emptiness proof and the one obstruction that emptied their predecessors is
machine-checked absent. That is weaker than "provably inhabited on-chain", and the
difference must not be elided.

---

## 4. COVERAGE — STATED, AND ANSWERED "NO"

`WSC/Coverage.lean` (840 lines) + `WSC/COVERAGE.md` (440 lines). This is the newest
and, for a reviewer, the most important artifact in the campaign.

* `Covers fam Valid Bound := ∀ ctx, Valid ctx → Bound ctx → ∃ S ∈ fam, S ctx`, with
  each family member the literal **range** of a shape builder (12 of them, 421 free
  leaves in total = the entire symbolic surface of the campaign).
* `SizeBound mIn mRef mOut mWdrl mMint` constrains **only** the five list dimensions a
  reviewer means by "size". That omission is the crux, not an oversight.
* **`not_covers_at_T1R_size : ¬ Covers recutFamily ValidRewarding (SizeBound 2 2 2 2 0)`**
  — refuted at SHAPE T1R's own size, by three witnesses that differ from the certified
  inhabitant in **exactly one** `Data`-skeleton feature each (two signatories; a third
  reference input; an `always` validity range) with every leaf scalar untouched. All
  three are `validRewardingContext ∧ redeemersExactAllPlutus`, all three are **accepted** by
  `Runs.globalRun 4400`, and all three cost **exactly 2,603 steps** —
  `missed_transactions_cost_exactly_2603_steps`, byte-identical to `K_T1R_is_2603`.
  **0 project axioms, no `sorryAx`.**
* **Transcription control:** `ctxOk_in_family` puts the certified inhabitant *inside*
  `rangeT1R`, so `¬ Covers` cannot be an artefact of a mis-copied binder list.
* **`family_invariants`** proves all twelve shapes freeze ≤1 signatory, ≤2 reference
  inputs, a **finite** validity lower bound, `txInfoTxCerts = []` and `txInfoData = []`
  — 12 proofs, by computation, **no solver**.
* **The arithmetic, machine-checked (`native_decide`), deliberately a LOWER bound:**
  the smallest bound admitting a real transfer (1 input, **2** reference inputs, 1
  output) contains **9,269,489,664** `Data` skeletons ≈ **971 CPU-years** for one
  property at the measured 3.3 s/shape. At T1R's own bound: 3.05×10¹⁴ skeletons ≈
  3.2×10⁷ CPU-years. **Enumeration is out of reach at every meaningful bound.**
* **The one positive result:** `p3_lives_over_a_covering_class` — **P3 is proved over
  a fully symbolic context and therefore needs no coverage argument at all.** It is
  the only property in the campaign of which that is true, and the existence proof for
  the recommended route.

**"Coverage is false" ≠ "coverage is impossible."** The Lean artifact refutes coverage
for *this family at these bounds*; that a larger family could not cover a smaller
bound is argued from **arithmetic only** and is **not** a theorem. `COVERAGE.md` says
so and no theorem asserts it.

---

## 5. THE SHAPE BRIDGE AND THE BUDGET BRIDGES

* `WSC/ShapeBridge.lean` proves the bridge for **16** shapes, all at `exec` level by
  kernel-checked `rfl` (no `sorryAx`; `inputs_M1` depends on **no axioms at all**).
  **None of those 16 is consumed by anything** — they are all at pre-re-cut shapes.
* **Two bridges ARE consumed:** `exec_T1R`/`bridge_T1R` (C4) and — new in stage 11 —
  `exec_S1R`/`bridge_S1R`, applied in `p2_on_S1RShape`. Both `exec_*` are
  kernel-checked `rfl` with **0 axioms**; both `bridge_*` are `blaster`, `✅ Valid`,
  0 project axioms. The other 10 re-cut shapes have **no** `ShapeBridge` entry;
  writing them is mechanical, consuming them is not.
* **Budget bridges: three of seven published instantiations are now exercised.**
  `LR_BUDGET_base` at `K_base = 600` (in `p3_lifted`); `LR_BUDGET_global` at
  `K_global = 4400` (in `shapedGlobalContainment_T1R`), whose non-vacuity side
  condition is *discharged* by `NonVacuity.globalNonVacuous_at_4400`, not assumed;
  and — **new** — `LR_BUDGET_seize` at `K_seize = 3800` (in `p2_on_S1RShape`).
  `LR_BUDGET_minting` is still applied by **nothing**.

---

## 6. AXIOM BASE — WHAT IS ASSUMED

51 declarations; **28** reached by each strongest composed result; **0** under the
shaped layer. See `WSC/README.md` §3.2 for the enumerated 26 + 2, and `WSC/AUDIT.md`
§3 for the per-theorem table.

The 21 that no top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_minting`, `DIRWF`,
`TS1`–`TS5` (less `TS3`), `TS_MINTING_IDENTITY`, `LR_REDEEMER_COVERAGE`, and the two
`*_faithful` axioms — are what a *fuller* bytecode discharge of the leaves would add.
**Read 26/28 as a floor, not a ceiling.**

`LR_REDEEMER_COVERAGE` (`WSC/Honest.lean`, LR-CTX audit row S) is reached only by the
emptiness proofs of the **retired** shapes, so it weakens negative results and
strengthens nothing (see F18).

---

## 7. DEFECTS — CURRENT LEDGER

| id | severity | status | summary |
|---|---|---|---|
| **F2-coverage** | CRITICAL | **OPEN — and now PROVED FALSE** | No argument that the shapes exhaust the transactions the claim is about, and stage 11 replaced that absence with a machine-checked refutation at T1R's own size. **The binding constraint on the whole deliverable.** |
| **F1** | CRITICAL | **NARROWED TO A RATIO** | Both composed results have complete `LeafSet`s (N = 0), but **1 of 4 leaves is the bytecode and 3 are the shape** on each side. Closing `p2` cost zero axioms and added zero bytecode content. For the general class nothing is proved. |
| **F2-realizability** | CRITICAL | **REPAIRED (13/13)** | Shapes re-cut to satisfy Conway `hasExactSetOfRedeemers`; verified in both directions (new shapes pass, old shapes fail, 13/13 goldens match). SHAPE **L2 is now re-cut as L2R** (G1, `f4486ca`), so there is no longer an unrepaired shape. Note the rule the shapes are checked against is the **all-Plutus** specialisation — see F18. |
| **D6** | HIGH | OPEN | Blaster emits kernel-ill-typed `dite'` when a CIP-153 `Value` builtin result stays symbolic. Blocks SHAPES T3/T4, hence P1 dispatch Paths B/C and input-side aggregation. Needs an upstream fix. |
| **F8** | MEDIUM | OPEN, **now binding on BOTH composed results** | `PropExecFaithful`: theorems on `.prop`, witnesses on `.exec`, equality unproved and deliberately not axiomatized. All 12 re-cut groups inherit it; so do both composed results, via `bridge_T1R` and `bridge_S1R`. |
| **F4** | MEDIUM | OPEN by nature | "`sorry`-free" is false; **101** results are `admit`-closed and every top-level theorem carries `sorryAx`. |
| **D5** | was HIGH → **MEDIUM** | **PARTIALLY REPAIRED** | Revision now recorded in three places; verified offline bundle in `WSC/substrate/` reconstructs the pinned tree byte-identically; `WSC/REPRODUCE.md` is the third-party recipe. **Still open:** branch unpublished, path absolute, rev not enforced by lake. |
| **F20** | MEDIUM | **PROCESS FIX ADOPTED** | One stage-11 unit (E2) delivered **nothing**; a second (E3) produced correct work but left it uncommitted in scratch. No instrument could see either, because every instrument measures what EXISTS. E5 landed E3's work. **G3 adopted the fix as a procedure** (`AUDIT.md` F20): existence check before measurement; deltas reconciled to source **lines**, not totals; definitions the claim depends on are unfolded and read. At G3 both G-stage units passed the existence check outright. |
| **D11 / F17** | was MEDIUM | **CLOSED — LANDED (G1, `f4486ca`)** | `M2RWitness.exec_accepts_at_900` and `K_is_784` **pinned two-sided** are in `P4ShapedRIdx.lean:174-194`. 0 project axioms, no `sorryAx`, 0 new solver verdicts. G3 verified the acceptance and the K-measurement are about the **same run**, by unfolding `mintingPolicyInputs900` and `mintRInputsIdx`. SHAPE M2R meets 4/4. |
| **F19** | LOW | **CLOSED (G1, `f4486ca`)** | SHAPE **L2R** exists (`WSC/Shaped/MintingLocalShapedRIdx.lean`), is node-realizable, definitionally contains L1R (`localRCtxIdx_at_one`, `rfl`), and carries all four bar items. **Cite `P4_local_noEscape_RIdx`**, not the retired `P4_local_noEscape_shapedIdx`. Two riders: the headline is **derived** from a `✅ Valid` negative control (the direct goal is `⚠️ Undetermined` at a 300 s cap) via `halt_not_error`, which is strictly stronger, not weaker; and **C1 at L2R is `⚠️ Undetermined` and is not asserted**. |
| **F21** | INFO | **NEW (G3)** | The clean-room log carries two lines beginning `Error:` — a `panic!` from CLAB's `Recursor.all` macro at `V3/Contexts.lean`. Benign (definition elaborates, exit 0) and **pre-existing** (present in the C4-era log at the same definition). Recorded because the "zero errors" instrument is a line-anchored, case-sensitive grep and does not see them. |
| **F22** | INFO | **NEW (G3)** | `bridge_GIdx` / `bridge_GNIdx` (`ShapeBridge.lean:900-948`) are the only results over `appliedGlobalShapedIdx1600` / `appliedGlobalShapedNIdx1600`, and neither term has a vacuity probe, a concrete witness, or a reduction lemma to `globalShapedCtx` — `GlobalShapedIdx.lean` is defs-only. An `↔` between two unsatisfiable statements is true. Not load-bearing (cited only in narrative), so informational; cheap fix is one `rfl` lemma inheriting `bridge_G1`'s witness. |
| **D12 / F18** | LOW | **RESOLVED (task G2)** | The faithful rule is **not expressible** in `TxInfo` — it needs `isNativeScript`, a predicate on a script BODY, and `TxInfo` carries only hashes (the companion `scriptsProvided` filter is a no-op, guaranteed by `babbageMissingScripts`). So: predicates renamed `…AllPlutus` at every use site; the true rule stated modulo a language oracle with the two directions now THEOREMS (`redeemerCoverageModNative_of_allPlutus` positive; `coveredByNonNative_strictly_weaker` / `noExtra_not_conservative` negative, all at `[propext, Quot.sound]`); every negative use audited one by one (`ShapeRealizability.lean` §2.3) — **6 unaffected** (spending route), **6 downgraded** to an explicit `¬ isNative w` side condition now carried in the TYPE via `RedeemerCoverageAt w`, **1 measurement** whose interpretation only is downgraded. `g6_class_is_empty_nonNative` is the axiom-free true-rule form of the one unconditional negative result. Positive results, leaves and both composed containment theorems are untouched. |
| **`SeizeWdrlOfScoped`** | MEDIUM | OPEN, newly tractable | `LR5` does not entail `seizeCred ∈ txInfoWdrl`. The same rule in the other direction is now audit row S, and is what discharges the shape leaves in §3. |
| **`ValueAlgebra`/`LedgerCanon`** | MEDIUM | OPEN | Uninstantiated, so `LR_BALANCE_SLOT` stays an axiom. `valueOf` is not additive over `merge` without canonicity (machine-checked counterexample). ~330 lines. |
| **F5** | MEDIUM | **CLOSED** | Prep-cost table was ~47× pessimistic (`lake env lean` without `--load-dynlib`). Re-measured; `K-MEASUREMENTS.md` §5.1a carries correct figures. |
| **F7** | — | **CLOSED** | Every `*NonVacuous` obligation discharged, all `native_decide`, 0 project axioms. |
| **F13 / F14** | — | **CLOSED (C3)** | Stale seize ExBudget rows corrected; the false `PROVENANCE.md` note removed. |
| **F16** | — | **CLOSED (C4)** | A closed inhabitation statement about a named concrete context now exists (`t1RShape_witness`, `s1RShape_witness`). |

---

## 8. WHAT WOULD MOVE THE NEEDLE, IN ORDER

The order changed at E5, because coverage now has a measured answer and the honest
conclusion is to stop trying to close it by enumeration.

1. **Fix D6 upstream and invest in UNSHAPED prep/solve cost.** This is now the highest
   -value item, on the campaign's own measurements: the only property that needs no
   coverage argument (P3) is the only unshaped one, and the obstacles to unshaped work
   are **engineering defects with named reproductions** — unshaped global prep is
   45.5 s at 1600 but never completes at 3300; the unshaped P5 solve was killed at
   5,241 s ≈ 87 min with no verdict against ≈2 s shaped
   (`WSC/SHAPING-RESULTS.md:11`); unshaped seize prep at 2000 never completed in
   77 min. Route A's obstacle, by contrast, is arithmetic (971 CPU-years) and cannot
   be engineered away.
2. **Push the PCB branch and restore a real git pin (D5).** One line, and until it is
   done the bundle's custody is the only thing making this checkable elsewhere.
3. **Discharge more leaves from the bytecode, changing the RATIO rather than N.**
   The measure that matters is 1-of-4 → 2-of-4. Needs `p4` at a minting shape and
   `nopre` at a registration shape, composed into the same class — i.e. a union
   `Shape` over several re-cut shapes.
4. **Bridge and consume the other re-cut shapes** (`exec_<S>R` by `rfl`,
   `bridge_<S>R` by `blaster`, ~1 s each on the evidence of `bridge_T1R`/`bridge_S1R`).
5. **Instantiate `ValueAlgebra` + `LedgerCanon`**, removing `LR_BALANCE_SLOT` from the
   axiom base.
6. **Restate the shaped groups on `Runs.XRun K`** with fresh vacuity probes, to
   delete `PropExecFaithful` (F8) campaign-wide. Real risk: one may come back `Valid`,
   i.e. vacuous, as happened to P6 at 2500.
7. **A shape-coverage programme — DO NOT START ONE.** `COVERAGE.md` recommends against
   it on the campaign's own arithmetic. The fallback if (1) stalls is the source-model
   route with an explicit faithfulness axiom — a *stated* trade, which is more than any
   affordable coverage programme offers.

**Removed from this list at G3, because they are DONE:** "land M2R's CEK witness
(F17)" and "re-cut SHAPE L2 (F19)". Both landed at `f4486ca` and were verified at G3
(`AUDIT.md` §7.6.1, §7.6.2).

**Also NOT recommended at G3: further loosening rungs of the L2R kind.** L2R was
worth doing because it retired a theorem quantified over a *proved-empty* class. But
it cost a 300-second solver cap, left C1 `⚠️ Undetermined`, and moved the
code-to-shape ratio **not at all**. Loosening rungs buy narrowness, not coverage.

**House rule adopted at G3 (from G1's measurement):** Blaster's default solver
timeout is **infinity** (`Blaster/Command/Syntax.lean:15`), and an uncapped goal at a
new shape ground for >13 minutes with no diagnostic. **Every `blaster` call in a new
shape must carry an explicit `(timeout: …)`.** On `Undetermined` the tactic leaves
the goal open rather than admitting (`Blaster/Command/Tactic.lean:47-50`), so a cap
is a hang guard and not a soundness hole.

---

## 9. REPRODUCTION

Full third-party recipe, including substrate reconstruction: **`WSC/REPRODUCE.md`**.

```bash
# the whole library, clean-room
#   G3 (f4486ca): 432 jobs, 1:46-2:10, 162 ✅ markers (103 V + 59 F), 0 errors,
#       0 ⚠️, 20 expected `sorry` warnings, 94 WSC modules, 5 `unused variable`,
#       RSS 1.50-1.66 GB (LOAD-DEPENDENT — not an instrument)
#   E5 (7039cdb): 431 jobs, 1:39-1:57, 159 ✅ markers (102 V + 57 F), 93 WSC modules
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# the axiom census behind §6 and AUDIT.md §3 — PARSE ACROSS NEWLINES.
#   A line-oriented grep undercounts sorryAx as 17; the true figure is 37.
#     Composition.containment_on_contained_class        -> 26
#     RealizableLeaves.containment_on_realizable_class  -> 28 (26 + LR_BUDGET_global + TS3)
#     RealizableLeaves.containment_on_seize_class       -> 28 (26 + LR_BUDGET_seize + nodeStepsSeize)
#     RealizableLeaves.realizable_inhabitant{,_NS,_S1R} -> 0, no sorryAx
#     Coverage.not_covers_at_T1R_size                   -> 0, no sorryAx

# the shaped layer adds no assumption
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0

# the re-cut, both directions
#   RealizableShapes.all_recut_witnesses_redeemersExact
#   RealizableShapes.all_old_witnesses_fail_c3_coverage
#   Goldens.Audit.every_golden_is_redeemer_covered          # 13/13

# prep-cost re-measurement (F5's repair) -- ALWAYS `lake build`, never `lake env lean`
for m in Base Minting900 Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.{olean,ilean,trace}
  /usr/bin/time -f "$m %e s" lake build WSC.Prep.$m > /dev/null
done                                        # expect ~1.6 / 1.5 / 36-46 s

# PROVENANCE re-verification (AUDIT.md §6.1) -- 4/4, re-verified at E5
sha256sum WSC/flats/*.flat

# SUBSTRATE re-verification (AUDIT.md §6.2) -- see WSC/substrate/README.md §3
git bundle verify WSC/substrate/pcb-cip153-value-builtins.bundle
```

Companion documents: `WSC/AUDIT.md` (**authoritative** — the clean-room re-audit, the
censuses, the provenance and substrate re-verification, the per-unit verification of
stage 11, the ranked findings, and "what a reviewer should not believe"),
`WSC/README.md` (reviewer-facing summary), `WSC/EXEC-SUMMARY.md` (one page, no Lean),
`WSC/COVERAGE.md` (the coverage question and its answer), `WSC/REPRODUCE.md`,
`WSC/substrate/README.md`, `WSC/ARCHITECTURE.md` (binding; ADDENDUM v3 overrides the
base text), `WSC/SHAPE-BRIDGE.md`, `WSC/SHAPING-RESULTS.md`, `WSC/SPIKE-FINDINGS.md`,
`WSC/LR-CTX-AUDIT.md`, `WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md`.
