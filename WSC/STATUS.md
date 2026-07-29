# WSC containment campaign — AUTHORITATIVE STATUS

> # ⛔ TASK R1 (2026-07-28) — **BOTH FAITHFULNESS AXIOMS ARE RETRACTED**
>
> `WSC.Model.globalModel_faithful` and `WSC.SeizeModel.seizeModel_faithful` are
> FALSE and have been **DELETED**, with every declaration that rested on them
> (`P1_bytecode`, `P1_bytecode_of_P1_model`, `P6_bytecode`,
> `P6_bytecode_of_P6_model`, `P2a_bytecode`, `P2b_bytecode`,
> `P2b_model_implies_bytecode`). **Findings F24 and the N5 seize half are CLOSED.**
> Machine-checked refutations: `WSC/Model/GlobalModelRefuted.lean` (new) and
> `WSC/Model/SeizeModelRefuted.lean`. Full disposition: `WSC/AUDIT.md` entry **R1**.
>
> **Measured cost: ZERO.** Clean-room before/after — **445 jobs** (was 444, +1
> module), **175 verdicts (110 `✅ Valid` + 65 `✅ Expected Falsified`) — identical**,
> 0 `⚠️`/`❌`, 0 errors, 20 `sorry`, 5 unused-variable; project axioms under
> `top_claim` **25 → 25**, under both `containment_on_*_class` **28 → 28**.
> Neither axiom ever appeared in the transitive axiom set of any composed result;
> the only two audited results that reached one (`P2a_bytecode`,
> `P2b_model_implies_bytecode`) are themselves deleted. Axiom DECLARATIONS under
> `WSC/`: **47 → 45** (and see AUDIT R1.4 — the published "51" was a grep artefact).
>
> **This is a STRICT improvement.** Every property is proved at UPLC against the
> compiled bytecode; the models were the B3 fallback from a wall that shaped
> contexts removed. **One thing is genuinely lost and is reported as a loss:** the
> library no longer has any UNBOUNDED statement about the seize path. P2 against
> production is `WSC/Props/Shaped/P2ShapedR.lean`, bounded by budget 3800 and
> SHAPE S1R.
>
> `WSC/Model/*` is KEPT, demoted, with **no axiom and no bridge**, in two clearly
> marked categories: TRUE LEAN FACTS ABOUT A STALE MODEL (`pathC_sound`,
> `accum_lookup`, the `mintWalk_*` sublist lemmas,
> `P2a_seizeModel_preserves_structure`, the `tokensContain_unsound_*`
> counterexamples — all still true, none about production) and SPECIFICATION
> VOCABULARY consumed by the live UPLC theorems (`Model/Ground.lean`'s
> `outSum`/`inSum`, `mintSigned`/`mintPosOf`/`coveringNodeExists`/`paramsPinned`,
> `P2.sumOutAtBase`/`sumInAtBase`, the seize redeemer projections).
> `Model/Ground.lean` no longer imports the transcription at all.


> # ⚠️ POST-#112 (task N6, 2026-07-28) — READ `WSC/AUDIT.md`'s BANNER FIRST
>
> This file was written against the PRE-#112 wsc-poc bytecode. wsc-poc PR #112
> (`main` @ **2306678**) changed three of the four validators SEMANTICALLY; the
> minting policy is byte-identical. Tasks N1–N6 re-based everything.
>
> **The current measurements are (task H2, 2026-07-28): 444 jobs, 0 errors,
> `175` solver verdicts (`110 ✅ Valid` + `65 ✅ Expected Falsified`),
> 0 `⚠️`/`❌`, 20 `sorry`, 5 unused-variable, 106 WSC modules, two clean-room
> runs, wall 10:25 / 10:35, peak RSS ≈ 4.35 GB.**
> The delta over the N6 census (440 / 170 / 102) is tasks H1 (SHAPE T8R's
> certified inhabitant — no new solver verdicts) and H2 (SHAPES T3R/T4R:
> +3 modules, +2 `✅ Valid`, +3 `✅ Expected Falsified`). Both composed results survive with **28** project axioms
> each and **1 of 4** leaves discharged by the bytecode on each side — unchanged
> — but `top_claim` now carries one NEW hypothesis, `WdrlPairShaped Shape`.
>
> Everything that changed, with measurements: `WSC/AUDIT.md` (top banner) and
> `WSC/status-fragments/N6-compose-and-reaudit.md`. Numbers in the body below
> that disagree with the ones above are the pre-#112 record.

---


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

## 0-N6. THE SEVEN SENTENCES, RE-STATED AT wsc-poc `main` @ 2306678 (PR #112)

**This section SUPERSEDES §0 below, sentence by sentence. §0 is kept because the
history is part of the record.**

1. **The top claim is still NOT PROVED**, and it is now narrower. *In an honest
   deployment, programmable tokens cannot exist outside the mini-ledger.* What
   exists is (a) a machine-checked **reduction** to four leaf obligations plus
   **25 project axioms** (`Composition.top_claim`) — which now ALSO takes
   `WdrlPairShaped Shape`, a side condition on the transaction class that PR #112
   forced in; (b) that reduction discharged over one inert accounting class,
   **intersected with `WSC.WdrlPair`**; and (c) that reduction discharged with NO
   remaining leaf hypothesis over the same TWO node-realizable shape classes,
   `containment_on_realizable_class` (transfer, `T1RShapeNS`) and
   `containment_on_seize_class` (seize, `S1RShape`), each depending on **28**
   project axioms — *unchanged from pre-#112, measured*.
2. **"N = 0" IS STILL NOT THE MEASURE. THE RATIO IS, AND IT DID NOT MOVE.**
   One of four leaves is the production bytecode with its acceptance hypothesis
   genuinely consumed; three of four are the shape — on *each* side, exactly as
   before:

   | class | `p1` | `p2` | `p4` | `nopre` |
   |---|---|---|---|---|
   | `T1RShapeNS` (transfer) | **BYTECODE** (`P1R_T1` @ 4400) | shape + ledger rule | shape | shape |
   | `S1RShape` (seize) | shape + ledger rule | **BYTECODE** (`P2b_R_containment` @ 3800) | shape | shape |

   A fifth bytecode result is on the critical path and always was:
   `p3_lifted` consumes `P3_B1W_run` (`programmableLogicBase` @ 600, SHAPE B1W)
   inside branch C. It is not a `LeafSet` field, so it does not enter this table.
3. **Everything about the bytecode is still BOUNDED BY A CEK BUDGET**, and the
   budgets moved: base 600 (witness K **194**, was 208), global 4400 (T1R K
   **2343**, was 2603), seize 3800 (S1R K **2301**, was 3004), minting 900
   (K 784, unchanged — the minting bytecode is byte-identical).
4. **The shaped results are still bounded by their SHAPE, and coverage is still
   PROVED FALSE** — re-measured at 2306678 and it reproduces exactly: three
   ledger-valid, Conway-redeemer-exact transactions the production bytecode
   accepts in **2,343** steps, byte-identically to the certified inhabitant,
   which no shape in the family contains (`Coverage.not_covers_at_T1R_size`).
   **One thing improved:** P3's new class `WSC.WdrlPair` has a complete,
   both-directions ledger-vocabulary characterisation (`Coverage.wdrlPair_char`)
   — the only class in the campaign of which that is true.
5. **`sorryAx` is still under both composed results** (Blaster closes `Valid`
   goals by `admit`), and `WSC.OnChain`, `WSC.Deployed`, the `LR_*` ledger rules
   and the four `nodeSteps*` are still opaque axioms.
6. **Two results were REFUTED by #112 and are reported as losses, not repaired:**
   `WSC.SeizeModel.seizeModel_faithful` is FALSE at 2306678
   (`WSC/Model/SeizeModelRefuted.lean` settles it by computation on two contexts
   differing in one lovelace leaf), which costs the library its only **UNBOUNDED**
   seize result; and `WSC/Props/Shaped/P2Shaped.lean` (P2 over the pre-re-cut
   SHAPE S1) was DELETED because its structure conjunct is `❌ Falsified` against
   the ada top-up #112 legalised. **UPDATE (task R1): the axiom is not merely
   flagged, it is DELETED**, together with `P2a_bytecode`, `P2b_bytecode` and
   `P2b_model_implies_bytecode`; and `WSC.Model.globalModel_faithful` went with
   it, for two independent reasons (F24, plus a budget defect that predates
   #112). See the R1 banner at the top of this file.
7. **The reproducibility caveat got WORSE.** Two of the four production
   validators — `programmableLogicGlobal` **and now `programmableSeize`** — do
   not DECODE at all without the unpublished `cip153-value-builtins`
   PlutusCoreBlaster branch, which additionally needed a seventh builtin
   (`ScaleValue`, flat tag 100) added by task N5; and Blaster is now a local
   unpublished pin too (`wsc-d6-dite-branch-retype`, one commit) without which
   the global-1600 and seize preps die in the kernel. **Nothing in this library
   is reproducible off this machine until three branches are published.**

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
   bracket-only parser reports 167 results instead of the true **172** (at HEAD
   `f4486ca`, before the H2 cleanup: 169 vs 174 — the trap is the parser, not the
   number).
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

> **⚠️ ONE REVISION LATER — THE DEAD-FILE CLEANUP (task H2).** Six modules were
> deleted for PR submission. **The verdict count did not move**: still **162 =
> 103 `✅ Valid` + 59 `✅ Expected Falsified`**, still 0 errors, 0 `⚠️`/`❌`, 20
> `sorry` warnings, 5 unused-variable, and the per-verdict reconciliation is still
> exactly 101 + 2 + 59. Four rows of the table below moved: **jobs 432 → 431**,
> **WSC modules 94 → 93**, **`#print axioms` results 174 → 172** (`sorryAx`
> unchanged at 37; `native_decide` 72 → 70; zero-project-axiom 124 → 122; the two
> removed results were both builtins-only), wall **1:49–2:00** with a same-load
> pre-change control at 2:35. `axiom` declaration counts (51 / 0) are unchanged.
> The full decision table for every file in the tree is **`AUDIT.md` §12**.

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
| **P1** | PROVED, **PATH A and PATH C** (B reached, not isolable — see below) | `P1R_T1/T2/T6/T7/T8` (`P1ShapedR.lean`); **`P1BC_T3R`, `P1BC_T4R`** (`P1ShapedBC.lean`, H2) | 4400 / T1R, T2R, T6R, T7R, **T8R**, **T3R**, **T4R** | **2343 / 2567 / 2777 / 2567 / 2288 / 1936 + 2228 / 2696** — all pinned two-sided | `t1R…t7R_realizable`, **`t8R_realizable`** (H1), **`t3R_realizable`, `t3R_realizable_pathC`, `t4R_realizable`** (H2) | **4/4 — every row, T8R/T3R/T4R included** (F23 closed at H1) |
| **P2** | PROVED — P2b unchanged; **P2a RESTATED** for #112's ada top-up | `P2a_R_structure`, `P2b_R_containment`, `P2a_R_ada_only_tops_up` (`P2ShapedR.lean`) | 3800 / S1R | **2301** (accept) / **2412** | `s1r_realizable(Exact)` | **4/4** |
| **P3** | PROVED, **SHAPED (regressed at #112)** | `P3_base_requires_global_or_seize_run_B1RG` / `_B1RS` (`P3_BaseRun.lean`), `P3_B1W_run` (`P3_BaseWdrl.lean`) | 600 / B1RG, B1RS, B1W | golden **194** | ✅ at each shape's own prep AND run term | `b1RG_realizable`, `b1RS_realizable`, `b1W_realizable` |
| **P4** | PROVED, all four arms | `P4_disjunction_at_{L1R,DT1R,DS1R}`, `P4_burnonly_arm_R`, **`P4_local_noEscape_RIdx` (L2R)** | 900 / M1R, M2R; 2500 / L1R, **L2R**, DT1R, DS1R | 784 / **784** / 1681 / **1681** / 1257 / 1466 | `m1r,m2r,l1r,dt1r,ds1r_realizable`; L2R via `L2RWitness.ctx_realizable` | **4/4 — every row, M2R included** (F17 landed at `f4486ca`) |
| **P4a** | PROVED | `P4a_R_*`, `P4a_RIdx_*`, `P4a_local_R` | as P4 | as P4 | as P4 | as P4 |
| **P5** | PROVED | `P5R_shaped_indexed/_exists/_groundtruth` (`P5ShapedR.lean`) | 1600 / G1R | **1402** | `g1R_realizable` | **4/4** |
| **P6** | PROVED | `P6R_shaped_member_adds_to_requirement`, `_mint_stays_at_base`, `_noBaseInputs` | 3300 / G6R | **2196** | `g6R_realizable` | **4/4** |

The four-point bar is: theorem `✅ Valid`; vacuity probe at **its own** prep term and
**its own** shape reporting `✅ Expected Falsified`; concrete accepting CEK witness;
shape realizability theorem. **Every one of the now-14 re-cut shapes meets it in full
in the library** (T1R, T2R, T6R, T7R, **T8R**, G1R, G6R, M1R, M2R, L1R, L2R, DT1R,
DS1R, S1R). There is no longer a 2/4 or 3/4 row.

**T8R (F23) — CLOSED at task H1 (2026-07-28).** T8R was the last shape below the bar
and the only one that reaches the line PR #112 was written to add
(`ownerWdrlIdxs`, ProgrammableLogicBase.hs:386-393). It now carries:

* **(c)** `P1RShapedWitness.exec_accepts_T8R_at_4400`
  (`P1ShapedR.lean:1011`) — the real compiled `programmableLogicGlobal` bytecode
  accepts `ctxSOwn` through `appliedGlobalShapedT8R.exec`, the same applied term
  `P1R_T8` quantifies over. Sameness is not asserted, it is proved twice by `rfl`:
  `p1SOwnInputs_eq_globalInputs` (`:970`, class level, every leaf assignment) and
  `ctxSOwn_is_the_exec_argument` (`:989`, point level). **K = 2288, pinned
  TWO-SIDED** (`K_T8R_is_2288`, `:1036`) — **55 steps BELOW T1R's 2343** at
  otherwise identical leaves, i.e. #112's indexed owner lookup is cheaper than the
  signature check it sits beside, despite one more withdrawal entry.
* **(d)** `t8R_class_covered` (`GlobalRealizability.lean:508`, `RedeemerCovered` for
  every leaf assignment), `t8R_class_coverage` (`:728`,
  `redeemerCoverageAllPlutus = true` in CLAB's own vocabulary) and `t8R_realizable`
  (`:939`) — `validRewardingContext` ∧ `redeemersExactAllPlutus` (BOTH halves of
  Conway's exact-redeemer rule) ∧ `RedeemerCovered` ∧ real-CEK acceptance.
  4 redeemer entries = 1 script input + 0 mint policies + 3 script withdrawals,
  exact.
* **the index made to EARN it.** `exec_rejects_T8R_misindexed_owner` (`:1059`) and
  `exec_rejects_T8R_unwitnessed_owner` (`:1077`) reject two contexts that differ
  from the accepted witness in the SINGLE leaf `sOwn`, are `validRewardingContext`
  and `redeemersExactAllPlutus` (`t8R_rejected_members_are_ledger_legal`,
  `GlobalRealizability.lean:977`), and are refused by the real bytecode. The first
  is the sharp one: its owner's stake script **is** invoked, at withdrawal entry 1,
  while the redeemer names entry 2 — exactly what the pre-#112 membership scan
  accepted.
* **0 project axioms** on all of it, **0 new solver verdicts** (every new result is
  `native_decide` or `rfl`), verdict total unchanged at 170.

⚠ **And a NEGATIVE result found while closing it — see `F24` below.** The
misindexed context is also the first executable proof that
`WSC.Model.globalModel_faithful` is **FALSE** of the post-#112 program. **At task
R1 that axiom was RETRACTED** and this context became half of the retraction
certificate.

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
  `missed_transactions_cost_exactly_2343_steps`, byte-identical to `K_T1R_is_2343`.
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
* **The one positive result, RESTATED AFTER #112 — it got weaker.** This bullet used
  to be `p3_lives_over_a_covering_class`: *P3 proved over a fully symbolic context,
  needing no coverage argument at all, the only property of which that was true.*
  **That is false at 2306678** and the theorem is gone (task N3). The replacement is
  `p3_lives_over_the_wdrlPair_class`: P3 over `WSC.WdrlPair` — withdrawal map of
  length 2, both credentials script credentials — with the redeemer and both script
  parameters still fully symbolic. Its value is that **the class has a complete
  both-directions characterisation in ledger vocabulary** (`wdrlPair_char`, axioms
  `[propext]`), so for P3 alone the coverage question is a fifteen-line theorem and
  not a programme.

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

The ones no top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_minting`, `DIRWF`,
`TS1`–`TS5` (less `TS3`), `TS_MINTING_IDENTITY`, `LR_REDEEMER_COVERAGE` — are what a
*fuller* bytecode discharge of the leaves would add. **Read 26/28 as a floor, not a
ceiling.** ⚠️ **CORRECTED at task R1:** this sentence used to say "21 … and the two
`*_faithful` axioms". Those two axioms are FALSE and have been DELETED, so they are
not on any list of things a fuller discharge would add — a fuller discharge would
never have been allowed to add them. The count also moved because the underlying
`grep -rn '^axiom '` census overcounted by 4 prose lines (AUDIT R1.4): the true
declaration count is 45 after R1, 47 before.

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
| **D6** | was HIGH | **CLOSED — FIXED UPSTREAM (N5), re-tested (N6)** | Blaster emitted a kernel-ill-typed `dite'` when a CIP-153 `Value` builtin result stayed symbolic, because the condition and the branch binders were optimized independently. Fixed by `optimizeDITE` rebuilding both binder types from the final condition — Blaster `wsc-d6-dite-branch-retype` @ **`4d320dd`**. Both reproductions now build (`T3PrepFAILS` 2.4 s, `T4PrepFAILS` 9.4 s, exit 0) and are **relabelled as regression tests**. It also unblocked **D8**, which is why P1/P5/P6 are statable at 2306678. **The limitation it supported was only half lifted at N6** — T3/T4 were pre-re-cut and not node-realizable (T3 needs 3 redeemer entries, supplies 1) — **and is now FULLY lifted at task H2 (2026-07-28)**: SHAPES **T3R/T4R** exist, prep at 4400, and P1 is proved over both. PATH C is proved executed (`T3R_pathC_is_taken`); PATH A is proved excluded at T3R (`T3R_not_path_A`); PATH B is reached and measured (K 1936 vs 2228) but is semantically subsumed by C, so no accept/reject theorem can separate it. See `AUDIT.md` **D6** and **H2 (2026-07-28)**. |
| **F8** | MEDIUM | OPEN, **now binding on BOTH composed results** | `PropExecFaithful`: theorems on `.prop`, witnesses on `.exec`, equality unproved and deliberately not axiomatized. All 12 re-cut groups inherit it; so do both composed results, via `bridge_T1R` and `bridge_S1R`. |
| **F4** | MEDIUM | OPEN by nature | "`sorry`-free" is false; **101** results are `admit`-closed and every top-level theorem carries `sorryAx`. |
| **D5** | was HIGH → **MEDIUM** | **PARTIALLY REPAIRED** | Revision now recorded in three places; verified offline bundle in `WSC/substrate/` reconstructs the pinned tree byte-identically; `WSC/REPRODUCE.md` is the third-party recipe. **Still open:** branch unpublished, path absolute, rev not enforced by lake. |
| **F20** | MEDIUM | **PROCESS FIX ADOPTED** | One stage-11 unit (E2) delivered **nothing**; a second (E3) produced correct work but left it uncommitted in scratch. No instrument could see either, because every instrument measures what EXISTS. E5 landed E3's work. **G3 adopted the fix as a procedure** (`AUDIT.md` F20): existence check before measurement; deltas reconciled to source **lines**, not totals; definitions the claim depends on are unfolded and read. At G3 both G-stage units passed the existence check outright. |
| **D11 / F17** | was MEDIUM | **CLOSED — LANDED (G1, `f4486ca`)** | `M2RWitness.exec_accepts_at_900` and `K_is_784` **pinned two-sided** are in `P4ShapedRIdx.lean:174-194`. 0 project axioms, no `sorryAx`, 0 new solver verdicts. G3 verified the acceptance and the K-measurement are about the **same run**, by unfolding `mintingPolicyInputs900` and `mintRInputsIdx`. SHAPE M2R meets 4/4. |
| **F23** | was MEDIUM | **CLOSED (task H1, 2026-07-28)** | SHAPE T8R was the only shape below the four-point bar, and the only one exercising PR #112's `ownerWdrlIdxs`. It now has (c) `exec_accepts_T8R_at_4400` with **K = 2288 pinned two-sided** and two `rfl` same-term audits, and (d) `t8R_class_covered` / `t8R_class_coverage` / `t8R_realizable`. Plus two rejecting siblings (`exec_rejects_T8R_misindexed_owner`, `…_unwitnessed_owner`) that make the index live. 0 project axioms, 0 new solver verdicts. **14/14 shapes now meet the bar.** |
| **F24** | **MEDIUM** | **RESOLVED (task R1, 2026-07-28) — BY RETRACTION, not by repair** | `WSC.Model.globalModel_faithful` was FALSE of the post-#112 program and **has been DELETED**, together with `P1_bytecode`, `P1_bytecode_of_P1_model`, `P6_bytecode` and `P6_bytecode_of_P6_model`. **Two independent refutations, both machine-checked in `WSC/Model/GlobalModelRefuted.lean`:** (1) SEMANTIC — `global_model_and_bytecode_DISAGREE` runs the real compiled `programmableLogicGlobal` on `P1RShapedWitness.ctxSOwnMisindexed` and it reaches `State.Error` at a 20,000-step meter while `Model.globalModel` returns `true`; the accepting sibling needs 2,288 steps (`K_T8R_is_2288`), so that is a refusal and not budget exhaustion, and the model is **unsound**, not conservative, at PR #112's indexed owner check (`ProgrammableLogicBase.hs:386-393`, redeemer field `:1043-1051`; the model still scans, `gateInput` `:224-236`, and binds `_ownerWdrlIdxsUnmodelled` `:668-676`). Controls on both sides. (2) BUDGET, new at R1 and independent of #112 — `golden_shows_budget_gap`: the axiom's right-hand side is `appliedGlobal1600`, a run METERED AT 1600 CEK steps, while the model accepts the `transfer-member-single-policy` golden whose **K = 2,782, pinned two-sided**. Any axiom of that shape is unsatisfiable at a finite prep budget. **Cost of the resolution: zero.** 175 verdicts before and after, 25/28 project axioms unchanged under every composed result, and `WSC/Shaped/Probe/P1Axioms.lean` had already measured the axiom absent from every shaped P1/P5/P6 theorem. **The 'fix' this row used to propose — re-transcribe `:386-393` into `gateInput` — was NOT done and is not recommended:** it would repair one divergence in a model whose bridge is unsatisfiable for a second, structural reason, on a route the UPLC results have made unnecessary. |
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

1. **D6 IS NOW FIXED — the remaining item is the T3R/T4R re-cut, plus UNSHAPED prep/solve cost.** This is still the highest
   -value item, but the case for it CHANGED at #112 and got weaker: the property that
   used to need no coverage argument (P3) **is no longer unshaped**, so the route has
   lost its worked example. The obstacles to unshaped work remain
   **engineering defects with named reproductions** — unshaped global prep is
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
   it on the campaign's own arithmetic. ⚠️ **CORRECTED at task R1:** the named fallback
   used to be "the source-model route with an explicit faithfulness axiom — a *stated*
   trade". **That fallback is CLOSED.** Both faithfulness axioms the campaign wrote
   turned out to be FALSE, and one of them (`globalModel_faithful`) was
   *unsatisfiable by construction*, because its right-hand side was a run metered at a
   finite prep budget while its left-hand side was not. Stating a trade does not make
   it a safe one; a source-model route is only worth attempting with a bridge that is
   PROVED, not asserted.

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
#   CURRENT (post-H2): 431 jobs, 1:49-2:00, 162 ✅ markers (103 V + 59 F), 0 errors,
#       0 ⚠️, 20 expected `sorry` warnings, 93 WSC modules, 5 `unused variable`,
#       RSS 1.50-1.66 GB (LOAD-DEPENDENT — not an instrument)
#   G3 (f4486ca): 432 jobs, 1:46-2:10, same 162 markers, 94 WSC modules
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
