# WSC containment campaign — FINAL AUDIT (task C4)

**What this file is.** The last technical gate before the campaign is quoted
outside this repository, and the authoritative statement of what is and is not
established. Nothing below is taken on any earlier agent's word — including the
five agents (A1, A2, C1, C2, C3) whose work this audit gates. Every number was
re-measured in a clean-room rebuild on 2026-07-25 at the revision named below; every
claim that could not be reproduced is corrected in place and listed in §8 FINDINGS.

**This revision SUPERSEDES the A3 audit**, which in turn superseded U3. The A3 body
is folded in here finding by finding; its original remains in `git log`
(`416087d`). Where this audit disagrees with A3 the disagreement is stated, not
patched over — and there is one large disagreement, §0.

**THE HEADLINE CHANGE SINCE A3.** A3's two CRITICAL findings were F1 ("the top claim
is proved only where the class, not the code, does the work") and F2 ("no shape
coverage argument exists; **and every shape is unrealizable**"). The second half of
F2 — the sharper half — is now **REPAIRED for 11 of 12 shapes** (tasks C1, C2) and
the repair is machine-checked in both directions. F1 is **partially answered**
(task C4): there is now a `LeafSet` over a shape class that is *not* empty, three of
whose four fields are discharged and one of whose fields is discharged **by the
production bytecode with its acceptance hypothesis genuinely used**. Neither finding
is closed. Both are smaller, and the residue is stated as a number.

Audited revision: branch `wsc-containment-proofs`, HEAD = the C4 commit on top of
`e7329ed`, tree clean.
Environment: 32-core box, Lean 4.24.0, Z3 4.15.2, `maxHeartbeats 0`,
Blaster git `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`
(branch `beta-lambda-cache-optimization`), PlutusCoreBlaster by **local path**
`/home/gumbo/iohk/PlutusCoreBlaster` (branch `cip153-value-builtins`, **unpushed**;
see §8 D5 — `lake-manifest.json` records **no revision at all** for it).

---

## 0. THE ONE-PARAGRAPH ANSWER

The library is internally consistent and its measurements reproduce: **429 jobs,
90–103 s, 158 solver verdicts all ✅, zero errors, zero unexplained `sorry`s**, and the
leaf theorems say what they claim to say in ground-truth vocabulary. Six safety
properties of the four production validators are genuinely proved against the **real
compiled bytecode**, whose provenance is verified end to end (§6). Two things
changed since A3 and they are the only reasons to re-read this file:

1. **The shaped classes are no longer empty.** A3 reported, as a measured fact, that
   every shape in the library was unrealizable as a node-built transaction: the
   shapes baked a one-entry redeemer map while carrying two script withdrawals, and
   Conway UTXOW requires one redeemer entry per script witness. Tasks C1/C2 re-cut
   **11 of the 12** shapes to carry the redeemer entries the rule demands, re-proved
   **every** headline over the re-cut shapes, and certified each with a concrete
   inhabitant satisfying `validXContext` **and both halves of Conway's
   `hasExactSetOfRedeemers`** — the latter transcribed into CLAB by task C3 from the
   ledger source and cross-checked on all 13 goldens (§4b). **Every witness CEK step
   count is byte-identical to before the re-cut** (2603/3572/3150/3572/1541/2837/
   784/1681/1257/1466/3004+3328), because none of the four validators dereferences
   `txInfoRedeemers` except `DelegateSeize`. The one shape not re-cut is **L2**.
2. **A `LeafSet` now exists over a non-empty class, and the bytecode does work in
   it.** `RealizableLeaves.containment_on_realizable_class_of_p2` (task C4) is the
   top claim over `T1RShape`, with `p1` discharged from `WSC.P1R_T1` — the
   production `programmableLogicGlobal` bytecode at budget 4400 — through a new
   shape bridge and `LR_BUDGET_global`. **Its acceptance hypothesis is used**, which
   was false of every previous leaf discharge in this library. `p4` and `nopre` are
   discharged *by the shape* (a pure-transfer transaction mints nothing and
   registers nothing) and say so; `p2` is carried as the single remaining
   hypothesis, i.e. an **N = 1** obligation gap.

The top-level sentence *"in an honest deployment, programmable tokens cannot exist
outside the mini-ledger"* is still **not proved**, and the reasons remain structural:
there is still no shape-**coverage** argument, every bytecode result is still bounded
twice (a CEK step budget AND a fixed `Data` skeleton), `p2` is still open, and 28
project axioms plus `sorryAx` still stand under the composed result. The deliverable
is: six real, controlled, non-vacuous properties of the production bytecode over
named bounded families that are now **node-realizable**; a machine-checked reduction
of the top claim to four leaf obligations plus 28 axioms; and that reduction
discharged three-quarters of the way over one realizable class. Not the claim.

---

## 1. CLEAN-ROOM REBUILD

### 1.1 Method

```
cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-c4
cd <SCRATCH>/clab-c4
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.olean \
       .lake/build/lib/lean/WSC.ilean .lake/build/lib/lean/WSC.olean.hash \
       .lake/build/lib/lean/WSC.ilean.hash .lake/build/lib/lean/WSC.trace
/usr/bin/time -v lake build WSC WSC.ShapeBridge
```

Dependency oleans (`CardanoLedgerApi` and the `PlutusCore` / `Blaster` packages under
`.lake/packages`) were **kept**; every `WSC.*` olean/ilean/trace was deleted. That is
the right cut and a full `lake clean` is not needed: no WSC verdict is computed in a
dependency module — every `#import_uplc`, `#prep_uplc` and `#blaster` lives in a
`WSC/` module — so deleting the WSC oleans forces all of them to run for real.
Confirmed by the log: **90 distinct `WSC.*` modules re-elaborated**, including all 15
shaped/unshaped `#prep_uplc` modules, all 4 `#import_uplc` sites, and all 158 solver
invocations.

### 1.2 Result, against the audited baselines

| measurement | A3 (`80cdac7`) | C1 (`48689b4`) | C2 (`e7329ed`) | **C4 (this audit)** |
|---|---|---|---|---|
| exit status | 0 — 405 jobs | 0 — 416 jobs | 0 — 428 jobs | **0 — `Build completed successfully (429 jobs)`** |
| wall clock | 1 m 38.50 s | 1 m 45.66 s | 1 m 34.93 s | **1 m 30.22 s / 1 m 42.57 s** (two independent runs — quote the range, not a point) |
| user + sys CPU | 275.9 + 33.6 s | — | 379.5 + 50.1 s | **380.4 s + 56.6 s (484 %)** |
| max RSS | 1.65 GB | 1.64 GB | 1.66 GB | **1.65 GB** (1,648,992 KB) |
| WSC modules re-elaborated | 67 | 78 | 89 | **90** |
| `error:` lines | 0 | 0 | 0 | **0** (hard requirement — met) |
| solver verdicts | 101: 66 V + 35 F | 119: 75 V + 44 F | 157: 100 V + 57 F | **158: 101 `✅ Valid` + 57 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` | 0 | 0 | 0 | **0** |
| `declaration uses 'sorry'` | 20 | 20 | 20 | **20** (census §2) |
| `unused variable` warnings | 5 | 5 | 5 | **5** — all at `Composition.lean:2442-2446` (§5.4) |

### 1.3 The verdict delta reconciles exactly, stage by stage

`101 → 158` is `+57`, and every marker is accounted for:

* **C3** (`755d75e…7174e3d`): **+0 jobs, +0 verdicts.** C3's additions are CLAB
  definitions (`scriptPurposesWitnessed`, `redeemerCoverage`, `noExtraRedeemers`,
  `redeemersExact`), `native_decide` golden theorems in `WSC/Goldens/Audit.lean`, one
  new `axiom` (`LR_REDEEMER_COVERAGE`) and audit-table prose. None of those is a
  `blaster` invocation. Verified by differencing the per-file marker table.
* **C1** (`48689b4`): **+11 modules, +18 verdicts** (9 Valid + 9 Expected Falsified) —
  `P1ShapedR` 5 + 5, `P5ShapedR` 2 + 2, `P6ShapedR` 2 + 2. Its six new `#prep_uplc`
  modules and `GlobalRealizability` contribute no verdict (`native_decide` and
  ordinary Lean only).
* **C2** (`e7329ed`): **+12 modules, +38 verdicts** (25 Valid + 13 Expected
  Falsified) — `P4ShapedR` 4 + 2, `P4ShapedRIdx` 3 + 2, `P4LocalShapedR` 6 + 2,
  `P4DelegateShapedR` 7 + 4, `P2ShapedR` 5 + 3. `WSC/Realizability.lean` and
  `RealizableShapes` contribute none.
* **C4** (this task): **+1 module, +1 verdict** — `RealizableLeaves.bridge_T1R`,
  1 `✅ Valid`. `exec_T1R` is `rfl`; everything else in the module is ordinary Lean
  plus two `native_decide`s inherited from C1's witness.

`66 + 9 + 25 + 1 = 101` ✅ Valid and `35 + 9 + 13 + 0 = 57` ✅ Expected Falsified.

Per-file marker table, complete (regenerable from the log):

| file | ✅ Valid | ✅ Expected Falsified |
|---|---|---|
| `WSC/ShapeBridge.lean` | 19 | 6 |
| `WSC/Props/Shaped/P4DelegateShaped.lean` | 7 | 4 |
| **`WSC/Props/Shaped/P4DelegateShapedR.lean`** | **7** | **4** |
| `WSC/Props/Shaped/P4LocalShaped.lean` | 7 | 3 |
| **`WSC/Props/Shaped/P4LocalShapedR.lean`** | **6** | **2** |
| `WSC/Props/Shaped/P1Shaped.lean` | 5 | 5 |
| **`WSC/Props/Shaped/P1ShapedR.lean`** | **5** | **5** |
| `WSC/Props/Shaped/P2Shaped.lean` | 5 | 3 |
| **`WSC/Props/Shaped/P2ShapedR.lean`** | **5** | **3** |
| `WSC/Props/Shaped/P4Shaped.lean` | 4 | 2 |
| **`WSC/Props/Shaped/P4ShapedR.lean`** | **4** | **2** |
| `WSC/Props/Shaped/P4ShapedIdx.lean` | 3 | 2 |
| **`WSC/Props/Shaped/P4ShapedRIdx.lean`** | **3** | **2** |
| `WSC/Props/P3_Base.lean` | 3 | 2 |
| `WSC/Props/P3_BaseRun.lean` | 3 | 1 |
| `WSC/Props/Shaped/P5Shaped.lean` | 2 | 2 |
| **`WSC/Props/Shaped/P5ShapedR.lean`** | **2** | **2** |
| `WSC/Props/Shaped/P6Shaped.lean` | 2 | 2 |
| **`WSC/Props/Shaped/P6ShapedR.lean`** | **2** | **2** |
| `WSC/Shaped/Calib/P3Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Unshaped.lean` | 1 | 1 |
| `WSC/Goldens/Witnesses.lean` | 1 | — |
| `WSC/Prep/Global.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/P4_Minting.lean` | 1 (vacuity BY DESIGN) | — |
| **`WSC/Props/Shaped/RealizableLeaves.lean`** | **1** | — |
| **total** | **101** | **57** |

### 1.4 Source reconciliation — the check that rules out a skipped stanza

Counted over the 90 built modules, with block comments and docstrings stripped first
(A3 did not strip them, which is why its tactic count needed a manual correction):

* **57** active (column-0) `#blaster … (solve-result: 1)` stanzas = "expect
  Falsified" → **57 × `✅ Expected Falsified`**.
* **2** active `#blaster … (solve-result: 0)` stanzas = "expect Valid, i.e. expect
  VACUOUS" (`WSC/Prep/Global.lean:83` `global_vacuity_probe_600`;
  `WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous`) → **2 × `✅ Valid`**.
* **99** `blaster` tactic invocations in theorem position → **99 × `✅ Valid`**.
  (94 written `:= by blaster` on one line; **5** written `:= by` with `blaster`
  indented on the next line — `P3_BaseRun.lean:93,112,141`,
  `Goldens/Witnesses.lean:152`, `P3_Base.lean:210`. A naive one-line grep misses
  those five and lands on 96 instead of 101; recorded so the next auditor does not
  chase the discrepancy.)
* 57 + 2 + 99 = **158**, and the per-file split matches §1.2's table one-for-one.
  **No stanza is unaccounted for and none is skipped.**

### 1.5 Slowest cold modules

`WSC.Prep.Global1600` ≈ 42 s in-parallel, `WSC.ShapeBridge` ≈ 38 s,
`WSC.Shaped.MintingLocalShapedIdx` ≈ 30 s, `WSC.Props.Shaped.P2Shaped` ≈ 25 s,
`WSC.Props.Shaped.P2ShapedR` ≈ 24 s, `WSC.Composition` 5.4 s,
`WSC.Props.Shaped.P1ShapedR` 3.1 s, `WSC.Props.Shaped.RealizableLeaves` 2.6 s,
`WSC.Props.Shaped.P5ShapedR` 2.2 s. Everything else ≤ 7 s. **The re-cut cost
essentially nothing**: the six new global `#prep_uplc` modules are 1.1–1.5 s each,
and the predicted "enlarged redeemer map re-hits the solver wall" risk did not
materialise — 19/19 new queries (18 from C1/C2, 1 from C4) returned a verdict.

---

## 2. SORRY / ADMIT CENSUS

20 `declaration uses 'sorry'` warnings, classified:

| class | count | detail |
|---|---|---|
| **(a)** blaster `admit` on a declaration that reported ✅ Valid | **19** | `WSC/ShapeBridge.lean:{844,857,873,889,909,930,951,970,992,1015,1037,1060,1088,1111,1134,1157,1360,1370,1446}` |
| **(b)** PCB pre-existing, not WSC code | **1** | `PlutusCore/UPLC/CekMachine.lean:299:4` — unchanged |
| **(c)** anything else = DEFECT | **0** | — |

**The warning count is NOT a census and must never be quoted as one (§8 F6).**
`grep -rl 'set_option warn.sorry false' WSC/` returns **37 modules** (A3: 27; C1/C2/C4
added 10), so the ~80 further `admit`-closed theorems in them emit no warning at all.
The authoritative instrument is `#print axioms` → `sorryAx` (§3), and by that
instrument **every one of the 99 `by blaster` theorems in the library is
admit-closed.**

Literal-source grep over `WSC/**/*.lean`:

* **no** literal `sorry`, `admit` or `stop` in tactic position anywhere. All 3
  remaining textual hits are prose inside docstrings ("vacuously discharged", "too
  tight to admit the transactions", "the two budgets whose prep DID complete").
  Verified at this revision.
* **51** `axiom` declarations: `WSC/Honest.lean` (**38**), `WSC/Composition.lean`
  (**10**), `WSC/Props/P1_Transfer.lean` (**2**), `WSC/Model/SeizeModel.lean` (**1**).
  A3 published 50 with `Honest.lean` = 37; the +1 is C3's `LR_REDEEMER_COVERAGE`,
  and it is the only axiom added in stage 9.
* **Zero `axiom` declarations under `WSC/Prep/`, `WSC/Shaped/` or
  `WSC/Props/Shaped/`** — machine-verified at this revision, and this is the shaped
  layer's central claim: it adds no assumption. **It survives C1, C2 and C4
  intact**, including C4's new `RealizableLeaves.lean`, which lives under
  `Props/Shaped/` and declares no axiom.

---

## 3. AXIOM CENSUS

The rebuild log carries **142** `#print axioms` lines (A3: 73); **27** of them
contain `sorryAx`.

Legend: **(i)** Lean-standard `propext`/`Classical.choice`/`Quot.sound`;
**(ii)** `native_decide` = `Lean.ofReduceBool` + `Lean.trustCompiler`;
**(iii)** `sorryAx` = blaster's `admit`; **(iv)** project axioms, counted.

### 3.1 The number a reviewer needs

There are now **two** strongest-available claims and they are not comparable, so
both are quoted:

**(a) `Composition.containment_on_contained_class` — 26 project axioms.** Over the
`ContainedTx` accounting class. Uses **no UPLC result**; its acceptance hypotheses
are provably unused. The set is identical to `top_claim`'s, measured:

```
top_claim  ==  containment_on_contained_class      :  True
top_claim  ==  no_escape_on_contained_class        :  True
top_claim  ==  containment_on_inert_class_of_nopre :  True
```

**(b) `RealizableLeaves.containment_on_realizable_class_of_p2` — 28 project
axioms, plus one open `p2` hypothesis.** Over a shape class that is **not empty**.
Uses the production bytecode for `p1`, and **consumes the acceptance hypothesis**.
The 28 are the same 26 **plus exactly two**:

* `WSC.LR_BUDGET_global` — the ledger↔meter bridge at `K_global = 4400`, whose
  non-vacuity hypothesis is *discharged*, not assumed
  (`NonVacuity.globalNonVacuous_at_4400`, `native_decide` on the real CEK);
* `WSC.TS3` — reached through `Composition.coveringIn_of_coveringRaw`, the
  raw↔ground-truth reconciliation of the directory exemption predicate.

**That two-axiom delta is the price of making the bytecode load-bearing, and it is
the single most informative number in this audit.** Result (a) is cheaper in axioms
and says nothing about the validators. Result (b) costs two more axioms and says
something about the validators, over a class with a machine-checked node-realizable
inhabitant. Neither dominates; quote both or quote (b) with its `p2`.

The 26 shared, by home file:

`WSC/Honest.lean` (16):
```
Deployed  OnChain
LR_CTX  NONNEG  LR_BUDGET_base
LR_MINT_RUNS_POLICY  LR_SPEND_RUNS_VALIDATOR  LR_WDRL_RUNS_VALIDATOR
NodeAcceptsBase  NodeAcceptsGlobal  NodeAcceptsMinting  NodeAcceptsSeize
nodeStepsBase  nodeStepsGlobal  nodeStepsMinting
mlhPolicyId
```

`WSC/Composition.lean` (10):
```
LedgerStep  Genesis
lr_utxo_semantics  lr_inputs_in_ledger  lr_registration_source
LR_BALANCE_SLOT  NONNEG_L  DIRWF_L
ts_genesis  ts_minting_identity_L
```

**Read 26/28 as a floor, not a ceiling.** The library declares 51; the 23 that no
top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_{minting,seize}`, `DIRWF`,
`TS1`–`TS5` (less `TS3`), `TS_MINTING_IDENTITY`, `nodeStepsSeize`,
`LR_REDEEMER_COVERAGE`, and the two `*_faithful` axioms — are what a *fuller*
bytecode discharge of the leaves would add.

### 3.2 Per-theorem table (project-axiom count; flags)

| theorem | (i) | (ii) | (iii) | (iv) |
|---|---|---|---|---|
| **`RealizableLeaves.containment_on_realizable_class_of_p2`** | ✓ | ✓ | ✓ | **28** (§3.1b) + one open `p2` hypothesis |
| **`RealizableLeaves.no_tokens_outside_mini_ledger_on_realizable_class_of_p2`** | ✓ | ✓ | ✓ | **28** (identical set) + `p2` |
| **`RealizableLeaves.realizableLeaves`** (the constructed `LeafSet`) | ✓ | ✓ | ✓ | **12** — `Deployed`, `LR_BUDGET_global`, `LR_CTX`, `NodeAccepts{Global,Minting,Seize}`, `OnChain`, `TS3`, `nodeSteps{Base,Global,Minting}`, `LedgerStep` |
| **`RealizableLeaves.shapedGlobalContainment_T1R`** (the bytecode leaf) | ✓ | ✓ | ✓ | **7** — `LR_BUDGET_global`, `LR_CTX`, `NodeAcceptsGlobal`, `OnChain`, `nodeSteps{Base,Global,Minting}` |
| `RealizableLeaves.p4_on_T1RShape` | ✓ | — | **—** | 6 (all from the field's own signature; **no bytecode**) |
| `RealizableLeaves.nopre_on_T1RShape` | ✓ | — | **—** | 6 (likewise) |
| **`RealizableLeaves.bridge_T1R`** | ✓ | — | ✓ | **0** |
| **`RealizableLeaves.exec_T1R`** | ✓ | — | **—** | **0 — kernel-checked `rfl`** |
| **`RealizableLeaves.realizable_inhabitant`** | ✓ | ✓ | **—** | **0 — the class is non-empty and node-realizable, on no assumption** |
| `Composition.containment_on_contained_class` | ✓ | ✓ | ✓ | **26** (§3.1a) |
| `Composition.no_escape_on_contained_class` | ✓ | ✓ | ✓ | **26** (identical set) |
| `Composition.containment_on_inert_class_of_nopre` | ✓ | ✓ | ✓ | **26** + one open `nopre` hypothesis |
| `Composition.top_claim` / `no_programmable_tokens_outside_mini_ledger` | ✓ | ✓ | ✓ | **26** + a `LeafSet` hypothesis |
| `Composition.containedLeaves` | ✓ | **—** | **—** | **11**. **No `sorryAx`, no `native_decide`, no `blaster` verdict** — which is exactly how you can tell no bytecode result is used |
| `Composition.preservation` | ✓ | ✓ | ✓ | 22 |
| `Composition.leafP1_of_shapedGlobalContainment` | ✓ | — | — | 7 |
| `Composition.p4_disjuncts_of_custody` | ✓ | — | — | 1 — `OnChain` |
| `P1R_T1` / `P1R_T2` / `P1R_T6` / `P1R_T7` (+ controls) | ✓ | — | ✓ | **0** |
| `P5R_shaped_indexed` / `_exists` | ✓ | — | ✓ | **0** |
| `P5R_shaped_groundtruth` | ✓ | — | ✓ | 3 — `Deployed`, `OnChain`, `TS3` |
| `P6R_shaped_member_adds_to_requirement`, `_mint_stays_at_base` | ✓ | — | ✓ | **0** |
| `P6R_shaped_noBaseInputs` | ✓ | — | **—** | **0 — pure Lean** |
| `P4a_R_*`, `P4_burn_only_R(Idx)`, `P4_burnonly_arm_R` | ✓ | — | ✓ | **0** |
| `P4_local_*_R`, `P4_disjunction_at_L1R`, `P4_delegate*_R`, `P4_disjunction_at_{DT1R,DS1R}` | ✓ | — | ✓ | **0** |
| `P2a_R_structure` / `P2b_R_containment` / `P2_R_gates_are_earned` (+ controls) | ✓ | — | ✓ | **0** |
| **`{g1R,g6R,t1R,t2R,t6R,t7R}_class_coverage`**, **`{m1r,m2r,l1r,dt1r,ds1r,s1r}_class_coverage`** | ✓ | — | **—** | **0 — coverage holds at EVERY leaf assignment, in CLAB's own vocabulary** |
| **`{g1R,g6R,t1R,t2R,t6R,t7R}_realizable`**, **`{m1r,m2r,l1r,dt1r,ds1r,s1r}_realizable`** | ✓ | ✓ | **—** | **0** |
| `RealizableShapes.all_recut_witnesses_redeemersExact` | ✓ | ✓ | — | **0** |
| `RealizableShapes.all_old_witnesses_fail_c3_coverage` | ✓ | ✓ | — | **0** |
| `ShapeRealizability.t1_class_is_empty` | ✓ | — | **—** | **5** |
| `ShapeRealizability.{g6,t2,t6,t7}_class_is_empty` | ✓ | — | — | 2–5, incl. `LR_REDEEMER_COVERAGE` for `g6` |
| `ShapeRealizability.{l1,m1,g1,s1}_class_is_empty_under_coverage` | ✓ | — | — | 1 — `OnChain` (+ the `RedeemerCoverage` **hypothesis**, a `def … : Prop`, **not** an axiom) |
| `NonVacuity.{minting@2500, global@1600/3300/4400, seize@3800}` | ✓ | ✓ | **—** | **0** |
| `Composition.baseNonVacuous`, `mintingNonVacuous` | ✓ | ✓ | **—** | **0** |
| all concrete CEK witnesses (`K_T1R_is_2603`, `K_is_784`, `K_is_1681`, `ctxDS_K_is_1466`, …) | ✓ | ✓ | **—** | **0** |

### 3.3 Four properties of the list a reviewer should notice

1. **Every top-level theorem carries `sorryAx`.** All of them reach `p3_lifted`,
   which reaches the blaster-closed run-form P3; the new one additionally reaches
   `P1R_T1` and `bridge_T1R`. The kernel did **not** check them; their status is
   "checked modulo a `✅ Valid` Z3 verdict recorded in the build log". The sentence
   "the top theorem is `sorry`-free" is **false as stated** (§8 F4).
2. **A P1 result now DOES appear in a top-level theorem's dependency graph.** This
   is new and it is the point of stage 9. In `containment_on_contained_class` no
   P1/P2/P4/P5/P6 result appears anywhere; in
   `containment_on_realizable_class_of_p2`, `P1R_T1` and `bridge_T1R` are both
   reached, which is why that theorem carries `sorryAx` **through a shaped leaf** and
   why `NodeAcceptsGlobal` is not merely mentioned in a field type but consumed.
3. **`LR_BUDGET_minting` and `LR_BUDGET_seize` are still applied by nothing.**
   `grep` finds only docstring mentions. `LR_BUDGET_base` is applied at exactly one
   instantiation (`p3_lifted`, `K := 600`), and — new in C4 — `LR_BUDGET_global` at
   exactly one (`shapedGlobalContainment_T1R`, `K := 4400`). Two of A1's seven
   published budgets are now exercised; five are not (§8 F15).
4. **Lean's `unused variable` linter is still the honest instrument it was in A3.**
   Five warnings, all at `Composition.lean:2442-2446` — A2's inline `LeafSet` — and
   **none** in `RealizableLeaves.lean`, because its `p1` field really does use its
   acceptance hypothesis and its `p4`/`nopre` fields bind theirs as `_` deliberately
   (§5.4).

---

## 4. VACUITY RE-VERIFICATION

The highest-risk failure mode in the library, and the reason is on the record: task
V3 stated P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and only the mandatory probe
revealed the class was accept-**UNSAT** — the theorem was empty. Preserved as
`WSC/Shaped/Probe/G6Vacuous2500.lean`.

### 4.1 The pairing census, run mechanically over the whole built set

For every module in the built set, every prep/run term appearing in a theorem's
hypothesis was collected and matched against every term appearing in a
`*vacuity*`/`*vacuous*` stanza. Result: **20 prep/run terms carry accept-hypothesis
theorems, and every one of the 20 has at least one probe at that same term.**

Five terms appear with theorems but no probe; each was inspected and **none is an
accept-hypothesis theorem**:

| term | where it appears | why no probe is needed |
|---|---|---|
| `appliedGlobalShapedIdx1600` | `ShapeBridge.{inputs,exec,bridge}_GIdx`; `Probe/G2Probe` (imported nowhere) | bridges are equalities/iffs, not accept-hypothesis theorems |
| `appliedGlobalShapedNIdx1600` | `ShapeBridge.*_GNIdx`; `Probe/G3Probe` | same |
| `appliedMinting800` | `.exec` acceptance witnesses in `P4_Minting`, `P4Shaped` | a positive witness, not a hypothesis |
| `appliedMinting1300` | `#prep_uplc` declaration + `Imports.lean` prose | never used in a theorem |
| `appliedSeize` | `#prep_uplc` declaration + docstrings | never used in a theorem |

### 4.2 The re-cut groups — task C4's specific mandate

**Every one of the 11 re-cut shapes has a vacuity probe stated at ITS OWN new prep
term AND ITS OWN new shape builder**, verified by extracting the `applied*` and
`*Ctx` identifiers from each theorem and each probe and comparing them mechanically
rather than by reading docstrings:

| shape | prep term | shape builder | probe | result |
|---|---|---|---|---|
| T1R | `appliedGlobalShapedT1R` | `p1RShapedCtx` | `P1R_T1_vacuity_probe` | **Falsified** |
| T2R | `appliedGlobalShapedT2R` | `p1RShapedMintCtx` | `P1R_T2_vacuity_probe` | **Falsified** |
| T6R | `appliedGlobalShapedT6R` | `p1ROutCtx` | `P1R_T6_vacuity_probe` | **Falsified** |
| T7R | `appliedGlobalShapedT7R` | `p1ROutMintCtx` | `P1R_T7_vacuity_probe` | **Falsified** |
| G1R | `appliedGlobalShapedG1R` | `globalRShapedCtx` | `P5R_shaped_vacuity_probe` | **Falsified** |
| G6R | `appliedGlobalMemberShapedG6R` | `memberRShapedCtx` | `P6R_shaped_vacuity_probe` | **Falsified** |
| M1R | `appliedMintRShaped900` | `mintRCtx` | `P4_R_vacuity_probe` | **Falsified** |
| M2R | `appliedMintRShapedIdx900` | `mintRCtxIdx` | `P4_RIdx_vacuity_probe` | **Falsified** |
| L1R | `appliedMintLocalRShaped2500` | `localRCtx` | `P4_local_R_vacuity_probe` | **Falsified** |
| DT1R | `appliedMintDTRShaped2500` | `dtRCtx` | `P4_delegateTransfer_R_vacuity_probe` | **Falsified** |
| DS1R | `appliedMintDSRShaped2500` | `dsRCtx` | `P4_delegateSeize_R_vacuity_probe` | **Falsified** |
| S1R | `appliedSeizeRShaped3800` | `seizeRCtx` | `P2_R_vacuity_probe` | **Falsified** |

**A probe at the OLD term would have certified nothing about the new one.** Each
re-cut module did the right thing; this audit confirms it by identifier comparison,
not by trust. The 14 pre-existing groups' probes (A3 §4.1) all still report
Falsified in this rebuild and are unchanged.

**C4 added no accept-hypothesis theorem over a prep term.** `bridge_T1R` is an
iff between two executions, `exec_T1R` an equality; `shapedGlobalContainment_T1R`
hypothesises `WSC.NodeAcceptsGlobal` — an abstract axiom, not a prep term — and
`P1R_T1`'s own probe is what certifies the class it lands in. The correct vacuity
question for `RealizableLeaves` is *class inhabitation*, and §4c answers it.

### 4b. THE RE-CUT ITSELF, AUDITED — is the coverage claim real, and is it honest?

This is the new section, and it carries the audit's largest verdict change.

**The rule.** Conway UTXOW's `hasExactSetOfRedeemers`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`, cardano-ledger
`cd8b7fab8`) computes `redeemersNeeded` from `scriptsNeeded` filtered to scripts
that are **provided** and **not native**, then requires the redeemer-map key set to
equal it exactly — `MissingRedeemers` in one direction, `ExtraRedeemers` in the
other, both via `extSymmetricDifference`. I read the Haskell at that revision
myself; C3's audit row S quotes it correctly, including the spec comment at `:237`.

**Is C3's CLAB transcription over-strong?** *Yes, in one specific and documented
way, and it does not damage anything.* `Contexts.redeemerCoverage` omits the
`not (isNativeScript script)` filter and the `Map.lookup sh scriptsProvided` filter,
because `TxInfo` records neither a script's language nor the witness set. So it is an
**over-approximation**: it demands a redeemer entry for a script-credential
withdrawal even when that script is a native timelock, for which the ledger requires
none and the `ExtraRedeemers` half forbids one. C3's own section header and the
`redeemerCoverage` docstring state this explicitly ("Exact when no needed script is
native; otherwise strictly stronger than the ledger rule"). Three checks that the
over-approximation is harmless here:

1. **It is not a conjunct of `validScriptContext`.** C3 deliberately kept it out, for
   exactly this reason. So no ledger-validity claim in the library was strengthened.
2. **Where it is used POSITIVELY — the 12 `*_class_coverage` and 12 `*_realizable`
   theorems — proving the stronger predicate is conservative.** Those say the re-cut
   shapes carry the entries; if anything they carry more than the ledger insists on,
   which is the safe direction for a realizability claim.
3. **Where it is used as an ASSUMPTION — `LR_REDEEMER_COVERAGE` and the
   `RedeemerCoverage` hypotheses — it only weakens NEGATIVE results.** It is reached
   by nothing except the emptiness proofs of the RETIRED shapes. So the residual
   caveat is: *"the old shapes are empty" is proved under an all-Plutus reading; an
   old shape could in principle be realizable if one of its script withdrawals were a
   native timelock.* That caveat makes the library's self-criticism weaker, never its
   claims stronger. **Recorded as §8 F18 rather than waved away.**

**Is the rule the real one? Measured, not assumed.** Decoding all 13 goldens'
`ScriptContext`s gives `#redeemers = #script-inputs + #mint-policies +
#script-withdrawals` **exactly, 13/13**, with the purpose multiset matching
(`mint-burnonly` = `[Spending, Minting, Rewarding, Rewarding, Rewarding]`;
`seize-1-input` = `[Spending, Rewarding, Rewarding]`). All 13 satisfy
`redeemerCoverage`; all 9 accepting goldens satisfy the full `redeemersExact`
(`Goldens/Audit.lean`). So the predicate reproduces the real node's output on every
vector this campaign measured — and, in the other direction,
`all_old_witnesses_fail_c3_coverage` proves `redeemerCoverage = false` at all 5
pre-C2 witnesses. **The flip is machine-checked in both directions.** That is the
strongest form this evidence could take short of running a node.

### 4c. IS THE NEW CLASS REALLY NON-EMPTY? — the question that decides C4's worth

A3's §9 warned: *"Do not believe that instantiating the `Shape` parameter with a
shaped context class would fix that. It produces a true theorem about an EMPTY
class."* That warning was correct then and is why this section exists.

* `ShapeRealizability.t1_class_is_empty` proves the PRE-re-cut SHAPE T1 class empty
  **unconditionally**, and `t1_no_honest_step` proves no `Reachable.step` can fire,
  so `t1_top_claim_is_vacuous` is `ts_genesis` with extra syntax. Both retained.
* `RealizableLeaves.realizable_inhabitant` proves, with **0 project axioms and no
  `sorryAx`**, that `P1RShapedWitness.ctxOk` is (i) a member of `T1RShape
  witnessParams`, (ii) `validRewardingContext`, and (iii) `redeemersExact` — both
  halves of the Conway rule. The real compiled bytecode accepts it in 2,603 steps.

**The honest limit, stated precisely.** This does NOT prove that a `Reachable` trace
in the new class can take a step, and it cannot: `HonestTx` also requires
`WSC.OnChain ctx`, and `OnChain` is an opaque axiom, so **no term in this library can
prove any concrete context on-chain**. That is true of every witness in the campaign,
not a defect of C4's. What changed is the *direction of the available proof*: for
SHAPE T1 the emptiness is a **theorem**; for SHAPE T1R there is no emptiness proof
and the one obstruction that made its predecessor empty is machine-checked to be
absent. "Not provably empty, with the known obstruction removed" is weaker than
"provably inhabited on-chain", and this audit will not let the two be confused.

---

## 5. ANTI-TAUTOLOGY SPOT-CHECK

The question in each case: **is the postcondition a fact about the transaction, or is
it "the validator's own accumulator came out true"?** Re-read line by line at this
revision.

### 5.1 P1 containment at the realizable cut — `WSC.P1R_T1`

Postcondition, verbatim from `P1R_T1_stmt`:
`Model.outSum (.ScriptCredential plc) cs tn …txInfoOutputs ≥ Model.inSum … …txInfoInputs + Model.mintSigned cs tn …txInfoMint`
— **identical to `P1_T1`'s**, over the re-cut shape.

* `Model.outSum` / `inSum` (`WSC/Model/Ground.lean:43-56`) are independent structural
  recursions over the context's own output/input lists, guarded by
  `WSC.payCred o == base` and summing CLAB's `valueOf`. **No validator function
  appears in the postcondition** — the validator appears only in the hypothesis.
* `plc` is not a free choice: it is the same variable the shape puts in the
  params-UTxO datum the validator reads.
* The escape route is REAL at the re-cut, and is proved so:
  `P1RShapedWitness.ctxEscape_quantities` gives `outSum = 3 < inSum = 5`, and
  `exec_rejects_escape` shows the real CEK **rejects** that context with 4,400 steps
  available (so it is a genuine rejection, not budget exhaustion).
* The accepting witness is pinned two-sided: `K_T1R_is_2603` proves the machine halts
  at 2,603 and budget-errors at 2,602.
* `mintPos_form_REFUTED` re-refutes ARCHITECTURE §3-P1's unsigned form at the
  realizable cut too.

**Verdict: ground truth. Not true by construction.**

### 5.2 P2b containment — `WSC.P2b_R_containment`

Postcondition is `P2.sumOutAtBase … ≥ P2.sumInAtBase … + WSC.mintOf …`, universally
quantified over `tn`, in independent recursions; nothing from the seize validator's
`valueDelta` / `ptokenPairsContain` machinery appears.

**Doubt, recorded, and it is still the sharpest one in the library:** this conjunct
is FALSE-in-general on the source model — obligation B1 has two machine-checked
counterexamples (`ptokenPairsContain` is unsound with duplicate token names or
unsorted maps) — and it closes here *because* SHAPE S1R gives every value exactly one
policy and one token name. C2's header names the two shape facts it consumes and
records that S1R re-uses S1's value terms **by name**, so the re-cut preserved them
verbatim. **The re-cut removed the realizability defect; it did NOT remove the
shape-dependence.** That is why F2's coverage half is still CRITICAL.

### 5.3 P4-Local no-escape — `WSC.P4_local_noEscape_R`

Postcondition `noEscape (.ScriptCredential plc) ownCS (localRCtx …outputs) = true`,
where `noEscape` is `∀ o. payCred o == progLogicCred || ¬ hasCurrencySymbol cs
o.txOutValue`, scanning the transaction's own output list. Both disjuncts are live
(distinct free variables). `L1RWitness.exec_rejects_escaping_output` is the
excluded-case witness through the real CEK — and, new since A3, **over a
redeemer-covered context**, i.e. a transaction an attacker could really build.

**Verdict: ground truth. Not true by construction.**

### 5.4 The same check applied to the two `LeafSet` terms

| | `Composition.containedLeaves` (A2) | `RealizableLeaves.realizableLeaves` (C4) |
|---|---|---|
| class | `ContainedTx` — "no output carries a non-ada policy off-base, and none is a directory node" | `T1RShape` — "this tx is an instance of the re-cut SHAPE T1R at this deployment's credentials" |
| class provably empty? | no | no — **and it has a certified node-realizable inhabitant** (§4c) |
| `p1` discharged by | `contain_of_inertOffBase` — `LR_BALANCE_SLOT` + `NONNEG` + the class | **`WSC.P1R_T1` — the production bytecode**, via `bridge_T1R` + `LR_BUDGET_global` |
| `p1` uses its acceptance hypothesis? | **NO** — Lean's `unused variable` linter says so, 5 warnings | **YES** — and `#print axioms` shows `NodeAcceptsGlobal` + `sorryAx` reached through the shaped leaf |
| `p4` discharged by | the class | the SHAPE (T1R's mint is `[]`) — **acceptance hypothesis unused, bound as `_` on purpose** |
| `p2` | the class | **NOT discharged — carried as a hypothesis** |
| `nopre` | the class | the SHAPE (T1R's outputs carry `NoOutputDatum`) — no acceptance hypothesis exists in the signature |
| project axioms | 26 at the top | 28 at the top |

So `containment_on_realizable_class_of_p2` is **not** a tautology and, unlike its
predecessor, **is partly a statement about the validators**. But three of its four
leaves are still not: two are discharged by the shape and one is assumed. Quote it as
"one of four leaves is bytecode", never as "the leaves are proved".

### 5.5 What this audit did NOT check

* The `#prep_uplc`-produced `.prop` terms themselves. Every shaped leaf theorem's
  hypothesis is `isSuccessful (appliedXShaped.prop …)`; every witness and every K
  measurement runs `.exec`. `prop = exec` is unproved (§8 F8) and **the re-cut did
  not touch it** — `RealizableLeaves` inherits it through `bridge_T1R`, whose
  right-hand side is `Runs.globalRun` but whose left-hand side is the `.prop` term.
* `Optimize.main`'s faithfulness, for the same reason.
* Whether the goldens' `ScriptContext`s are what a *node* would build. They are
  harness-built and ledger-evaluated (§6.2).
* Whether a node would accept the re-cut shapes' transactions **in full** — fees
  against a real protocol-parameter set, agreement between a withdrawal credential
  and the script actually supplied in the witness set, and the UTxO set the inputs
  are drawn from are all still unmodelled. `Realizability.Realizable`'s docstring
  enumerates exactly this. **Realizability is NECESSARY, not SUFFICIENT.**

---

## 6. PROVENANCE — RE-VERIFIED END TO END

### 6.1 The bytecode is the production artefact at the recorded commit

`WSC/flats/PROVENANCE.md` records extraction from wsc-poc worktree at commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f`, with a sha256 per `.flat`. Both halves
re-derived independently (A3; unchanged at this revision — no `.flat` file was
touched by C1/C2/C3/C4, verified by `sha256sum`):

| flat | sha256 of the file | = PROVENANCE.md table | = `cborHex` at commit `7ae0024b…` |
|---|---|---|---|
| `programmableLogicBase.flat` | `1881821b…25faf3` | ✅ | ✅ |
| `programmableTokenMinting.flat` | `7274240514…feb048` | ✅ | ✅ |
| `programmableSeize.flat` | `289e9e8d…1c41a1` | ✅ | ✅ |
| `programmableLogicGlobal.flat` | `ddd6f7df…b433a2` | ✅ | ✅ |

**All four match on both counts.** "Proved against production bytecode" is
machine-verified, not asserted, and "unapplied" is confirmed — every deployment
parameter is still a lambda and is supplied Lean-side.

### 6.2 Goldens

13 golden vectors, **4 rejecting / 9 accepting**, each verified at extraction by
re-running the compiled script at PV11 through the Haskell ledger evaluator
(`PlutusLedgerApi.V3.evaluateScriptCounting`), requiring `Right budget` for every
accepting vector and `Left CekError` for every rejecting one — the rejecting controls
double as an **arity proof**. All 9 accepting goldens satisfy their matching
`validXContext` **verbatim**, and (C3) all 13 satisfy `redeemerCoverage` while all 9
accepting satisfy `redeemersExact` (§4b).

---

## 7. HONESTY-REGRESSION CHECKS ON THE STAGE-9 WORK

The specific risk: a *re-cut* can silently weaken a theorem, and a *new class* can
silently empty one.

### 7.1 Did the re-cut weaken any headline?

**No, and this was checked statement by statement rather than by reading reports.**
For each of the 11 re-cut shapes the `*_stmt` of the R theorem was diffed against the
pre-re-cut theorem's statement. The postconditions are identical; the hypothesis
`isSuccessful (applied…R.prop …)` names the new prep, and the shape builder named in
`validXContext` and in the ground-truth sums is the new one. Two consequences worth
stating:

* **Same budgets.** T*R at 4400, G1R at 1600, G6R at 3300, M1R/M2R at 900, L1R/DT1R/
  DS1R at 2500, S1R at 3800 — no budget was raised to make a re-cut proof go through.
* **Same witness K, to the step.** 2603 / 3572 / 3150 / 3572 / 1541 / 2837 / 784 /
  1681 / 1257 / 1466 / 3004+3328. That is *evidence about the validators*, not
  bookkeeping: it says the transfer, minting and seize validators never dereference
  `txInfoRedeemers`, so enlarging the map costs zero CEK steps. Only `DelegateSeize`
  walks the map, and DS1R's 1466 was independently re-measured.

### 7.2 Does C4's `LeafSet` overclaim?

Checked against measurements rather than prose:

| claim in `RealizableLeaves`'s header | verified how | verdict |
|---|---|---|
| "`p1` uses the acceptance hypothesis" | `#print axioms shapedGlobalContainment_T1R` lists `NodeAcceptsGlobal`, `LR_BUDGET_global`, `sorryAx`; and **no** `unused variable` warning is emitted for the module | ✅ |
| "`p4`/`nopre` do NOT use it" | both are `sorryAx`-free and `native_decide`-free; their axioms come only from the field signatures | ✅ |
| "N = 1" | `realizableLeaves` takes exactly one hypothesis, whose type is `LeafSet.p2`'s statement verbatim (it type-checks as that field) | ✅ |
| "the class is not empty" | `realizable_inhabitant`, 0 project axioms | ✅ with the §4c caveat about `OnChain` |
| "two extra axioms vs `containedLeaves`" | set difference of the two `#print axioms` outputs = `{LR_BUDGET_global, TS3}` | ✅ |

**One overclaim was found and corrected before commit**, and it is recorded because
the process matters: an earlier draft of the module header said "the top claim is now
proved over a realizable class". It is not — it is proved *assuming `p2`* over a
class that is *not provably empty*. The header now says both.

### 7.3 Is the four-point bar met for every re-proved property?

The bar this audit was asked to apply: (a) the theorem exists and its marker is
`✅ Valid`; (b) it has a vacuity probe at ITS OWN term and shape reporting
`✅ Expected Falsified`; (c) it has a concrete accepting CEK witness; (d) its shape
has a realizability theorem. Measured per group:

| property group | shape | (a) | (b) | (c) | (d) | verdict |
|---|---|---|---|---|---|---|
| P1 base transfer (`P1R_T1`) | T1R | ✅ | ✅ | ✅ K=2603 | ✅ `t1R_realizable` | **4/4** |
| P1 signed mint/burn (`P1R_T2`) | T2R | ✅ | ✅ | ✅ K=3572 | ✅ `t2R_realizable` | **4/4** |
| P1 output aggregation (`P1R_T6`) | T6R | ✅ | ✅ | ✅ K=3150 | ✅ `t6R_realizable` | **4/4** |
| P1 aggregation + mint (`P1R_T7`) | T7R | ✅ | ✅ | ✅ K=3572 | ✅ `t7R_realizable` | **4/4** |
| P5 non-member (`P5R_shaped_indexed`, `_exists`, `_groundtruth`) | G1R | ✅ | ✅ | ✅ K=1541 | ✅ `g1R_realizable` | **4/4** |
| P6 member (`P6R_shaped_member_adds_to_requirement`, `_mint_stays_at_base`) | G6R | ✅ | ✅ | ✅ K=2837 | ✅ `g6R_realizable` | **4/4** |
| P4a + BurnOnly (`P4a_R_*`, `P4_burn_only_R`, `P4_burnonly_arm_R`) | M1R | ✅ | ✅ | ✅ K=784 | ✅ `m1r_realizable` | **4/4** |
| P4a + BurnOnly, free wdrl index (`P4a_RIdx_*`, `P4_burn_only_RIdx`) | M2R | ✅ | ✅ | **✗** | ✅ `m2r_realizable` | **3/4 — see F17** |
| P4 Local (`P4_local_*_R`, `P4_disjunction_at_L1R`) | L1R | ✅ | ✅ | ✅ K=1681 | ✅ `l1r_realizable` | **4/4** |
| P4 DelegateTransfer (`P4_delegateTransfer_*_R`, `P4_disjunction_at_DT1R`) | DT1R | ✅ | ✅ | ✅ K=1257 | ✅ `dt1r_realizable` | **4/4** |
| P4 DelegateSeize (`P4_delegateSeize_arm_R`, `P4_disjunction_at_DS1R`) | DS1R | ✅ | ✅ | ✅ K=1466 | ✅ `ds1r_realizable` | **4/4** |
| P2 both conjuncts (`P2a_R_structure`, `P2b_R_containment`, `P2_R_gates_are_earned`) | S1R | ✅ | ✅ | ✅ K=3004/3328 | ✅ `s1r_realizable` | **4/4** |
| **P4 Local, free registration index (`P4_local_noEscape_shapedIdx`)** | **L2 — NOT re-cut** | ✅ | ✅ (at L2) | ✗ | **✗ — class PROVED EMPTY** | **NOT re-cut (F19)** |

**11 of 12 re-cut shapes meet the bar in full; M2R misses (c); SHAPE L2 was not
re-cut at all and its theorem still holds over an unrealizable class.**

---

## 8. FINDINGS, ranked by severity

### F1 — CRITICAL, NARROWED. The top claim is proved where the code does one quarter of the work.

A3's F1 said the top claim was discharged only where "the class, not the code, does
the work". That is now literally false of one field and still true of three.

`RealizableLeaves.containment_on_realizable_class_of_p2` is the top claim over
`T1RShape` with `p1` closed by `WSC.P1R_T1` — real bytecode, acceptance hypothesis
consumed, `#print axioms` showing it. But: `p4` and `nopre` are discharged **by the
shape** (a pure-transfer transaction mints nothing and registers nothing — true, and
honest, and not about the validators); `p2` is **assumed**; the class is one shape
class; and the whole thing is bounded by a 4,400-step CEK budget and a fixed `Data`
skeleton. For the **general** class the four leaf obligations stand as before:
ingredients proved for two with an unproved residue, `p2` needs an unwritten
"structure preserved ⟹ contained" lemma, `nopre` (`L-mint-needs-reg`) is untouched.
**Nothing in this repository proves the top-level claim for the general class of
transactions that put a programmable token at an off-base output.** Every external
quotation must say so. The correct one-line summary is: *"one of four leaf
obligations is now discharged from the production bytecode, over one non-empty shape
class, assuming a second."*

### F2 — CRITICAL for coverage; **REPAIRED for realizability** (11 of 12 shapes).

Two independent bounds on every bytecode result. **One is now lifted; the other is
not.**

*Realizability — REPAIRED, and machine-checked in both directions.* A3 reported every
shape empty as a class of ledger transactions, because a tractable `#prep_uplc`
forced a **one-entry** redeemer map alongside a **two-entry, both-script** withdrawal
map, and Conway UTXOW requires one entry per script witness. Tasks C1/C2 re-cut 11
shapes to carry exactly the entries the rule demands — several shrinking the
withdrawal map to the one script the validator actually dereferences — and proved,
per shape: class-level coverage in CLAB's own vocabulary at **every** leaf assignment,
and point-level `Realizable`/`RealizableExact` at a concrete witness. `t1_class_is_empty`
and its siblings are retained as the proof that the old classes really were empty.
**Every witness K is unchanged** (§7.1), the six new global preps cost 1.1–1.5 s each,
and the predicted solver wall did not appear. Residue: **SHAPE L2 was not re-cut**
(F19) and **M2R has no CEK witness** (F17).

*Coverage — UNCHANGED, and still the binding constraint.* There is still no argument
that the shapes exhaust the transactions the claim is about. `SHAPE-BRIDGE.md` §10
enumerates three routes and offers none; `ShapeBridge.M1Covers` is recorded **false as
stated**. §5.2 shows this is not pedantry: P2b is provable at SHAPE S1R precisely
because S1R's one-policy / one-token-name values evade the two counterexamples that
defeat the general statement on the source model — and the re-cut preserved those
value terms **by name**, so it did not weaken that dependence at all.

**Honest framing of the shaped layer, revised.** It was: *"exhaustive symbolic
checking of the real compiled code over named bounded families of `Data` skeletons
whose intersection with node-buildable transaction contexts is currently EMPTY."*
It is now: **"exhaustive symbolic checking of the real compiled code over named
bounded families of `Data` skeletons that are node-realizable — each certified by an
inhabitant satisfying CLAB's ledger predicate and both halves of Conway's
redeemer rule — but with no argument that the families cover the transactions the
claim is about."** The first framing said the results constrained the program's
behaviour on *no* realizable transaction. That is no longer true. They now constrain
it on a named, inhabited, node-realizable family — and on nothing outside it.

### F3 — HIGH, PARTLY CLOSED. The shape bridge is proved; one instance is now consumed.

All 25 `ShapeBridge` verdicts re-verified, including the 16 kernel-checked `exec`-level
`rfl` bridges. A3's finding was that **no** `bridge_<S>` was applied to anything,
because no `LeafSet` field was discharged from a shaped theorem. **That is now false
for exactly one shape:** C4's `bridge_T1R` (a new instance of the same pattern, in
`RealizableLeaves.lean` rather than `ShapeBridge.lean`, to avoid re-elaborating a
38 s module) is applied in `shapedGlobalContainment_T1R`. The 16 bridges in
`ShapeBridge.lean` itself are still consumed by nothing, and the 11 other re-cut
shapes have **no** `ShapeBridge` entry at all. Writing them is mechanical
(`exec_<S>R` by `rfl`, `bridge_<S>R` by `blaster`, ~1 s each on the evidence of
`bridge_T1R`); consuming them needs the `p2`/`p4` vocabulary work F1 describes.

### F4 — MEDIUM. "`sorry`-free" is false, including for every top-level theorem.

99 theorem-position results are closed by `blaster`'s `admit`. All top-level theorems
inherit `sorryAx` — the older ones through `p3_lifted` → the blaster-closed run-form
P3, the new one through that **and** through `P1R_T1`/`bridge_T1R`. Nothing about the
mathematics changes — every verdict is ✅ Valid — but a reviewer who greps for
`sorryAx` must not be surprised. Do not use the build log's `sorry` warning count as a
census: 37 modules suppress it.

### F5 — MEDIUM, CLOSED by measurement. `K-MEASUREMENTS.md` §5.1's prep table was ~47× pessimistic.

Re-measured cold and isolated with `lake build`: `WSC.Prep.Base` 1.63 s (published
"≈11 s class"), `WSC.Prep.Minting900` 1.46 s (published 27.6 s),
`WSC.Prep.Global1600` **45.5 s** (published **2,143 s** — 47×). §5.1 is marked
SUPERSEDED with the cause (`lake env lean` without `--load-dynlib`, so Blaster/PCB run
interpreted). **Always time with `lake build`, never `lake env lean`.** Corroborated
again in stage 9: the twelve new shaped preps cost 1.1–1.5 s each.

### F6 — MEDIUM, count UPDATED. `warn.sorry false` makes the build-log census incomplete, in 37 modules.

A3 measured 27; this revision measures **37** (C1/C2/C4 added 10). Any "expected
`sorry` whitelist = N" claim is a count of *unsuppressed* warnings only. The correct
instrument is `#print axioms` → `sorryAx`.

### F7 — CLOSED. Every non-vacuity obligation is discharged.

`WSC/Props/Shaped/NonVacuity.lean` discharges `MintingNonVacuous` at 2500,
`GlobalNonVacuous` at 1600 / 3300 / 4400 and `SeizeNonVacuous` at 3800; with
`Composition`'s base-600 / minting-900 pair the set is complete. All five
`native_decide` on the real CEK: **0 project axioms, no `sorryAx`.** New in C4:
`globalNonVacuous_at_4400` is no longer decorative — it is the hypothesis that makes
`LR_BUDGET_global` usable in `shapedGlobalContainment_T1R`.

### F8 — LOW but structural, UNCHANGED. `prop` vs `exec` (`PropExecFaithful`).

Every *shaped* leaf theorem hypothesises `isSuccessful (appliedXShaped.prop …)`; every
K measurement, every concrete accepting instance and every `native_decide` witness
runs `.exec`. `#prep_uplc` emits the two as separate terms and equality is **not**
definitional (`rfl` fails — `BridgeProbe2FAILS.lean`, kept as evidence). Deliberately
**not** axiomatized. **The re-cut did not narrow this and C4 inherits it**: the 12
re-cut groups are on `.prop`, and `bridge_T1R` — the very lemma that carries `P1R_T1`
into the composition — has `.prop` on its left-hand side. Mitigation in place: every
probe is stated on `.prop`, so the accept classes are certified non-empty on the term
the theorems use. Closing this campaign-wide means restating all 12 groups on
`Runs.XRun K` with 12 fresh, re-measured vacuity probes, and real risk of one coming
back `Valid` (i.e. vacuous), as happened to P6 at 2500.

### F9, F10, F11 — CLOSED (U3/A3). Stale `LeafSet` docstrings; `WSC.ShapeBridge` outside the default target; `P5_Witness1600` citability.

All fixed and re-verified. `WSC.lean` now carries **77** imports, including
`RealizableLeaves`.

### F12 / D5 / D6 — Carried forward, unchanged.

* **Blaster defect D6** — `#prep_uplc` emits kernel-ill-typed `Blaster.dite'` terms
  when a CIP-153 `Value` builtin result stays symbolic. Reproductions
  `WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`, imported nowhere. **Blocks
  SHAPES T3/T4, hence P1's containment dispatch Paths B/C and input-side aggregation
  over ≥ 2 mini-ledger inputs at UPLC.** Needs an upstream fix. Unaffected by the
  re-cut.
* **`WSC.LR5` does not entail `seizeCred ∈ txInfoWdrl`** from `seizeScopedToNodeOf`.
  Isolated as `Composition.SeizeWdrlOfScoped`. **Note the C3 connection:** the same
  missing rule, in the other direction, IS the redeemer-coverage rule — and
  `WSC/Honest.lean`'s LR-CTX table now HAS a row for it (row S,
  `LR_REDEEMER_COVERAGE`). Discharging `SeizeWdrlOfScoped` from row S is now a
  short, well-posed piece of work that did not exist before stage 9.
* **`ValueAlgebra` + `LedgerCanon` uninstantiated**, so `LR_BALANCE_SLOT` is still an
  axiom although `LR_BALANCE_SLOT_of_valueAlgebra` proves its exact statement from
  `LR7` plus those residues. `valueOf` is **not** additive over `merge` without
  canonicity (`merge_not_additive_without_canonicity`, a `native_decide`
  counterexample); budget it as a ~330-line development.
* **D5 — the highest operational risk in the repository.** `lakefile.lean` requires
  PlutusCoreBlaster from the **absolute local path** `/home/gumbo/iohk/PlutusCoreBlaster`
  (branch `cip153-value-builtins`, unpushed), and `lake-manifest.json` records
  `"type": "path"` with **no revision at all**. Without those CIP-153 `Value` builtins
  `programmableLogicGlobal.flat` does not decode, so **every** P1/P5/P6 claim — now
  including the composed C4 result — inherits this. (For contrast, `Blaster` *is*
  pinned: `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`.)

### F13, F14 — CLOSED by C3. Stale seize ExBudget rows; the false PROVENANCE note.

A3 found the golden cost tables stale for the two accepting seize vectors, and
`PROVENANCE.md`'s closing note factually false (it claimed
`programmableLogicGlobal.flat` does not decode and its `#import_uplc` is commented —
U5 had landed and it is live at `Prep/Global.lean:46`). C3 corrected both against
fresh measurements. Re-verified here: the seize rows now carry 60,231,630 / 163,820
and 105,501,594 / 274,735, and `PROVENANCE.md` no longer contains the false note.

### F15 — LOW, PARTLY EXERCISED. A1's `K`-widening.

The four budget bridges assert the ledger↔meter equivalence at seven proved budgets
rather than two. A3 recorded all seven instantiations as unexercised except
`LR_BUDGET_base` at 600. **C4 exercises a second: `LR_BUDGET_global` at 4400.** Five
of seven remain consumed by nothing.

### F16 — INFORMATIONAL, CLOSED in spirit by C4. Inhabitation as implication vs closed `∃`.

A3 noted `containedTx_witness` is an implication over the output list rather than a
closed `∃ ctx, ContainedTx hp ctx`. C4's `t1RShape_witness` **is** a closed statement
about a named concrete `ScriptContext` (`P1RShapedWitness.ctxOk`), so the pattern A3
asked for now exists in the library for the class that matters.

### F17 — MEDIUM, NEW. SHAPE M2R has no CEK acceptance witness.

`appliedMintRShapedIdx900.exec` is executed **nowhere** in the library — verified by
grep. `M2RWitness.ctx` carries `Realizable` (ledger-level, `native_decide`) but there
is no `exec_accepts` and no measured K for the shape. So the M2R group meets three of
the four bars in §7.3: its vacuity probe returns `Falsified`, which does certify the
accept class non-empty **on the `.prop` term**, but there is no solver-free
`native_decide` corroboration on `.exec` as there is for every other re-cut shape.
Carried over rather than introduced — A3's §4.1 recorded the pre-C2 M2 row as "shares
M1's witness", which was already an informal discharge. **Fix is cheap** (one
`native_decide` at the M1R leaves, which `M2RWitness.ctx` already uses) and is the
single cheapest item on the open list.

### F18 — LOW, NEW. C3's coverage predicate is strictly stronger than the ledger rule, and one direction of use inherits that.

`Contexts.redeemerCoverage` omits `hasExactSetOfRedeemers`'s `not (isNativeScript …)`
and `Map.lookup sh scriptsProvided` filters, because `TxInfo` expresses neither.
C3 documents this and deliberately keeps the predicate out of `validScriptContext`.
Consequence, stated so it cannot be forgotten: the **positive** uses (the 12
realizability theorems) are conservative and unaffected, but the **negative** uses —
`LR_REDEEMER_COVERAGE` and the `RedeemerCoverage` hypotheses that prove the RETIRED
shapes empty — assume the all-Plutus reading. A retired shape could in principle be
realizable if one of its script withdrawals were a **native timelock**, which needs no
redeemer entry. This weakens the library's self-criticism, never its claims. No action
required; recorded because "unconditional" appears in several emptiness docstrings and
means "no `RedeemerCoverage` hypothesis", not "no assumption".

### F19 — LOW, NEW. SHAPE L2 was not re-cut and its theorem is still over an empty class.

`P4_local_noEscape_shapedIdx` (the free-registration-index rung of P4-Local) still
ranges over SHAPE L2, whose class is proved empty under `RedeemerCoverage`. C2 marked
it as such in `P4LocalShapedR.lean` and in `RealizableShapes.lean` rather than passing
over it, which is the right disposition. Its value was the index-dependence
measurement, which the withdrawal map does not affect — so the loss is small, but the
library does contain one headline-adjacent theorem over a class known to be empty, and
that must not be quoted.

---

## 9. WHAT A REVIEWER SHOULD NOT BELIEVE

1. **Do not believe "the WSC containment property is proved."** It is (a)
   machine-checked as a *reduction* to four leaf obligations plus 26–28 project
   axioms, (b) discharged outright over one inert accounting class, and (c)
   discharged three-quarters of the way over one **node-realizable shape class**,
   with the fourth quarter assumed. None of the three is the claim.
2. **Do not believe the shapes are still unrealizable — and do not believe they are
   node-buildable either.** A3's blanket "every shape is empty" is **obsolete** for 11
   of 12 shapes. What replaced it is narrower than it sounds: each re-cut shape has a
   concrete inhabitant satisfying CLAB's ledger predicate **and** both halves of the
   Conway redeemer rule, and `OnChain` remains an opaque axiom, so no term in this
   library proves any context is genuinely on-chain. "The one defect audit F2 named is
   gone" is the exact claim. Fees, witness-set agreement and the UTxO set are still
   unmodelled.
3. **Do not believe any UPLC result is universally quantified over transactions.**
   Every one is bounded by a CEK step budget AND by a fixed `Data` skeleton. Quote
   both bounds or quote neither. There is no coverage theorem; §5.2 exhibits a theorem
   that provably does not generalise.
4. **Do not believe "`sorry`-free".** 99 theorem-position results are closed by
   `blaster`'s `admit`; every top-level theorem inherits `sorryAx`. And do not use the
   build log's `sorry` warning count as a census — 37 modules suppress it.
5. **Do not believe the witnesses and the theorems are always about the same term.**
   For the shaped layer — including all 12 re-cut groups — theorems are on `.prop`,
   witnesses and all measured K on `.exec`, equality unproved. **No longer true** for
   the base/keystone path, every `*NonVacuous` obligation and every published K
   constant. Name the layer when quoting this.
6. **Do not believe the source-model and shaped routes are the same strength.** The
   model route quantifies over all contexts and all step counts but trusts a hand
   transcription; the shaped route trusts no transcription but is doubly bounded.
   Neither dominates.
7. **Do not believe the prep-cost figures in `K-MEASUREMENTS.md` §5.1** (F5). Measure
   before concluding anything is unaffordable, and always with `lake build`.
8. **Do not believe this builds anywhere else.** The substrate pin is an absolute
   local path to an unpushed branch, with **no revision recorded in the manifest**
   (D5).
9. **Do not quote SHAPE L2's theorem or SHAPE M2R's as fully controlled** (F19, F17).
10. **Do believe, because it is now machine-verified:** the four `.flat` files are
    byte-identical to the `cborHex` of the named unapplied production scripts at the
    recorded wsc-poc commit (§6.1); the redeemer-coverage rule reproduces the real
    node's output on 13/13 goldens (§4b); and the re-cut cost zero CEK steps (§7.1).

---

## 10. REPRODUCTION

```bash
# 1. clean-room rebuild of everything
#    expect: 429 jobs, 90-105 s, 158 ✅ markers (101 Valid + 57 Expected Falsified),
#            0 errors, 0 ⚠️/❌, 20 expected `sorry` warnings, 90 WSC modules,
#            5 `unused variable` warnings (all Composition.lean:2442-2446)
cp -a <CLAB> <SCRATCH>/clab-audit && cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census from that log
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c   # 101 Valid, 57 Exp. Falsified
grep -cE '⚠️|❌' build.log                            # 0
grep -c 'error:' build.log                            # 0
grep -c "declaration uses 'sorry'" build.log          # 20  (NOT a census — §2)
grep -c 'unused variable' build.log                   # 5   (all in Composition.lean)

# 3. source reconciliation (57 + 2 + 99 = 158) over the BUILT modules only.
#    STRIP BLOCK COMMENTS FIRST, and count `by`-newline-`blaster` as well as
#    one-line `by blaster` — there are 5 of the former (§1.4).

# 4. axiom census
grep -E 'depends on axioms|does not depend' build.log   # 142 lines, 27 with sorryAx
#    the delta that matters:
#      Composition.containment_on_contained_class          -> 26 project axioms
#      RealizableLeaves.containment_on_realizable_class_of_p2 -> 28 (= 26 + LR_BUDGET_global + TS3)
#      RealizableLeaves.realizable_inhabitant              -> 0

# 5. axiom-declaration census
grep -rn '^axiom ' --include='*.lean' WSC/ | wc -l                                  # 51
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0
grep -rl 'set_option warn.sorry false' --include='*.lean' WSC/ | wc -l              # 37

# 6. the re-cut, checked in both directions
#    every re-cut witness is redeemer-exact; every retired witness is not:
#      RealizableShapes.all_recut_witnesses_redeemersExact
#      RealizableShapes.all_old_witnesses_fail_c3_coverage
#    and the rule reproduces the node on all 13 goldens:
#      Goldens.Audit.every_golden_is_redeemer_covered
#      Goldens.Audit.every_accepting_golden_has_exact_redeemers

# 7. PROVENANCE re-verification (§6.1)
sha256sum WSC/flats/*.flat
git -C <wsc-poc worktree> show \
  7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum

# 8. prep-cost re-measurement (the F5 repair) — always `lake build`
for m in Base Minting900 Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.{olean,ilean,trace}
  /usr/bin/time -f "$m %e s" lake build WSC.Prep.$m > /dev/null
done                       # expect ~ 1.6 / 1.5 / 36-46 s
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artefact is the
entire content of F5.
