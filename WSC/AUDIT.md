# WSC containment campaign — FINAL AUDIT (task A3)

**What this file is.** The last technical gate before the campaign is quoted
outside this repository, and the authoritative statement of what is and is not
established. Nothing below is taken on any earlier agent's word — including the two
agents (A1, A2) whose work this audit gates. Every number was re-measured in a
clean-room rebuild on 2026-07-25 at the revision named below; every claim that could
not be reproduced is corrected in place and listed in §8 FINDINGS.

**This revision SUPERSEDES the U3 audit and its Appendices A and B.** The U3 body,
A1's resolution log and A2's resolution log are folded in here, finding by finding;
their originals remain in `git log` (`ba72b1e`, `8c4cdd0`, `b32a8b0`, `80cdac7`).
Where this audit disagrees with any of them the disagreement is stated, not patched
over.

Audited revision: branch `wsc-containment-proofs`, HEAD
`80cdac7b5e7f42dcccfe655c4f2e46236108916c`, tree clean.
Environment: 32-core box, Lean 4.24.0, Z3 4.15.2, `maxHeartbeats 0`,
Blaster git `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`
(branch `beta-lambda-cache-optimization`), PlutusCoreBlaster by **local path**
`/home/gumbo/iohk/PlutusCoreBlaster` (branch `cip153-value-builtins`, **unpushed**;
see §8 F12 — `lake-manifest.json` records **no revision at all** for it).

---

## 0. THE ONE-PARAGRAPH ANSWER

The library is internally consistent and its measurements reproduce: **405 jobs,
98.5 s, 101 solver verdicts all ✅, zero errors, zero unexplained `sorry`s**, and the
leaf theorems say what they claim to say in ground-truth vocabulary. Six safety
properties of the four production validators are genuinely proved against the **real
compiled bytecode** — and the provenance of that bytecode is now verified end to end
(§6, a check the U3 audit declined). But the top-level sentence *"in an honest
deployment, programmable tokens cannot exist outside the mini-ledger"* is **not
proved**, and the two reasons are structural, not clerical:

1. A `LeafSet` term now exists (`Composition.containedLeaves`, task A2) and the top
   claim is instantiated at it — but only over the `ContainedTx` class, whose defining
   property is that nothing leaves the mini-ledger *by construction*. Its four fields
   use **no UPLC result**, their acceptance hypotheses are provably unused, and the
   resulting theorem depends on the **same 26 project axioms and the same `sorryAx`**
   as the un-instantiated `top_claim` (§3.1, measured set-identical). What is closed
   is the ledger-level plumbing, not the bytecode question.
2. Every bytecode result for P1/P2/P4/P4a/P5/P6 is bounded twice — by a CEK step
   budget *and* by a fixed `Data` shape — there is no coverage argument, one shaped
   result provably does not generalise past its shape, and (task A2, corroborated
   here by measurement in §8 F2) **every shape in this library is unrealizable as a
   node-built transaction context.**

The deliverable is therefore: six real, controlled, non-vacuous properties of the
production bytecode over named bounded symbolic families; a machine-checked reduction
of the top claim to four leaf obligations plus 26 axioms; and that reduction
discharged over one accounting class. Not the claim.

---

## 1. CLEAN-ROOM REBUILD

### 1.1 Method

```
cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-A3   # HEAD 80cdac7
cd <SCRATCH>/clab-A3
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
Confirmed by the log: **67 distinct `WSC.*` modules re-elaborated**, including all 9
unshaped/shaped `#prep_uplc` modules, all 4 `#import_uplc` sites, and all 101 solver
invocations.

### 1.2 Result, against the audited baseline

| measurement | U3 baseline (`a8d95a7`) | **A3 (`80cdac7`)** |
|---|---|---|
| exit status | 0 — 401 jobs | **0 — `Build completed successfully (405 jobs)`** |
| wall clock | 1 m 33.66 s | **1 m 38.50 s** |
| user + sys CPU | 251.4 s + 33.4 s (304 %) | **275.9 s + 33.6 s (314 %)** |
| max RSS | 1.61 GB | **1.65 GB** (1,646,380 KB) |
| WSC modules re-elaborated | 63 | **67** |
| `error:` lines | 0 | **0** (hard requirement — met) |
| solver verdicts | 98: 64 `✅ Valid` + 34 `✅ Expected Falsified` | **101: 66 `✅ Valid` + 35 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` markers | 0 | **0** |
| `declaration uses 'sorry'` | 21 | **20** (census §2) |
| other warnings | 64 `simp argument is unused` | **64 `simp argument is unused` + 5 `unused variable`** |

The five `unused variable` warnings are *evidence*, not noise: they sit at
`WSC/Composition.lean:2442-2446`, the inline `LeafSet` inside
`containment_on_inert_class_of_nopre`, and they are Lean's own confirmation that A2's
leaf discharges do not use their acceptance hypotheses (§7.2).

### 1.3 The verdict delta reconciles exactly

`98 → 101` is `+4 −1`, and every marker is accounted for:

* **`+4`** — the new module `WSC/Props/P3_BaseRun.lean` (task A1): 3 × `✅ Valid`
  (`P3_base_requires_global_or_seize_run`, `P3_run_negative_control`,
  `propRun_base_600`) and 1 × `✅ Expected Falsified` (`P3_run_vacuity_probe`, at the
  run term — §4.2).
* **`−1`** — `WSC/Composition.lean` now contributes **zero** verdicts (baseline: 1
  `✅ Valid`): `Composition.mintingNonVacuous` is a term proof instead of
  `by blaster`. That is also why the `sorry` count drops 21 → 20.
* `WSC/Props/Shaped/NonVacuity.lean` (A1) and
  `WSC/Props/Shaped/ShapeRealizability.lean` (A2) contribute **zero** verdicts each —
  everything in them is ordinary Lean plus `native_decide`.

Per-file marker table, complete (full `file:line:col` list in
`<SCRATCH>/A3-markers.txt`, regenerable from the log):

| file | ✅ Valid | ✅ Expected Falsified |
|---|---|---|
| `WSC/ShapeBridge.lean` | 19 | 6 |
| `WSC/Props/Shaped/P4LocalShaped.lean` | 7 | 3 |
| `WSC/Props/Shaped/P4DelegateShaped.lean` | 7 | 4 |
| `WSC/Props/Shaped/P1Shaped.lean` | 5 | 5 |
| `WSC/Props/Shaped/P2Shaped.lean` | 5 | 3 |
| `WSC/Props/Shaped/P4Shaped.lean` | 4 | 2 |
| `WSC/Props/Shaped/P4ShapedIdx.lean` | 3 | 2 |
| `WSC/Props/P3_Base.lean` | 3 | 2 |
| **`WSC/Props/P3_BaseRun.lean`** | **3** | **1** |
| `WSC/Props/Shaped/P5Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Unshaped.lean` | 1 | 1 |
| `WSC/Goldens/Witnesses.lean` | 1 | — |
| `WSC/Prep/Global.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/P4_Minting.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Composition.lean` | — (was 1) | — |
| **total** | **66** | **35** |

### 1.4 Source reconciliation — the check that rules out a skipped stanza

Counted over the 67 built modules, not over the whole tree:

* **35** active (column-0) `#blaster … (solve-result: 1)` stanzas = "expect
  Falsified" → **35 × `✅ Expected Falsified`**.
* **2** active `#blaster … (solve-result: 0)` stanzas = "expect Valid, i.e. expect
  VACUOUS" (`WSC/Prep/Global.lean:83` `global_vacuity_probe_600`;
  `WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous`) → **2 × `✅ Valid`**.
* **64** `blaster` tactic invocations in theorem position → **64 × `✅ Valid`**.
* 35 + 2 + 64 = **101**, and the per-file split matches §1.2's table one-for-one
  (e.g. `ShapeBridge` 19 tactic uses ↔ 19 `✅ Valid`). **No stanza is unaccounted for
  and none is skipped.**

Commented-out `#blaster` lines (8, all in `WSC/Props/P4_Minting.lean`, the
unshaped-minting record) are excluded and produce no marker, as expected.

### 1.5 Slowest cold modules

`WSC.Prep.Global1600` ≈ 42 s in-parallel (**45.5 s isolated**, §8 F5),
`WSC.ShapeBridge` ≈ 38 s, `WSC.Shaped.MintingLocalShapedIdx` ≈ 30 s,
`WSC.Props.Shaped.P2Shaped` ≈ 25 s, `WSC.Composition` 5.4 s,
`WSC.Props.P3_BaseRun` 4.7 s, `WSC.Props.Shaped.ShapeRealizability` 1.3 s,
`WSC.Props.Shaped.NonVacuity` 1.0 s. Everything else ≤ 7 s.

---

## 2. SORRY / ADMIT CENSUS

20 `declaration uses 'sorry'` warnings, classified:

| class | count | detail |
|---|---|---|
| **(a)** blaster `admit` on a declaration that reported ✅ Valid | **19** | `WSC/ShapeBridge.lean:{844,857,873,889,909,930,951,970,992,1015,1037,1060,1088,1111,1134,1157,1360,1370,1446}` — each pairs with the next ✅ Valid marker in the same file (the marker sits on the `by blaster` position, several lines below the `theorem` keyword, because the statements are long) |
| **(b)** PCB pre-existing, not WSC code | **1** | `PlutusCore/UPLC/CekMachine.lean:299:4` — unchanged |
| **(c)** anything else = DEFECT | **0** | — |

**The warning count is NOT a census and must never be quoted as one (§8 F6).**
`grep -rl 'set_option warn.sorry false' WSC/` returns **27 modules**, of which **16
are in the built set** — so the ~45 further `admit`-closed theorems in them emit no
warning at all. **The earlier figure of 15 modules is wrong; the correct figures are
27 total / 16 built.** The authoritative instrument is `#print axioms` → `sorryAx`
(§3), and by that instrument **every one of the 64 `by blaster` theorems in the
library is admit-closed.**

Literal-source grep over `WSC/**/*.lean`:

* **no** literal `sorry`, `admit` or `stop` in tactic position anywhere. Every hit is
  `set_option warn.sorry false` or prose in a docstring. Verified at this revision.
* **50** `axiom` declarations: `WSC/Honest.lean` (**37**), `WSC/Composition.lean`
  (**10**), `WSC/Props/P1_Transfer.lean` (**2**), `WSC/Model/SeizeModel.lean` (**1**).
  **Zero `axiom` declarations under `WSC/Prep/`, `WSC/Shaped/` or
  `WSC/Props/Shaped/`** — machine-verified, and this is the shaped layer's central
  claim: it adds no assumption. It survives A1 and A2 intact.
  (The U3 audit published **47** with `Honest.lean` = 35 and `P1_Transfer.lean` = 1.
  Those totals were 4 low; the per-file attribution and the "no axiom in the shaped
  layer" conclusion both reproduce. A1's deletion of `GlobalPreppedAt` took the total
  51 → 50 and `Honest.lean` 38 → 37.)

---

## 3. AXIOM CENSUS

Reproduce the per-theorem lists with `lake build WSC.Shaped.Probe.U3Census` (2.7 s
warm; `#print axioms` only, adds no trust surface) plus the 8 `#print axioms`
commands at the end of `WSC/Composition.lean` and the 5 in
`WSC/Props/Shaped/NonVacuity.lean`. The rebuild log carries **73** such lines; **8**
of them contain `sorryAx`.

Legend: **(i)** Lean-standard `propext`/`Classical.choice`/`Quot.sound`;
**(ii)** `native_decide` = `Lean.ofReduceBool` + `Lean.trustCompiler`;
**(iii)** `sorryAx` = blaster's `admit`; **(iv)** project axioms, counted.

### 3.1 The number a reviewer needs

**The strongest available claim is
`WSC.Composition.containment_on_contained_class`, and it depends on 26 project
axioms — the SAME 26, as a set, that the un-instantiated `top_claim` depends on —
plus `sorryAx`, plus the two `native_decide` axioms, plus the three Lean-standard
ones.** Measured by set comparison in this rebuild, not asserted:

```
top_claim  ==  containment_on_contained_class      :  True
top_claim  ==  no_escape_on_contained_class        :  True
top_claim  ==  containment_on_inert_class_of_nopre :  True
```

The 26, by home file:

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

**Read 26 as a floor, not a ceiling.** The library declares 50; the 24 that no
top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_{minting,global,seize}`, `DIRWF`,
`TS1`–`TS5`, `TS_MINTING_IDENTITY`, `nodeStepsSeize`, and the two `*_faithful`
axioms — are exactly what any *bytecode-based* discharge of the leaves would add.

### 3.2 Per-theorem table (project-axiom count; flags)

| theorem | (i) | (ii) | (iii) | (iv) |
|---|---|---|---|---|
| **`Composition.containment_on_contained_class`** | ✓ | ✓ | ✓ | **26** (§3.1) |
| **`Composition.no_escape_on_contained_class`** | ✓ | ✓ | ✓ | **26** (identical set) |
| **`Composition.containment_on_inert_class_of_nopre`** | ✓ | ✓ | ✓ | **26** (identical set) + one open `nopre` hypothesis |
| `Composition.top_claim` / `no_programmable_tokens_outside_mini_ledger` | ✓ | ✓ | ✓ | **26** + a `LeafSet` hypothesis |
| **`Composition.containedLeaves`** (the constructed `LeafSet`) | ✓ | **—** | **—** | **11** — `LR_BALANCE_SLOT`, `LedgerStep`, `Deployed`, `NONNEG`, `NodeAccepts{Global,Minting,Seize}`, `OnChain`, `nodeSteps{Base,Global,Minting}`. **No `sorryAx`, no `native_decide`, no `blaster` verdict, no `*_faithful`.** The `NodeAccepts*`/`nodeSteps*` entries are present only because the field TYPES mention them |
| `Composition.preservation` | ✓ | ✓ | ✓ | 22 |
| `Composition.nonEscape_of_registered` | ✓ | ✓ | ✓ | 20 |
| `Composition.p3_lifted` | ✓ | ✓ | ✓ | 9 |
| `Composition.containedTx_witness` (inhabitation) | ✓ | — | — | **0** |
| `Composition.contained_witness_moves_tokens` | ✓ | ✓ | — | **0** |
| `Composition.contain_of_inertOffBase` | ✓ | — | — | 3 |
| `Composition.LR_BALANCE_SLOT_of_valueAlgebra` | ✓ | — | — | 2 — `LR7`, `OnChain` (notably **not** `LR_BALANCE_SLOT`) |
| `Composition.leafP1_of_shapedGlobalContainment` | ✓ | — | — | 7 |
| `Composition.p4_disjuncts_of_custody` | ✓ | — | — | 1 — `OnChain` |
| `covering_node_excludes_registration`, `covering_excludes_registeredIn` | ✓ | — | — | **0 — PROVED** |
| `Composition.contain_iff_modelSums`, `outSum_eq_sumOutsIf`, `noEscape_of_inertOffBase` | ✓ | — | — | 0 |
| `P1_T1` / `P1_T2` / `P1_T6` / `P1_T7` (+ negative control) | ✓ | — | ✓ | **0** |
| `P2a_shaped_structure` / `P2b_shaped_containment` / `P2_shaped` (+ controls) | ✓ | — | ✓ | **0** |
| `P3_base_requires_global_or_seize` / `_negative_control` (prep form) | ✓ | — | ✓ | **0** |
| **`P3_base_requires_global_or_seize_run` / `P3_run_negative_control`** (run form — what `p3_lifted` consumes) | ✓ | — | ✓ | **0** |
| `P4a_shaped_*`, `P4_burn_only_shaped(Idx)`, `P4_burnonly_arm_shaped` | ✓ | — | ✓ | **0** |
| `P4_local_*`, `P4_disjunction_at_L1`, `P4_delegate*`, `P4_disjunction_at_{DT1,DS1}` | ✓ | — | ✓ | **0** |
| `P5_shaped_indexed` / `P5_shaped_exists` | ✓ | — | ✓ | **0** |
| `P5_shaped_groundtruth` | ✓ | — | ✓ | 3 — `Deployed`, `OnChain`, `TS3` |
| `P6_shaped_noBaseInputs` | ✓ | — | **—** | **0 — pure Lean; the only headline the kernel fully checks** |
| `P6_shaped_member_adds_to_requirement`, `P6_shaped_member_mint_stays_at_base` | ✓ | — | ✓ | 0 |
| `Model.P1_bytecode_of_P1_model`, `P6_bytecode_of_P6_model` | ✓ | — | — | 1 — `Model.globalModel_faithful` |
| `P2.P2a_bytecode`, `P2.P2b_model_implies_bytecode` | ✓ | — | — | 1 — `SeizeModel.seizeModel_faithful` |
| `P2.P2a_seizeModel_preserves_structure` | ✓ | — | — | 0 (about the model only) |
| `ShapeBridge.inputs_M1` | — | — | — | **0 — "does not depend on any axioms"** |
| `ShapeBridge.exec_M1` / `exec_T1` | ✓ | — | **—** | **0 — kernel-checked `rfl`** |
| `ShapeBridge.bridge_M1` / `bridge_T1` | ✓ | — | ✓ | 0 |
| **`NonVacuity.{minting@2500, global@1600, global@3300, global@4400, seize@3800}`** | ✓ | ✓ | **—** | **0 — no `sorryAx`, no project axiom** |
| `Composition.baseNonVacuous`, `Composition.mintingNonVacuous` | ✓ | ✓ | **—** | **0** (A1 removed their `sorryAx`) |
| **`ShapeRealizability.t1_class_is_empty`** | ✓ | — | **—** | **5** — `Deployed`, `LR_CTX`, `LR_SPEND_RUNS_VALIDATOR`, `NodeAcceptsBase`, `OnChain`. **No `sorryAx`** |
| `ShapeRealizability.{l1,m1,g1,s1}_class_is_empty_under_coverage` | ✓ | — | — | 1 — `OnChain` (+ the `RedeemerCoverage` **hypothesis**, which is a `def … : Prop`, **not** an axiom) |
| `ShapeRealizability.ds1_uncovered_wdrl_exists` | ✓ | — | — | 0 |
| `ShapeRealizability.clab_validRewardingContext_admits_unrealizable` | ✓ | ✓ | — | 5 |
| all 14 concrete CEK witnesses (`K_T1_is_2603`, `K_is_1681`, `K_is_2837`, `mintPos_form_REFUTED`, `golden_halts_at_1600`, …) | ✓ | ✓ | **—** | **0** |

### 3.3 Three properties of the list a reviewer should notice

1. **Every top-level theorem carries `sorryAx`.** All four reach `p3_lifted`, which
   reaches the blaster-closed run-form P3. The kernel did **not** check them; their
   status is "checked modulo a `✅ Valid` Z3 verdict recorded in the build log". The
   sentence "the top theorem is `sorry`-free" is **false as stated** (§8 F4).
2. **No P1/P2/P4/P4a/P5/P6 result appears in any top-level theorem's dependency
   graph.** Not one. In `top_claim` they enter as the `LeafSet` *hypothesis*; in
   `containment_on_contained_class` that hypothesis is discharged from ledger
   accounting instead (§7.2). `#print axioms containedLeaves` shows no `sorryAx` and
   no `*_faithful` — which is exactly how you can tell no bytecode result is used.
3. **`LR_BUDGET_minting`, `LR_BUDGET_global` and `LR_BUDGET_seize` are applied by
   nothing in the library.** `grep` over `WSC/**/*.lean` finds only docstring
   mentions. Only `LR_BUDGET_base` is applied, at exactly one instantiation
   (`Composition.p3_lifted`, `K := K_base = 600`). A1 made all four `K`-parametric and
   published seven budgets; six of the seven are unexercised (§8 F15).

---

## 4. VACUITY RE-VERIFICATION

The highest-risk failure mode in the library, and the reason is on the record: task
V3 stated P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and only the mandatory probe
revealed the class was accept-**UNSAT** — the theorem was empty. Preserved as
`WSC/Shaped/Probe/G6Vacuous2500.lean` (a stanza that *expects* `Valid`). P6 was
restated at 3300 (witness K = 2837).

### 4.1 The 14 pre-existing accept-hypothesis theorem groups

Every group, its prep term, and its probe **at that same prep term** — re-verified by
reading the `applied*.prop` identifier on both sides, not by trusting docstrings:

| theorem(s) | prep term (budget) | probe | result | solver-free witness |
|---|---|---|---|---|
| `P3_base_requires_global_or_seize` | `appliedBase.prop` (600) | `:112` | **Falsified** | `P3Witness`, golden K = 208 |
| `P1_T1` | `appliedGlobalShapedT1.prop` (4400) | `:380` | **Falsified** | `K_T1_is_2603` |
| `P1_T2` | `appliedGlobalShapedT2.prop` (4400) | `:403` | **Falsified** | `K_T2_is_3572` |
| `P1_T6` | `appliedGlobalShapedT6.prop` (4400) | `:861` | **Falsified** | `K_T6_is_3150` |
| `P1_T7` | `appliedGlobalShapedT7.prop` (4400) | `:884` | **Falsified** | `K_T7_is_3572` |
| `P2a_shaped_structure`, `P2b_shaped_containment`, `P2_shaped` | `appliedSeizeShaped3800.prop` (3800) | `:630` | **Falsified** | `K_is_3004_and_3328` |
| `P4a_shaped_*`, `P4_burn_only_shaped`, `P4_burnonly_arm_shaped` | `appliedMintShaped900.prop` (900) | `:247` | **Falsified** | `exec_accepts_at_900`, K = 784 |
| `P4a_shapedIdx_*`, `P4_burn_only_shapedIdx` | `appliedMintShapedIdx900.prop` (900) | `:103` | **Falsified** | shares M1's witness |
| `P4_local_*`, `P4_disjunction_at_L1` | `appliedMintLocalShaped2500.prop` (2500) | `:545` | **Falsified** | `K_is_1681` |
| `P4_local_noEscape_shapedIdx` | `appliedMintLocalIdxShaped2500.prop` (2500) | `:455` | **Falsified** (300 s Z3 cap) | — |
| `P4_delegateTransfer_*`, `P4_disjunction_at_DT1` | `appliedMintDTShaped2500.prop` (2500) | `:360` | **Falsified** | `ctxDT_K_is_1257` |
| `P4_delegateSeize_*`, `P4_disjunction_at_DS1` | `appliedMintDSShaped2500.prop` (2500) | `:530` | **Falsified** | `ctxDS_K_is_1466` |
| `P5_shaped_indexed/_exists/_groundtruth` | `appliedGlobalShaped1600.prop` (1600) | `:398` | **Falsified** | `K_is_1541` |
| `P6_shaped_member_*` | `appliedGlobalMemberShaped3300.prop` (3300) | `:363` | **Falsified** | `K_is_2837` |
| P3 calibration pair | `appliedBaseShaped.prop` / `appliedBase.prop` | `Calib/P3Shaped:81`, `Calib/P3Unshaped:38` | **Falsified** ×2 | — |

### 4.2 The theorems A1 and A2 added — task A3's specific mandate

* **A1's one new accept-hypothesis theorem is covered, at its own term.**
  `P3_base_requires_global_or_seize_run` hypothesises
  `isSuccessful (Runs.baseRun K_base …)`, and its probe (`P3_run_vacuity_probe`,
  `WSC/Props/P3_BaseRun.lean:123`) is stated over **`Runs.baseRun K_base`** — the same
  term — and reports `✅ Expected Falsified` in this rebuild. A probe at the old prep
  term would have certified nothing about the new one; the module says so and did the
  right thing. `P3_run_negative_control` is additionally present, with the standing E9
  caveat that a negative control is satisfied by budget-`Error` too and therefore
  cannot detect the bound.
* **A1's five `NonVacuity` theorems are not accept-hypothesis theorems** — they are
  existential *witnesses* (`∃ params ctx, valid… ∧ isSuccessful (Runs.XRun K …)`), so
  no probe is applicable; the relevant check is that the term in the ∃ is the term the
  gated axiom names, and it is (`Runs.mintingRun 2500`,
  `Runs.globalRun 1600/3300/4400`, `Runs.seizeRun 3800`). All five are `native_decide`
  on the real CEK with **0 project axioms and no `sorryAx`**.
* **A2 added no accept-hypothesis theorem over any prep term.**
  `ShapeRealizability`'s results are emptiness statements (their content is a
  negation, so vacuity is not the failure mode); `Composition` §11's four fields do
  carry `NodeAcceptsX` hypotheses, but those are abstract axioms, not prep terms — and
  they are **provably unused** (§5.4, §7.2). The correct vacuity question for §11 is
  therefore *class inhabitation*, and A2 answered it (§7.3).

**Verdict: 15 of 15 accept-hypothesis theorem groups have a vacuity probe at their
own prep term and their own shape; all 15 report Falsified. No theorem is without a
probe. No probe returned `Valid` where `Valid` would mean vacuous.** 14 of 15 also
carry a solver-free `native_decide` CEK witness with a measured K.

### 4.3 Deliberate vacuity results, and open vacuity items

Two `✅ Valid` markers in §1.2 **are** vacuity results, by design, and no theorem is
stated at either term — checked by grep, not assumed. `appliedGlobal.prop` (600) and
`appliedMinting.prop` (600) each appear in exactly one `Prop`, their own vacuity
stanza (`WSC/Prep/Global.lean:81`, `WSC/Props/P4_Minting.lean:384`).

**No `*NonVacuous` obligation in the library is open.** `BaseNonVacuous 600` and
`MintingNonVacuous 900` are `Composition.baseNonVacuous` / `mintingNonVacuous`;
`MintingNonVacuous 2500`, `GlobalNonVacuous 1600/3300/4400` and `SeizeNonVacuous 3800`
are the five theorems in `WSC/Props/Shaped/NonVacuity.lean`. This closes the U3
audit's F7 and reverses its "`SeizeNonVacuous` is unreachable at any affordable
budget" entry — correctly, because that reasoning was about `#prep_uplc` cost and does
not apply to a run term.

---

## 5. ANTI-TAUTOLOGY SPOT-CHECK

The question in each case: **is the postcondition a fact about the transaction, or is
it "the validator's own accumulator came out true"?** Re-read line by line at this
revision.

### 5.1 P1 containment — `WSC.P1_T1` (`P1Shaped.lean:179-223`)

Postcondition:
`Model.outSum (.ScriptCredential plc) cs tn …txInfoOutputs ≥ Model.inSum … …txInfoInputs + Model.mintSigned cs tn …txInfoMint`.

* `Model.outSum` / `inSum` (`WSC/Model/Ground.lean:43-56`) are independent structural
  recursions over the context's own output/input lists, guarded by
  `WSC.payCred o == base` and summing CLAB's `valueOf`; `Model.mintSigned`
  (`P1_Transfer.lean:192`) is `valueOf cs tn mint`, definitionally `WSC.mintOf`. **No
  validator function appears in the postcondition** — the validator appears only in the
  hypothesis `isSuccessful (appliedGlobalShapedT1.prop …)`. Re-verified by reading both
  definitions.
* `plc` is not a free choice: it is the same variable the shape puts in the params-UTxO
  datum the validator reads, so the theorem is about the deployment's own mini-ledger
  credential.
* The escape route is REAL — SHAPE T1 carries a second input and a second output at
  non-base addresses, so ledger balance alone gives only
  `qIn + qIn2 + mint = qOut + qEsc` and does not imply the conclusion.
  `P1ShapedWitness.ctxOk_*` is an ACCEPTED instance with `qEsc = 4 > 0`;
  `exec_rejects_escape` is a `validRewardingContext`-clean instance that violates the
  conclusion and is REJECTED by the real CEK.
* **Doubt, recorded:** the *hypothesis* `Model.coveringNodeExists … = false` is in
  raw-decode vocabulary. It is a hypothesis, so it only weakens the theorem;
  `Composition.lean` §7.1 bridges it at a cost of `TS3`.

**Verdict: ground truth. Not true by construction.**

### 5.2 P2b containment — `WSC.P2b_shaped_containment` (`P2Shaped.lean:288`)

Postcondition: `P2.sumOutAtBase base key tn …txInfoOutputs ≥ P2.sumInAtBase base key tn …txInfoInputs + WSC.mintOf key tn …txInfoMint`, universally quantified over `tn`.

* `sumOutAtBase`/`sumInAtBase` (`P2_Seize.lean:258-272`) are again independent
  recursions using `WSC.outAtBase`/`inAtBase` (pure `payCred == base`) and `valueOf`.
  Nothing from the seize validator's `valueDelta` / `remainingProgCSDelta` /
  `ptokenPairsContain` machinery appears.
* `key` is the directory node datum's key field — the object the validator itself
  authenticated, not a free choice.
* `P2_shaped_gates_are_earned` (`:342`, ✅ Valid) shows the three authentication gates
  are each a pair of DISTINCT free variables, so the bytecode earns them.
* **Doubt, recorded, and it is the sharpest one in the library:** this conjunct is
  FALSE-in-general on the source model — obligation B1 has two machine-checked
  counterexamples, `ptokenPairsContain` being unsound with duplicate token names or
  unsorted maps — and it closes here *because* SHAPE S1 gives every value exactly one
  policy and one token name, so the counterexamples cannot be instantiated.

**Verdict: ground truth. Not true by construction. Shape-bound in an essential, not
incidental, way — this is the concrete reason §8 F2 is CRITICAL.**

### 5.3 P4-Local no-escape — `WSC.P4_local_noEscape_shaped` (`P4LocalShaped.lean:203`)

Postcondition `noEscape (.ScriptCredential plc) ownCS (localShapedOutputs …) = true`,
where `noEscape` (`Spec.lean:187-191`) is
`∀ o. payCred o == progLogicCred || ¬ hasCurrencySymbol cs o.txOutValue`.

* The list in the conclusion IS the transaction's output list: `localShapedCtx` sets
  `txInfoOutputs := localShapedOutputs …` (`MintingLocalShaped.lean:223`) — same
  application, same argument order. So the scan is over every output, not a sub-list.
* Both disjuncts are live: `o0h` vs `plc` and `c0` vs `ownCS` are distinct free
  variables. Output 1 clears via the value disjunct; output 0 must clear via the
  credential disjunct, which the bytecode has to earn.
* `exec_rejects_escaping_output` is the excluded-case witness through the real CEK.
* The two delegating arms (DT1/DS1) prove strictly less — only that a sibling
  validator RUNS (`credentialInWithdrawals`) — and their docstrings say so.

**Verdict: ground truth. Not true by construction.**

### 5.4 NEW — the same check applied to A2's `containedLeaves`

This is the result the previous audits could not check, and it does not pass in the
same sense the three above do — which is what A2's own documentation says, and what
this audit confirms independently:

* `p4_on_containedTx`'s proof is
  `intro …; exact Or.inl (noEscape_of_inertOffBase hp.progLogicCred cs hcs _ hsh.1)`
  — it uses the CLASS hypothesis and nothing else.
* `p1_on_containedTx` / `p2_on_containedTx` reduce to `contain_of_inertOffBase`, whose
  ingredients are `LR_BALANCE_SLOT`, `WSC.NONNEG`, `noEscape_of_inertOffBase` and
  `int_contain_of_escape_zero` (an `omega` on `Int`).
* **The acceptance hypotheses and P1's `¬ coveringIn` premise are unused**, and the
  Lean compiler says so itself in §11.6's inline copy (five `unused variable` warnings
  at `Composition.lean:2442-2446`).

So `containment_on_contained_class` is **not** a tautology — `LR_BALANCE_SLOT`,
`NONNEG` and the trace induction are real content — but it is **not a statement about
the validators**. On the `ContainedTx` class the class hypothesis is what closes the
escape.

### 5.5 What this audit did NOT check

* The `#prep_uplc`-produced `.prop` terms themselves. Every shaped leaf theorem's
  hypothesis is `isSuccessful (appliedXShaped.prop …)`; every witness and every K
  measurement runs `.exec`. `prop = exec` is unproved (§8 F8). A1 removed this from
  the base/keystone path only.
* `Optimize.main`'s faithfulness, for the same reason.
* Whether the goldens' `ScriptContext`s are what a *node* would build. They are
  harness-built and ledger-evaluated (§6.2), which corroborates shape and cost, not
  the `OnChain`/`LR_CTX` axioms.

---

## 6. PROVENANCE — RE-VERIFIED END TO END (new in A3)

The U3 audit listed the `.flat` provenance chain under "what I did NOT check". It is
checked now, and it passes.

### 6.1 The bytecode is the production artefact at the recorded commit

`WSC/flats/PROVENANCE.md` records extraction from wsc-poc worktree
`/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d` at commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f`, with a sha256 per `.flat`. Both halves
re-derived independently:

```
sha256sum WSC/flats/*.flat
git -C <worktree> show 7ae0024b…:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum
```

| flat | sha256 of the file | = PROVENANCE.md table | = `cborHex` at commit `7ae0024b…` |
|---|---|---|---|
| `programmableLogicBase.flat` | `1881821b…25faf3` | ✅ | ✅ |
| `programmableTokenMinting.flat` | `7274240514…feb048` | ✅ | ✅ |
| `programmableSeize.flat` | `289e9e8d…1c41a1` | ✅ | ✅ |
| `programmableLogicGlobal.flat` | `ddd6f7df…b433a2` | ✅ | ✅ |

**All four match on both counts.** The `.flat` files are byte-identical to the
`cborHex` strings of the named **unapplied** production TextEnvelope JSONs at the
recorded commit — so "proved against production bytecode" is machine-verified, not
asserted, and "unapplied" is confirmed (every deployment parameter is still a lambda
and is supplied Lean-side, so no theorem can quietly be about a partially applied
term).

**But `PROVENANCE.md`'s closing note is factually FALSE at this revision** (§8 F14):
it says `programmableLogicGlobal.flat` "does not decode with the current
PlutusCoreBlaster flat decoder … its `#import_uplc` line is kept commented … until
task U5 lands those builtins". U5 landed: it is imported and decoded at
`WSC/Prep/Global.lean:46` and `WSC/Prep/Global1600.lean:66`, and P1/P5/P6 all run on
it. Not this audit's file to edit; recorded as a finding.

### 6.2 Goldens

13 golden vectors (`WSC/goldens/*.json`), **4 rejecting / 9 accepting**, and 13
applied flats under `WSC/goldens/applied/`. Each was verified at extraction by
re-running the actual compiled script at PV11 through the Haskell ledger evaluator
(`PlutusLedgerApi.V3.evaluateScriptCounting`), requiring `Right budget` for every
accepting vector and `Left CekError` for every rejecting one — and the rejecting
controls double as an **arity proof**, since an under-applied Plutus script evaluates
to a lambda and can never produce `Left`. All 9 accepting goldens satisfy their
matching `validXContext` **verbatim** (`WSC/Goldens/Audit.lean`).

---

## 7. HONESTY-REGRESSION CHECKS ON A1 AND A2 (new in A3)

The specific risk this audit was asked to test: an axiom *restatement* can silently
strengthen an assumption, and a *class restriction* can silently empty a theorem.

### 7.1 Did A1's restated `LR_BUDGET_*` assert more than before?

Old and new statements compared semantically, term by term (old text from
`git show 54a6545:WSC/Honest.lean`). Three distinct effects, and they do not all
point the same way:

**(a) The right-hand side changed TERM. This is not a weakening — it is a
substitution of one unproved assumption for another.** Old RHS:
`isSuccessful (appliedX.prop …)`, an `Optimize.main` output. New RHS:
`isSuccessful (Runs.XRun K …)`. `appliedX.prop = Runs.XRun K` is **not proved in
either direction** (`PropExecFaithful`, §8 F8; `rfl` fails —
`Shaped/Probe/BridgeProbe2FAILS.lean`), so neither axiom implies the other. What
genuinely improves is **auditability**: `Runs.XRun K` is a two-line definition naming
the imported flat, the audited inputs function and the budget
(`WSC/Runs.lean:86-121`), so a reviewer can read what is being assumed; the old RHS
was opaque. A1's docstrings claim exactly this and no more. **No regression.**

**(b) The `K`-widening DOES assert strictly more instances, and it is currently
unexercised.** `LR_BUDGET_base` went from a fixed `K_base` to
`∀ K, BaseNonVacuous K → …`; `LR_BUDGET_minting` likewise from `K_mint`. The guard is
real (it is per-context: `nodeStepsX ctx ≤ K`), and seven budgets now have proved
non-vacuity (600/900/1600/2500/3300/3800/4400), so the axioms assert the equivalence
at seven budgets where they previously asserted it at two. That is a widening and
should be quoted as one. Mitigating measurement: **six of the seven instantiations are
used by nothing** — only `LR_BUDGET_base` at `K_base = 600` is ever applied (§3.3 item
3). **Reported, not a defect; the widened surface is inert today and will matter the
moment a shaped leaf is wired in.**

**(c) One "restatement" was in fact a REPAIR, and A1 undersold it.** The old
`LR_BUDGET_seize` read

```lean
axiom LR_BUDGET_seize :
  SeizeNonVacuous →
  ∀ (K : Nat) (pcs : CurrencySymbol) (ctx : ScriptContext),
    OnChain ctx → nodeStepsSeize pcs ctx ≤ K →
    (NodeAcceptsSeize pcs ctx ↔ isSuccessful (appliedSeize.prop pcs ctx))
```

`K` is quantified *inside* and occurs **only in the guard**. Instantiating
`K := nodeStepsSeize pcs ctx` makes the guard reflexively true, so the axiom collapsed
to an **unbounded** equivalence between node acceptance and the budget-**600** prep,
for every on-chain context. The new form indexes both sides by `K` and cannot be
collapsed that way, so it is **strictly weaker**. Nothing consumed the old one (it was
gated on a then-unprovable hypothesis), so no result changes — but the old statement
was defective and the new one is not.

**(d) `GlobalPreppedAt` deletion is a strict reduction of the axiom base.** It was the
unprovable side condition "the term you handed me really is the prep of that flat at
that budget"; `Runs.globalRun K` exhibits flat, inputs function and budget in its own
definition, so the condition is discharged by reading it. Measured:
`WSC/Honest.lean` 38 → 37 `axiom` declarations, library 51 → 50.

### 7.2 Does A2's scope docstring match what was proved?

`Composition.lean` §11.4's four numbered scope items, each checked against a
measurement rather than against the prose:

| §11.4 claim | verified how | verdict |
|---|---|---|
| 1. the class excludes exactly the transactions for which containment is a property of the bytecode | read `InertOffBase` (`:2142`): every output is either at `progLogicCred` or carries no non-ada policy | ✅ and the docstring states it as bluntly as this audit would |
| 1′. "this theorem is NOT evidence that the validators enforce containment" | `#print axioms containedLeaves` has no `sorryAx`, no `*_faithful`, no `native_decide`; the acceptance hypotheses are unused (Lean's own `unused variable` warnings, §1.2) | ✅ |
| 2. no shape-coverage argument exists and this does not create one | grep: no coverage theorem anywhere in `WSC/` | ✅ |
| 3. "the axioms are unchanged from `top_claim`'s … `sorryAx` still present" | set comparison of the two `#print axioms` outputs: **identical** (§3.1) | ✅ |
| 4. `Genesis` still assumed | `ts_genesis` and `Genesis` both in the 26 | ✅ |

**No overclaim found.** The one thing a reader must not do is invert the emphasis: "a
`LeafSet` now exists and the top claim is instantiated" is true, and it is progress on
the *plumbing*, not on the *bytecode* question. Every reviewer-facing document in this
repository now leads with that.

### 7.3 Is A2's class INHABITED?

**Yes, and non-degenerately.** `containedTx_witness` (`:2398`) proves
`ContainedTx hp ctx` for **every** deployment `hp` and every `ctx` whose
`txInfoOutputs` are `containedWitnessOuts hp.progLogicCred` — a concrete two-output
body: output 0 at the base credential holding 2 ada **+ 5 `MMM.TOK`**, output 1 at a
pubkey wallet holding 1 ada only. `containedWitnessBaseValue` is canonical (ada first,
policies ascending), i.e. a value a real `TxOut` can carry.
`contained_witness_moves_tokens` (`:2408`) proves that output is at base **and** really
holds 5 of `MMM.TOK` — `native_decide` on CLAB's own `valueOf` — so the invariant the
class member satisfies is not satisfied by emptiness. Both have **0 project axioms**.

Two precisions this audit adds:

* The inhabitation is stated as an **implication over the output list**, not as a
  closed `∃ ctx, ContainedTx hp ctx`. Since `ContainedTx` constrains only
  `txInfoOutputs`, and `ScriptContext` is inhabited (13 decoded goldens exhibit terms),
  the class is non-empty as a set of `ScriptContext`s — but no full `ScriptContext`
  term is exhibited in §11. A one-line gap (§8 F16).
* `WSC.OnChain` is an opaque axiom, so **no** term in this library can prove any
  witness on-chain. §11.5's docstring says this. It is true of every witness in the
  campaign, not a defect of A2's.

### 7.4 Is A2's emptiness finding about the *real* shapes?

Checked, because a straw-man shape would make the finding meaningless.
`ShapeRealizability`'s hypotheses are
`ctx.scriptContextTxInfo = (p1ShapedCtx … ).scriptContextTxInfo` (and `localShapedCtx`,
`mintShapedCtx`, `globalShapedCtx`, `seizeShapedCtx`) with the scalars universally
quantified **exactly as in the corresponding P-theorem** — same builders, same argument
lists. So the emptiness is about the same classes P1/P2/P4/P5 quantify over. ✅

`t1_class_is_empty` additionally requires
`hp.progLogicCred = .ScriptCredential plc` — the identification without which the
shaped conclusion's `Model.outSum (.ScriptCredential plc)` is not the composition's
`outAtB hp.progLogicCred`. That hypothesis is necessary and the docstring justifies it.
`RedeemerCoverage` is a `def … : Prop`, **not** an axiom — verified by the axiom census
(§2), so no library result became stronger because of a negative finding.

---

## 8. FINDINGS, ranked by severity

### F1 — CRITICAL. The top claim is proved only where the class, not the code, does the work.

`Composition.containedLeaves` closes the U3 audit's "no `LeafSet` term exists"
literally, and `containment_on_contained_class` / `no_escape_on_contained_class` are
the top claim with **no `LeafSet` hypothesis**. Both are real theorems and green in
this rebuild. But: the class `ContainedTx` says *no output carries a non-ada policy
off-base and no output is a directory node*; the four fields are discharged from
`LR_BALANCE_SLOT` + `WSC.NONNEG` + that class; **no UPLC result is used**, the
acceptance hypotheses are provably unused (§5.4, §7.2), and the axiom list is
set-identical to `top_claim`'s 26 plus `sorryAx` (§3.1). For the **general** class the
four leaf obligations stand as before: ingredients proved for two
(`leafP1_of_shapedGlobalContainment`, `p4_disjuncts_of_custody`) each with an unproved
residue; `p2` needs an unwritten "structure preserved ⟹ contained" lemma; `nopre`
(`L-mint-needs-reg`) is untouched — `containment_on_inert_class_of_nopre` is the
honest variant that carries it as the single remaining hypothesis.
**Nothing in this repository proves the top-level claim for transactions that put a
programmable token at an off-base output — i.e. for the transactions the claim is
about.** Every external quotation must say so.

### F2 — CRITICAL. No shape-coverage argument exists; and every shape is unrealizable.

Two independent bounds on every bytecode result for P1/P2/P4/P4a/P5/P6, and neither is
discharged.

*Coverage.* `SHAPE-BRIDGE.md` §10 enumerates three routes and offers none;
`ShapeBridge.M1Covers` is recorded **false as stated**. §5.2 shows this is not
pedantry: P2b is provable at SHAPE S1 precisely because S1's one-policy /
one-token-name values evade the two counterexamples that defeat the general statement
on the source model.

*Realizability — sharper than "narrow".* Task A2 proved every shaped class **empty as
a class of ledger transactions**: a tractable `#prep_uplc` needs the redeemer map
inside the frozen `Data` skeleton, so every shape bakes a **one-entry** redeemer map
(two for DS1) while baking a **two-entry withdrawal map whose entries are both SCRIPT
credentials**, and Conway UTXOW (`MissingRedeemers`) requires one redeemer entry per
script witness. `t1_class_is_empty` is **unconditional** on the axioms this library
already has; the rest are conditional on `RedeemerCoverage`.

**This audit corroborates the diagnosis by measurement, which no earlier document
did.** Decoding all 13 goldens' `ScriptContext`s (CBOR → `Data`) and counting the
`TxInfo` fields:

| golden | inputs | withdrawals | **redeemers** |
|---|---|---|---|
| `programmableLogicBase.base-spend-transfer-tx` | 1 | 2 | **3** |
| `programmableLogicGlobal.transfer-member-single-policy` | 1 | 2 | **3** |
| `programmableLogicGlobal.transfer-mixed-many-policies` | 1 | 2 | **3** |
| `programmableLogicGlobal.transfer-nonmember-covering-node` | 1 | 1 | **2** |
| `programmableSeize.seize-1-input` | 2 | 2 | **3** |
| `programmableSeize.seize-2-inputs-partial-with-noise` | 3 | 2 | **4** |
| `programmableTokenMinting.mint-burnonly` | 1 | 3 | **5** |
| `programmableTokenMinting.mint-delegate-transfer-topup` | 1 | 3 | **5** |
| `programmableTokenMinting.mint-local-registered-by-ref` | 1 | 1 | **2** |
| *every shape in this library* | 1–2 | **2 (both script)** | **1** (2 for DS1) |

Every accepting golden carries **strictly more** redeemer entries than withdrawals —
consistent with one per script witness plus a `Spending` entry — while every shape
carries one. So the unrealizability is a **`#prep_uplc` tractability truncation, not a
harness defect and not a defect of the system**: the real vectors the campaign
measured are redeemer-covered. It also **sizes the fix**, which no earlier document
did: the cheapest realizable re-cut is modelled by `transfer-nonmember-covering-node` —
**one** script withdrawal and a **two**-entry redeemer map — i.e. shrink each shape's
withdrawal map to the one script credential the validator actually needs, add its
matching `Rewarding` entry, and add a `Spending` entry wherever the shape spends a
script input.

**Honest framing of the whole shaped layer, and it is weaker than "bounded model
checking of real transactions": exhaustive symbolic checking of the real compiled code
over named bounded families of `Data` skeletons whose intersection with node-buildable
transaction contexts is currently EMPTY.** The results are real statements about the
program; they do not yet constrain its behaviour on any single realizable transaction.
Mitigations on the record: each shape's witness K equals or closely tracks a real
golden's measured K (784 / 1257 / 1466 / 1681 / 1541 / 2837 / 3004 against goldens at
208 / 1554 / 2570 / 3262 / 3726 / 4647), and the shapes were cut from those goldens —
so the distance to reality is the redeemer/withdrawal map, not the shape of the value
flow.

### F3 — HIGH. The shape bridge is proved; half of it is consumed, and the half that matters is not.

All 25 `ShapeBridge` verdicts re-verified, including the 16 kernel-checked `exec`-level
`rfl` bridges (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; `inputs_M1`
depends on **no axioms at all**). Task A1 closed the `Honest.lean` half: the four
`LR_BUDGET_*` axioms now name `Runs.XRun K` (definitions moved to the new leaf module
`WSC/Runs.lean` to break the `Honest → ShapeBridge → Shaped/* → Honest` cycle, which is
why this had not been actioned before). **The `Composition.lean` half is still open: no
`bridge_<S>` is applied to anything, because no `LeafSet` field is discharged from a
shaped theorem** — and F2 explains why the consumer never arrived. Wiring the bridge in
is worthless until the shapes are re-cut.

### F4 — MEDIUM. "`sorry`-free" is false, including for every top-level theorem.

64 theorem-position results are closed by `blaster`'s `admit`. All four top-level
theorems inherit `sorryAx` through `p3_lifted` → the blaster-closed run-form P3. The
claim in `WSC/status-fragments/V4.md` that they are "`sorry`-free Lean theorems" is
**false as stated**; the fragment is left as the historical record. Nothing about the
mathematics changes — the P3 verdict is ✅ Valid — but a reviewer who greps for
`sorryAx` must not be surprised. A1's improvement here is real but narrower than a
sorry-count claim: `baseNonVacuous` and `mintingNonVacuous` no longer carry `sorryAx`
individually.

### F5 — MEDIUM, CLOSED by measurement. `K-MEASUREMENTS.md` §5.1's prep table was ~47× pessimistic.

Independently re-measured in this audit (cold, isolated, `lake build`, one module at a
time):

| module | budget | **A3 measured** | A1 measured | published §5.1 | overstatement |
|---|---|---|---|---|---|
| `WSC.Prep.Base` | 600 | **1.63 s** | 1.35 s | "≈11 s class" | ≈7× |
| `WSC.Prep.Minting900` | 900 | **1.46 s** | 1.53 s | 27.6 s | ≈19× |
| `WSC.Prep.Global1600` | 1600 | **45.54 s** | 37.8 s | **2,143 s** | **47×** |

The spread on `Prep.Global1600` across three independent runs is **36.6 – 45.5 s** (the
U3 audit's 44 s was under 30-way build parallelism). All three falsify 2,143 s. §5.1 is
marked SUPERSEDED with the cause (`lake env lean` without `--load-dynlib`, so
Blaster/PCB run interpreted, plus a substrate bump) and §5.1a carries figures measured
the right way. **This had a real cost:** task U2 declined to build `P1_Transfer`,
`P5_NonMember` and the entire shaped layer citing "a 35.7-min `#prep_uplc`", and
shipped edits validated against a partial build. The non-completions in the old table
were real timeouts, were not re-measured, and are **not** asserted to be affordable now.

### F6 — MEDIUM, count CORRECTED. `warn.sorry false` makes the build-log census incomplete, in 27 modules not 15.

Measured at this revision: **27** modules set `set_option warn.sorry false`; **16** of
them are in the built set. Earlier documents say 13, 15 or "15 modules". Any "expected
`sorry` whitelist = N" claim is a count of *unsuppressed* warnings only. The correct
instrument is `#print axioms` → `sorryAx`, reproducible in one command
(`WSC/Shaped/Probe/U3Census.lean`). Not fixed by deleting the options — that would bury
45+ expected warnings in every build.

### F7 — CLOSED. Every non-vacuity obligation is discharged.

`WSC/Props/Shaped/NonVacuity.lean` (downstream module, following the `P6Bridge.lean`
precedent) discharges `MintingNonVacuous` at 2500, `GlobalNonVacuous` at 1600 / 3300 /
4400 and `SeizeNonVacuous` at 3800; with `Composition`'s base-600 / minting-900 pair the
set is complete. All five `native_decide` on the real CEK: **0 project axioms, no
`sorryAx`.** Strictly cleaner than the discharge the finding pointed at
(`ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600` is `blaster` on
`appliedGlobal1600.prop` and carries `sorryAx`; retained as independent corroboration on
the `prop` term).

### F8 — LOW but structural, NARROWED not closed. `prop` vs `exec` (`PropExecFaithful`).

Every *shaped* leaf theorem hypothesises `isSuccessful (appliedXShaped.prop …)`; every K
measurement, every concrete accepting instance and every `native_decide` witness runs
`.exec`. `#prep_uplc` emits the two as separate terms (`PreProcess.lean:43-46`) and
equality is **not** definitional (`rfl` fails — `BridgeProbe2FAILS.lean`, kept as
evidence). Deliberately **not** axiomatized. A1 removed it from ONE path — the
base/keystone chain, by restating P3 itself on `Runs.baseRun K_base` with a fresh
vacuity probe at the run term — so `Composition.p3_lifted` mentions no `#prep_uplc`
output. **Restating the AXIOM does not remove it** (a point A1 corrected against the U3
recommendation): the 14 shaped theorem groups are still on `.prop` and reach the ledger
via `bridge_<S>` (Tier B, `blaster`). Doing the same restatement for all 14 — with 14
fresh, re-measured vacuity probes, and real risk of one coming back `Valid` (i.e.
vacuous), as happened to P6 at 2500 — is what would delete the residual campaign-wide.
Mitigation in place: every probe is stated on `.prop`, so the accept classes are
certified non-empty on the term the theorems use. `propRun_base_600` records the
equivalence at the base prep **with** its health warning (`blaster` normalises the left
side into the right, so the verdict is evidence of optimizer determinism, not of
faithfulness) and is used by nothing.

### F9, F10 — CLOSED (U3). Stale `LeafSet` docstrings; `WSC.ShapeBridge` outside the default build target.

Both fixed and re-verified: `WSC.lean` imports `ShapeBridge`, `Runs`, `P3_BaseRun`,
`NonVacuity` and `ShapeRealizability` (52 imports).

### F11 — CLOSED. `WSC/Props/P5_Witness1600.lean` is now citable.

It was two `#eval`s printing strings — evidence a human can read in a build log, not
kernel-checked propositions. It now opens with a banner naming exactly what is and is
not a theorem in it, and the two facts it was cited for are theorems
(`golden_halts_at_1600`, `golden_errors_at_1553`, `native_decide` on the real applied
golden flat). The `#eval`s are retained, each prefixed `NOT A THEOREM`.

### F12 — Carried forward, unchanged (with one measurement that makes D5 worse).

* **Blaster defect D6** — `#prep_uplc` emits kernel-ill-typed `Blaster.dite'` terms when
  a CIP-153 `Value` builtin result stays symbolic (the motive is not updated after De
  Morgan / Bool-polarity rewrites). Reproductions
  `WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`, deliberately non-building and
  **imported nowhere** — re-verified by grep. **Blocks SHAPES T3/T4, hence P1's
  containment dispatch Paths B/C and input-side aggregation over ≥ 2 mini-ledger inputs
  at UPLC.** Needs an upstream fix.
* **`WSC.LR5` does not entail `seizeCred ∈ txInfoWdrl`** from `seizeScopedToNodeOf`
  (`validScriptInfo` constrains the RUNNING script's purpose only). Isolated as
  `Composition.SeizeWdrlOfScoped`; needs a strengthened `LR5` with a
  `Conway/TxInfo.hs transTxRedeemers` audit row. Note the connection to F2: the same
  missing rule, in the other direction, **is** `RedeemerCoverage`, and
  `WSC/Honest.lean`'s LR-CTX table has **no row for `MissingRedeemers`**.
* **`ValueAlgebra` + `LedgerCanon` uninstantiated**, so `LR_BALANCE_SLOT` is still an
  axiom although `LR_BALANCE_SLOT_of_valueAlgebra` proves its exact statement from
  `LR7` plus those two residues. U2's finding stands: `valueOf` is **not** additive
  over `merge` without canonicity (`merge_not_additive_without_canonicity`, a
  `native_decide` counterexample), and CLAB has **zero** `Value` algebra, so
  "mechanical" was wrong — budget it as a ~330-line development.
* **D5, and worse than previously described.** `lakefile.lean` requires
  PlutusCoreBlaster from the **absolute local path** `/home/gumbo/iohk/PlutusCoreBlaster`
  (branch `cip153-value-builtins`, unpushed). New measurement: `lake-manifest.json`
  records `"type": "path"` and **no revision at all** for that dependency — so there is
  not even a local commit to re-pin against, and nothing distinguishes one working-tree
  state from another. Without those CIP-153 `Value` builtins
  `programmableLogicGlobal.flat` does not decode (verified negative control against PCB
  `main`: *"Could not decode program!"*), so **every** P1/P5/P6 "proved against
  production bytecode" claim inherits this. **Highest operational risk in the
  repository.** (For contrast, `Blaster` *is* pinned: git rev
  `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`.)

### F13 — MEDIUM, NEW. The golden cost tables are stale for the two accepting seize vectors, and one published limit rests on them.

Measured at this revision:

| vector | published (`MANIFEST.md:125-126`, `K-MEASUREMENTS.md:154-155`) | **actual JSON now** |
|---|---|---|
| `programmableSeize.seize-1-input` | 51,571,527 CPU / 140,357 mem, K = **2,570** | **60,231,630 / 163,820** |
| `programmableSeize.seize-2-inputs-partial-with-noise` | 96,841,491 / 251,272, K = **4,647** | **105,501,594 / 274,735** |

The published figures are exactly the **pre-fix** values, i.e. the K measurement
predates the ScriptContext-builder re-dump; every applied golden flat differs byte-wise
from the one measured, so the "PCB budget = ledger? exact" verdicts and the step counts
2,570 / 4,647 in that table describe vectors that have since been replaced. Nothing
*proved* depends on them (no theorem consumes a seize golden's K). **One published limit
does:** `K_seize = 3800`'s stated scope ("does not cover the 2-input accepting seize
golden at 4,647 steps") quotes a stale K. Direction is favourable — the corrected costs
are **higher**, so the true K's are ≥ 2,570 / ≥ 4,647 — which makes the limit statement
conservative and still correct, and makes the corrected ≈3,000 steps for
`seize-1-input` *consistent* with the shaped P2 witnesses at K = 3004 / 3328. Re-measure
before quoting either number.

### F14 — LOW, NEW. `WSC/flats/PROVENANCE.md`'s closing note is factually false.

It states that `programmableLogicGlobal.flat` does not decode and that its
`#import_uplc` is kept commented until task U5. U5 landed; the import is live at
`WSC/Prep/Global.lean:46` and `WSC/Prep/Global1600.lean:66`. The provenance **table** in
the same file is correct and now independently re-verified (§6.1). Not this audit's file
to edit.

### F15 — LOW, NEW. A1's `K`-widening is real and inert; see §7.1(b)/(c).

The four budget bridges now assert the ledger↔meter equivalence at seven proved budgets
rather than two, and six of the seven instantiations are consumed by nothing (§3.3 item
3). One of the four restatements (`LR_BUDGET_seize`) was a repair of a statement that
collapsed to an unbounded claim, not a restatement — a strict weakening that A1's own
report described only as "restated".

### F16 — INFORMATIONAL, NEW. A2's inhabitation is an implication, not a closed `∃`.

`containedTx_witness` proves
`outputs = containedWitnessOuts hp.progLogicCred → ContainedTx hp ctx`. Since
`ContainedTx` constrains only `txInfoOutputs` and `ScriptContext` is inhabited, the
class is non-empty — but a closed `∃ ctx, ContainedTx hp ctx` is not in the library.
One `refine ⟨_, _⟩` away.

---

## 9. WHAT A REVIEWER SHOULD NOT BELIEVE

1. **Do not believe "the WSC containment property is proved."** It is (a)
   machine-checked as a *reduction* to four leaf obligations plus 26 project axioms, and
   (b) discharged outright over one class whose defining property is that nothing leaves
   the mini-ledger for accounting reasons. Neither is the claim. The reduction plus the
   six leaf results is the deliverable.
2. **Do not believe that instantiating the `Shape` parameter with a shaped context
   class would fix that.** It produces a true theorem about an **empty** class.
   `WSC/Props/Shaped/ShapeRealizability.lean` proves the emptiness — unconditionally for
   SHAPE T1, under the Conway `MissingRedeemers` rule for the rest — and exhibits the
   vacuous `LeafSet` so the trap is visible rather than described.
3. **Do not believe any UPLC result is universally quantified over transactions.** Every
   one is bounded by a CEK step budget AND by a fixed `Data` skeleton. Quote both bounds
   or quote neither. There is no coverage theorem; §5.2 exhibits a theorem that provably
   does not generalise; and F2 shows the shapes are not node-buildable at all.
4. **Do not believe "`sorry`-free".** 64 theorem-position results are closed by
   `blaster`'s `admit`; their certification is a `✅ Valid` Z3 verdict in the build log,
   not a kernel check. All four top-level theorems inherit `sorryAx` through P3. And do
   not use the build log's `sorry` warning count as a census — 27 modules suppress it.
5. **Do not believe the witnesses and the theorems are always about the same term.** For
   the shaped layer: theorems on `.prop`, witnesses and all measured K on `.exec`,
   equality unproved. **No longer true** for the base/keystone path, every
   `*NonVacuous` obligation and every published K constant — those state and witness on
   the same `Runs.XRun K` term. Name the layer when quoting this.
6. **Do not believe the source-model and shaped routes are the same strength.** The
   model route (`globalModel_faithful`, `seizeModel_faithful`) quantifies over all
   contexts and all step counts but trusts a hand transcription; the shaped route trusts
   no transcription but is doubly bounded and quantifies over unrealizable skeletons.
   Neither dominates.
7. **Do not believe the prep-cost figures in `K-MEASUREMENTS.md` §5.1**, or the golden
   cost/K rows for the two accepting seize vectors (F5, F13). Measure before concluding
   anything is unaffordable, and always with `lake build`.
8. **Do not believe this builds anywhere else.** The substrate pin is an absolute local
   path to an unpushed branch, with **no revision recorded in the manifest**.
9. **Do believe, because it is now machine-verified:** the four `.flat` files are
   byte-identical to the `cborHex` of the named unapplied production scripts at the
   recorded wsc-poc commit (§6.1). That part of the chain is no longer a matter of trust.

---

## 10. REPRODUCTION

```bash
# 1. clean-room rebuild of everything
#    expect: 405 jobs, ~98 s, 101 ✅ markers (66 Valid + 35 Expected Falsified),
#            0 errors, 0 ⚠️/❌, 20 expected `sorry` warnings, 67 WSC modules
cp -a <CLAB> <SCRATCH>/clab-audit && cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census from that log
grep -o 'WSC/[^ ]*: ✅ [A-Za-z ]*' build.log | wc -l          # 101
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c            # 66 Valid, 35 Exp. Falsified
grep -cE '⚠️|❌' build.log                                    # 0
grep -c 'error:' build.log                                    # 0
grep -c "declaration uses 'sorry'" build.log                  # 20  (NOT a census — §2)

# 3. source reconciliation (35 + 2 + 64 = 101), over the BUILT modules only
grep -h '^#blaster' <built modules> | grep -o 'solve-result: [01]' | sort | uniq -c
#   -> 35 x "solve-result: 1", 2 x "solve-result: 0"
# then count `blaster` tactic invocations in theorem position -> 64

# 4. axiom census (2.7 s warm) — `#print axioms` only, adds no trust surface
lake build WSC.Shaped.Probe.U3Census
grep -E 'depends on axioms|does not depend' build.log         # 73 lines, 8 with sorryAx
#   the 8 `#print axioms` at the end of WSC/Composition.lean carry §3.1's set comparison

# 5. axiom-declaration census
grep -rn '^axiom ' --include='*.lean' WSC/ | awk -F: '{print $1}' | sort | uniq -c  # 50
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0
grep -rl 'set_option warn.sorry false' --include='*.lean' WSC/ | wc -l              # 27

# 6. prep-cost re-measurement (the F5 repair) — always `lake build`, never `lake env lean`
for m in Base Minting900 Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.{olean,ilean,trace} .lake/build/lib/lean/WSC/Prep/$m.*.hash
  /usr/bin/time -f "$m %e s %M KB" lake build WSC.Prep.$m > /dev/null
done                       # expect ~ 1.6 / 1.5 / 36-46 s

# 7. PROVENANCE re-verification (§6.1)
sha256sum WSC/flats/*.flat
git -C <wsc-poc worktree> show \
  7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum

# 8. golden redeemer/withdrawal counts behind F2's table  (needs python3 cbor2)
#    decode scriptContextHex -> take .value[0].value -> fields [0] inputs, [6] wdrl, [9] redeemers
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artefact is the
entire content of F5.
