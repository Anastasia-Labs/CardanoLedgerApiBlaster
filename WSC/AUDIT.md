# WSC containment campaign — INDEPENDENT AUDIT (task U3)

**What this file is.** The last technical gate before the campaign is quoted
outside this repository. Nothing below is taken on any earlier agent's word: every
number was re-measured in a clean-room rebuild on 2026-07-25, and every claim that
could not be reproduced is listed in §7 FINDINGS. Where an earlier report was
wrong, the correction is named with the report that made the claim.

Audited revision: branch `wsc-containment-proofs`, HEAD `a8d95a7` (task U1) with
parent `92f3255` (U2), `0e2a99d` (V3), `521e49c` (Z6), `e519cf7` (V4).
Environment: 32-core box, Lean 4.24.0, Z3 4.15.2, `maxHeartbeats 0`,
PlutusCoreBlaster `cip153-value-builtins` (**unpushed**, ARCHITECTURE E11),
Blaster `beta-lambda-cache-optimization`.

**The one-paragraph answer.** The library is internally consistent: 98 solver
verdicts, all ✅, zero errors, zero unexplained `sorry`s, and the leaf theorems
say what they claim to say in ground-truth vocabulary. It is **not** a proof of
the top-level claim, and no honest reading makes it one. `top_claim` is an
*implication*: it consumes a `leaves : LeafSet hp Shape` bundle that **is never
constructed anywhere in the library**, and it depends on **26 project axioms**
plus `sorryAx`. The shaped leaf theorems are real results about the real compiled
bytecode, but they are bounded twice (CEK budget AND shape), no shape-coverage
argument exists, and they are not wired into `top_claim`. See §7 F1-F3.

---

## 1. CLEAN-ROOM REBUILD

### 1.1 Method

```
cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-audit    # HEAD a8d95a7
cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.olean \
       .lake/build/lib/lean/WSC.ilean .lake/build/lib/lean/WSC.olean.hash \
       .lake/build/lib/lean/WSC.ilean.hash .lake/build/lib/lean/WSC.trace
/usr/bin/time -v lake build WSC WSC.ShapeBridge
```

Dependency oleans (`CardanoLedgerApi`, and the `PlutusCore` / `Blaster` packages
under `.lake/packages`) were **kept**; every `WSC.*` olean/ilean/trace was
deleted. That is the right cut and a full `lake clean` was not needed: no WSC
verdict is computed in a dependency module — every `#import_uplc`, every
`#prep_uplc` and every `#blaster` lives in a `WSC/` module, so deleting the WSC
oleans forces all of them to run for real. Confirmed by the log: **63 WSC modules
re-elaborated** (jobs 325→401 of 401), including all 9 unshaped/shaped
`#prep_uplc` modules and all 98 solver invocations.

### 1.2 Result

| measurement | value |
|---|---|
| exit status | **0** — `Build completed successfully (401 jobs)` |
| wall clock | **1 m 33.66 s** |
| user + sys CPU | 251.4 s + 33.4 s (304 % of one core) |
| max RSS | 1.61 GB |
| WSC modules re-elaborated | 63 |
| `error:` lines | **0** |
| solver verdicts | **98**: 64 × `✅ Valid`, 34 × `✅ Expected Falsified` |
| `⚠️ Undetermined` / `❌` markers | **0** |
| `declaration uses 'sorry'` | 21 (census in §2) |
| other warnings | 64, all `This simp argument is unused` (cosmetic; 48 in PCB `Value/*`, 16 in `WSC/Props/P2_Seize.lean`) |

The 98 verdicts reconcile **exactly** against the sources, which is the check that
rules out a silently-skipped stanza:

* 36 standalone `#blaster` commands exist in the built set. 34 declare
  `(solve-result: 1)` = "expect Falsified" → 34 × `✅ Expected Falsified`.
  2 declare `(solve-result: 0)` = "expect Valid, i.e. expect VACUOUS"
  (`WSC/Prep/Global.lean:83` `global_vacuity_probe_600`,
  `WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous`) → 2 × `✅ Valid`.
* 62 `theorem … := by blaster` in the built set → 62 × `✅ Valid`.
* 34 + 2 + 62 = **98**. No stanza is unaccounted for and none is skipped.

Per-file verdicts (all ✅; complete list with `file:line` in
`<SCRATCH>/markers.txt`, regenerable from the log):

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
| `WSC/Props/Shaped/P5Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Unshaped.lean` | 1 | 1 |
| `WSC/Composition.lean` | 1 | — |
| `WSC/Goldens/Witnesses.lean` | 1 | — |
| `WSC/Prep/Global.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/P4_Minting.lean` | 1 (vacuity BY DESIGN) | — |

### 1.3 Transcript tail

```
info: WSC/ShapeBridge.lean:1607:0: 'WSC.ShapeBridge.inputs_M1' does not depend on any axioms
info: WSC/ShapeBridge.lean:1608:0: 'WSC.ShapeBridge.exec_M1' depends on axioms: [propext, Classical.choice, Quot.sound]
info: WSC/ShapeBridge.lean:1609:0: 'WSC.ShapeBridge.exec_T1' depends on axioms: [propext, Classical.choice, Quot.sound]
info: WSC/ShapeBridge.lean:1610:0: 'WSC.ShapeBridge.bridge_M1' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Build completed successfully (401 jobs).
        Elapsed (wall clock) time (h:mm:ss or m:ss): 1:33.66
        Maximum resident set size (kbytes): 1649648
        Exit status: 0
```

Slowest modules (cold, this rebuild): `WSC.Prep.Global1600` **44 s**,
`WSC.ShapeBridge` 36 s, `WSC.Shaped.MintingLocalShapedIdx` 31 s,
`WSC.Props.Shaped.P2Shaped` 25 s. Everything else ≤ 7 s. **See §7 F5: the 44 s
falsifies the 2,143 s (35.7 min) figure that `WSC/goldens/K-MEASUREMENTS.md` §5.1
publishes for the same module and that task U2 used as its reason for not building
half the library.**

---

## 2. SORRY / ADMIT CENSUS

21 `declaration uses 'sorry'` warnings, classified as the task requires:

| class | count | detail |
|---|---|---|
| **(a)** blaster `admit` on a declaration that reported ✅ Valid | **20** | `WSC/Composition.lean:1059` → `:1061 ✅ Valid`; `WSC/ShapeBridge.lean:{834,847,863,879,899,920,941,960,982,1005,1027,1050,1078,1101,1124,1147,1350,1360,1436}` → each pairs with the next ✅ Valid marker in the same file (the marker sits on the `by blaster` position, several lines below the `theorem` keyword, because the statements are long) |
| **(b)** PCB pre-existing | **1** | `PlutusCore/UPLC/CekMachine.lean:299:4` — not WSC code, unchanged |
| **(c)** anything else = DEFECT | **0** | — |

**The warning count is NOT a census, and must not be quoted as one (F6).** 13 WSC
modules carry `set_option warn.sorry false`
(`P1Shaped`, `P2Shaped`, `P4Shaped`, `P4ShapedIdx`, `P4LocalShaped`,
`P4DelegateShaped`, `P5Shaped`, `P6Shaped`, `P6Bridge`, `P3_Base`, `P5_NonMember`,
`P4_Minting`, `Goldens/Witnesses`, plus `Calib/P3Shaped`, `Calib/P3Unshaped`), so
the ~42 further blaster-closed theorems in them emit no warning at all. U1's
"expected `sorry` whitelist = 19" is therefore a count of *unsuppressed* warnings,
not of `admit`s. The authoritative instrument is `#print axioms` → `sorryAx`
(§3), and by that instrument **every** `by blaster` theorem in the library is
admit-closed.

Literal-source grep (`sorry` / `admit` / `stop` / `axiom` over `WSC/**/*.lean`):

* **no** literal `sorry`, `admit` or `stop` in tactic position anywhere in `WSC/`.
  Every hit is either the string `set_option warn.sorry false` or prose in a
  docstring.
* **47** `axiom` declarations, all in the four intended places:
  `WSC/Honest.lean` (**35**), `WSC/Composition.lean` (**10**),
  `WSC/Props/P1_Transfer.lean` (1 = `globalModel_faithful`),
  `WSC/Model/SeizeModel.lean` (1 = `seizeModel_faithful`).
  **No `axiom` hides in any `Props/Shaped/*`, `Shaped/*` or `Prep/*` module** —
  i.e. the shaped layer really does add no assumption, which is its central claim.
  Of the 47, `top_claim` reaches 26 (§3.1) — all 10 of `Composition.lean`'s and 16
  of `Honest.lean`'s. The 21 it does **not** reach are exactly what the open
  `LeafSet` fields would pull in: `LR1`-`LR7` (7), `LR_BUDGET_minting`,
  `LR_BUDGET_global`, `LR_BUDGET_seize`, `GlobalPreppedAt`, `DIRWF`, `TS1`, `TS2`,
  `TS3`, `TS4`, `TS5`, `TS_MINTING_IDENTITY`, `nodeStepsSeize`, and the two
  faithfulness axioms. **A reviewer must read "26" as a floor, not a ceiling.**

---

## 3. AXIOM CENSUS

Reproduce with `lake build WSC.Shaped.Probe.U3Census` (2.7 s warm) — that module
is `#print axioms` only and adds no trust surface.

Legend: **(i)** Lean-standard `propext`/`Classical.choice`/`Quot.sound`;
**(ii)** `native_decide` = `Lean.ofReduceBool`+`Lean.trustCompiler`;
**(iii)** `sorryAx` = blaster's `admit`; **(iv)** project axioms, counted.

| theorem | (i) | (ii) | (iii) | (iv) project axioms |
|---|---|---|---|---|
| **`WSC.Composition.top_claim`** | ✓ | ✓ | ✓ | **26** — see §3.1 |
| `WSC.Composition.no_programmable_tokens_outside_mini_ledger` | ✓ | ✓ | ✓ | **26** (identical set) |
| `WSC.Composition.preservation` | ✓ | ✓ | ✓ | 22 (top_claim's minus `DIRWF_L`, `Genesis`, `NONNEG_L`, `ts_genesis`) |
| `WSC.Composition.nonEscape_of_registered` | ✓ | ✓ | ✓ | 20 |
| `WSC.Composition.p3_lifted` | ✓ | ✓ | ✓ | 9 |
| `WSC.P1_T1` / `P1_T2` / `P1_T6` / `P1_T7` | ✓ | — | ✓ | **0** |
| `WSC.P1_T1_negative_control` | ✓ | — | ✓ | 0 |
| `WSC.P2a_shaped_structure` / `P2b_shaped_containment` / `P2_shaped` | ✓ | — | ✓ | **0** |
| `WSC.P2a_shaped_negative_control` / `P2b_shaped_negative_control` | ✓ | — | ✓ | 0 |
| `WSC.P3_base_requires_global_or_seize` / `P3_base_negative_control` | ✓ | — | ✓ | **0** |
| `WSC.P4a_shaped_mint_runs_minting_logic`, `P4_burn_only_shaped`, `P4_burnonly_arm_shaped` | ✓ | — | ✓ | **0** |
| `WSC.P4a_shapedIdx_mint_runs_minting_logic`, `P4_burn_only_shapedIdx` | ✓ | — | ✓ | 0 |
| `WSC.P4_local_noEscape_shaped`, `P4_local_noEscape_shapedIdx`, `P4_local_arm_shaped`, `P4_disjunction_at_L1` | ✓ | — | ✓ | **0** |
| `WSC.P4_delegateTransfer_arm_shaped`, `P4_disjunction_at_DT1` | ✓ | — | ✓ | 0 |
| `WSC.P4_delegateSeize_arm_shaped`, `P4_disjunction_at_DS1` | ✓ | — | ✓ | 0 |
| `WSC.P5_shaped_indexed` / `P5_shaped_exists` | ✓ | — | ✓ | **0** |
| `WSC.P5_shaped_groundtruth` | ✓ | — | ✓ | 3 — `Deployed`, `OnChain`, `TS3` |
| `WSC.P6_shaped_noBaseInputs` | ✓ | — | **—** | **0** (pure Lean; the only headline with no `sorryAx`) |
| `WSC.P6_shaped_member_adds_to_requirement`, `P6_shaped_member_mint_stays_at_base` | ✓ | — | ✓ | 0 |
| `WSC.Model.P1_bytecode_of_P1_model`, `P6_bytecode_of_P6_model` | ✓ | — | — | 1 — `Model.globalModel_faithful` |
| `WSC.P2.P2a_bytecode`, `P2.P2b_model_implies_bytecode` | ✓ | — | — | 1 — `SeizeModel.seizeModel_faithful` |
| `WSC.P2.P2a_seizeModel_preserves_structure` | ✓ | — | — | 0 (about the model only) |
| `WSC.ShapeBridge.exec_M1` / `exec_T1` | ✓ | — | **—** | **0** — kernel-checked `rfl` |
| `WSC.ShapeBridge.bridge_M1` / `bridge_T1` | ✓ | — | ✓ | 0 |
| `WSC.ShapeBridge.inputs_M1` | — | — | — | **0 — "does not depend on any axioms"** |
| `WSC.Composition.mintingNonVacuous` | ✓ | ✓ | ✓ | 0 |
| `WSC.Composition.LR_BALANCE_SLOT_of_valueAlgebra` | ✓ | — | — | 2 — `LR7`, `OnChain` (notably **not** `LR_BALANCE_SLOT`) |
| `WSC.Composition.leafP1_of_shapedGlobalContainment` | ✓ | — | — | 4 — `Deployed`, `NodeAcceptsGlobal`, `OnChain`, `TS3` |
| `WSC.Composition.p4_disjuncts_of_custody` | ✓ | — | — | 1 — `OnChain` |
| `WSC.Composition.coveringIn_of_coveringRaw` | ✓ | — | — | 3 — `Deployed`, `OnChain`, `TS3` |
| `WSC.Composition.coveringRaw_false_of_registered` | ✓ | — | — | 5 — + `LedgerStep`, `lr_inputs_in_ledger` |
| `WSC.covering_node_excludes_registration`, `covering_excludes_registeredIn` | ✓ | — | — | **0 — PROVED** |
| `WSC.Composition.contain_iff_modelSums`, `outSum_eq_sumOutsIf` | ✓ | — | — | 0 |
| all 14 concrete CEK witnesses (`K_T1_is_2603`, `K_is_1681`, `K_is_2837`, `mintPos_form_REFUTED`, …) | ✓ | ✓ | **—** | **0** |

### 3.1 The headline number a reviewer needs

**`WSC.Composition.top_claim` depends on 26 project axioms**, plus `sorryAx`,
`Lean.ofReduceBool`, `Lean.trustCompiler` and the three Lean-standard axioms — 32
entries in total, which reproduces U2's count exactly.

From `WSC/Honest.lean` (16):

```
Deployed  OnChain
LR_CTX  NONNEG  LR_BUDGET_base
LR_MINT_RUNS_POLICY  LR_SPEND_RUNS_VALIDATOR  LR_WDRL_RUNS_VALIDATOR
NodeAcceptsBase  NodeAcceptsGlobal  NodeAcceptsMinting  NodeAcceptsSeize
nodeStepsBase  nodeStepsGlobal  nodeStepsMinting
mlhPolicyId
```

From `WSC/Composition.lean` (10):

```
LedgerStep  Genesis
lr_utxo_semantics  lr_inputs_in_ledger  lr_registration_source
LR_BALANCE_SLOT  NONNEG_L  DIRWF_L
ts_genesis  ts_minting_identity_L
```

Three properties of that list a reviewer should notice, none of them flattering:

1. **`top_claim` carries `sorryAx`.** It reaches `p3_lifted`, which reaches the
   blaster-closed P3 theorem. So the kernel did **not** check `top_claim`; its
   status is "checked modulo the `✅ Valid` verdict of a Z3 run". That is the same
   trust level as every other blaster result here, but it means the sentence "the
   top theorem is `sorry`-free" — which appears in `WSC/status-fragments/V4.md` —
   is **false as stated** (F4).
2. **No P1/P2/P4/P5/P6 result appears in the list.** Not because they are
   discharged, but because they enter as the `leaves : LeafSet hp Shape`
   *hypothesis*. No `LeafSet` value is constructed anywhere in the library
   (verified by grep: every occurrence is a binder, a docstring or the structure
   declaration). `top_claim` is an implication whose antecedent is open (F1).
3. **`LR_BUDGET_global`, `LR_BUDGET_minting`, `LR_BUDGET_seize`,
   `GlobalPreppedAt`, `TS1`, `TS2`, `TS4`, `TS5`, `DIRWF`, `LR1`-`LR7` are NOT in
   the list.** They are not reached, because the leaves that would reach them are
   hypotheses. Anyone who instantiates the `LeafSet` will add them.

---

## 4. VACUITY RE-VERIFICATION

Highest-risk failure mode in the library, per the task, and the reason is on the
record: task V3 stated P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and only the
mandatory probe revealed the class was accept-**UNSAT** — the theorem was empty.
Preserved as `WSC/Shaped/Probe/G6Vacuous2500.lean`. P6 was restated at 3300
(witness K = 2837).

Every accept-hypothesis theorem, its prep term, and its probe **at that same prep
term** (verified by reading the `applied*.prop` identifier on both sides, not by
trusting the docstrings):

| theorem(s) | prep term (budget) | probe | probe result | second, solver-free witness |
|---|---|---|---|---|
| `P3_base_requires_global_or_seize` | `appliedBase.prop` (600) | `P3_base_vacuity_probe` `:112` | **Expected Falsified** | `P3Witness` accepts at 600 (K = 208 golden) |
| `P1_T1` | `appliedGlobalShapedT1.prop` (4400) | `P1_T1_vacuity_probe` `:380` | **Expected Falsified** | `K_T1_is_2603` |
| `P1_T2` | `appliedGlobalShapedT2.prop` (4400) | `P1_T2_vacuity_probe` `:403` | **Expected Falsified** | `K_T2_is_3572` |
| `P1_T6` | `appliedGlobalShapedT6.prop` (4400) | `P1_T6_vacuity_probe` `:861` | **Expected Falsified** | `K_T6_is_3150` |
| `P1_T7` | `appliedGlobalShapedT7.prop` (4400) | `P1_T7_vacuity_probe` `:884` | **Expected Falsified** | `K_T7_is_3572` |
| `P2a_shaped_structure`, `P2b_shaped_containment`, `P2_shaped` | `appliedSeizeShaped3800.prop` (3800) | `P2_shaped_vacuity_probe` `:630` | **Expected Falsified** | `K_is_3004_and_3328` |
| `P4a_shaped_*`, `P4_burn_only_shaped`, `P4_burnonly_arm_shaped` | `appliedMintShaped900.prop` (900) | `P4_shaped_vacuity_probe` `:247` | **Expected Falsified** | `exec_accepts_at_900`, K = 784 |
| `P4a_shapedIdx_*`, `P4_burn_only_shapedIdx` | `appliedMintShapedIdx900.prop` (900) | `P4_shapedIdx_vacuity_probe` `:103` | **Expected Falsified** | — (shares M1's witness) |
| `P4_local_*`, `P4_disjunction_at_L1` | `appliedMintLocalShaped2500.prop` (2500) | `P4_local_vacuity_probe` `:545` | **Expected Falsified** | `K_is_1681` |
| `P4_local_noEscape_shapedIdx` | `appliedMintLocalIdxShaped2500.prop` (2500) | `P4_localIdx_vacuity_probe` `:455` | **Expected Falsified** (300 s cap) | — |
| `P4_delegateTransfer_*`, `P4_disjunction_at_DT1` | `appliedMintDTShaped2500.prop` (2500) | `P4_delegateTransfer_vacuity_probe` `:360` | **Expected Falsified** | `ctxDT_K_is_1257` |
| `P4_delegateSeize_*`, `P4_disjunction_at_DS1` | `appliedMintDSShaped2500.prop` (2500) | `P4_delegateSeize_vacuity_probe` `:530` | **Expected Falsified** | `ctxDS_K_is_1466` |
| `P5_shaped_indexed/_exists/_groundtruth` | `appliedGlobalShaped1600.prop` (1600) | `P5_shaped_vacuity_probe` `:398` | **Expected Falsified** | `K_is_1541` |
| `P6_shaped_member_*` | `appliedGlobalMemberShaped3300.prop` (3300) | `P6_shaped_vacuity_probe` `:363` | **Expected Falsified** | `K_is_2837` |
| P3 calibration pair | `appliedBaseShaped.prop` / `appliedBase.prop` | `P3_shaped_vacuity`, `P3_unshaped_vacuity` | **Expected Falsified** ×2 | — |

**Verdict: 14 of 14 accept-hypothesis theorem groups have a vacuity probe at their
own prep term and their own shape, and all 14 report Falsified (= non-empty accept
class). No theorem is without a probe. No probe returned `Valid` where `Valid`
would mean vacuous.** Additionally, 13 of 14 carry a solver-free second witness (a
concrete `ScriptContext` run through the real CEK by `native_decide`), so
non-vacuity does not rest on the solver alone.

Two `✅ Valid` markers in §1.2 ARE vacuity results, deliberately, and no theorem is
stated at either term — checked by grep, not assumed:

* `WSC/Prep/Global.lean:83` `global_vacuity_probe_600` — `appliedGlobal.prop`
  (600) is provably accept-UNSAT. Only use of that term in a `Prop` anywhere.
* `WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous` — same for
  `appliedMinting.prop` (600). Its only use.

Open vacuity items (not defects, but not closed either):

* `GlobalNonVacuous` at the **unshaped** `appliedGlobal1600.prop`: the symbolic
  probe gave no verdict in 87 min (`P5_NonMember.lean:548`). U1 discharged it via a
  closed `blaster` goal (`ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`,
  ✅ Valid, re-verified in this rebuild at `ShapeBridge.lean:1436`). `WSC/Honest.lean`
  still records it open; the repair is one `:=` (F7).
* `SeizeNonVacuous` at `appliedSeize.prop` (600): unreachable at any affordable
  budget; the 600 and 1000 probes return `Valid` (vacuous). No theorem is stated
  there.

---

## 5. ANTI-TAUTOLOGY SPOT-CHECK

Three most load-bearing theorems, read line by line. The question in each case:
**is the postcondition a fact about the transaction, or is it "the validator's own
accumulator came out true"?**

### 5.1 P1 containment — `WSC.P1_T1` (`P1Shaped.lean:179-223`)

Postcondition:
`Model.outSum (.ScriptCredential plc) cs tn ctx.…txInfoOutputs ≥ Model.inSum … ctx.…txInfoInputs + Model.mintSigned cs tn ctx.…txInfoMint`.

* `Model.outSum` / `inSum` (`WSC/Model/Ground.lean:43-56`) are independent
  structural recursions over the context's own output/input lists, guarded by
  `WSC.payCred o == base` (`Spec.lean:31`, i.e. `txOutAddress.addressCredential`)
  and summing CLAB's `valueOf`. `Model.mintSigned` is `valueOf cs tn mint`
  (`P1_Transfer.lean:192`), definitionally `WSC.mintOf`. **No validator function
  appears in the postcondition** — the validator appears only in the hypothesis
  `isSuccessful (appliedGlobalShapedT1.prop …)`.
* The base credential `plc` is not a free choice: it is the same variable the
  shape puts in the params-UTxO datum the validator reads
  (`p1ShapedCtx … dirCS glc slc …`), so the theorem is about the deployment's own
  mini-ledger credential.
* The escape route is REAL, which is the part that could have made this vacuous.
  SHAPE T1 carries a second input at a non-base address and a second output at a
  non-base address, so ledger balance alone gives only
  `qIn + qIn2 + mint = qOut + qEsc` and does not imply the conclusion.
  `P1ShapedWitness.ctxOk_*` is an ACCEPTED instance with `qEsc = 4 > 0`, and
  `exec_rejects_escape` is a `validRewardingContext`-clean instance that violates
  the conclusion and is REJECTED by the real CEK (`native_decide`).
* **Doubt, recorded:** the *hypothesis* `Model.coveringNodeExists … = false` is in
  raw-decode vocabulary, not ground truth. That is a hypothesis, so it only
  weakens the theorem, and §7.1 of `Composition.lean` bridges it at a cost of
  `TS3`. No tautology risk.

**Verdict: ground truth. Not true by construction.**

### 5.2 P2b containment — `WSC.P2b_shaped_containment` (`P2Shaped.lean:288`)

Postcondition:
`WSC.P2.sumOutAtBase base key tn ctx.…txInfoOutputs ≥ WSC.P2.sumInAtBase base key tn ctx.…txInfoInputs + WSC.mintOf key tn ctx.…txInfoMint`,
universally quantified over `tn`.

* `sumOutAtBase` / `sumInAtBase` (`P2_Seize.lean:258-272`) are again independent
  recursions over the context's lists using `WSC.outAtBase`/`inAtBase` (pure
  `payCred == base`) and `valueOf`. Nothing from the seize validator's
  `valueDelta` / `remainingProgCSDelta` / `ptokenPairsContain` machinery appears.
* The seized policy `key` is the directory node datum's key field, i.e. the object
  the validator itself authenticated — again not a free choice.
* `P2_shaped_gates_are_earned` (`:342`, ✅ Valid) shows the three authentication
  gates (`pCS = ppCS`, `nCS = dirCS`, `w1 = ilsH`) are each a pair of DISTINCT free
  variables in the shape, so they are earned by the bytecode and not pre-satisfied.
* `exec_rejects_escaping_seize` and `exec_rejects_stolen_staking_credential`
  (`native_decide`, real CEK) are the excluded-case witnesses.
* **Doubt, recorded:** this is the conjunct that is FALSE-in-general on the source
  model (obligation B1 has two machine-checked counterexamples —
  `ptokenPairsContain` is unsound with duplicate token names or unsorted maps).
  It closes here *because* SHAPE S1 gives every value exactly one policy and one
  token name, so the counterexamples cannot be instantiated. That is a genuine
  result about the bytecode on that class, and it is **also** the sharpest example
  in the library of why a shape bound is not a footnote: this theorem does not
  generalize by inspection.

**Verdict: ground truth. Not true by construction. Shape-bound in an essential,
not incidental, way.**

### 5.3 P4-Local no-escape — `WSC.P4_local_noEscape_shaped` (`P4LocalShaped.lean:203`)

Postcondition:
`noEscape (.ScriptCredential plc) ownCS (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true`,
where `noEscape` (`Spec.lean:187-191`) is
`∀ o. payCred o == progLogicCred || ¬ hasCurrencySymbol cs o.txOutValue`.

* Checked that the list in the conclusion IS the transaction's output list:
  `localShapedCtx` sets `txInfoOutputs := localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1`
  (`MintingLocalShaped.lean:223`) — the same application, same argument order. So
  the scan is over every output of the transaction, not a sub-list. Same check for
  `P4_local_registration_shaped`, whose conclusion is over the literal 2-element
  reference-input list that `txInfoReferenceInputs` is set to (`:220-222`).
* Both disjuncts of the per-output condition are live: `o0h` and `plc` are
  distinct free variables (credential disjunct), `c0` and `ownCS` are distinct free
  variables (value disjunct). Output 1 is ada-only and clears via the value
  disjunct; output 0 must clear via the credential disjunct, which the bytecode has
  to earn.
* `exec_rejects_escaping_output` is the excluded-case witness through the real CEK.
* This is the theorem where the *policy's own* no-escape scan becomes ground
  truth. The two delegating arms (DT1/DS1) prove strictly less — only that a
  sibling validator RUNS (`credentialInWithdrawals`) — and their docstrings say so.

**Verdict: ground truth. Not true by construction.**

### 5.4 What I did NOT check

* The `#prep_uplc`-produced `.prop` terms themselves. Every leaf theorem's
  hypothesis is `isSuccessful (appliedX.prop …)`; every witness and every K
  measurement runs `appliedX.exec`. `prop = exec` is **not proved** (U1 §5,
  `PropExecFaithful`). See F8.
* The `.flat` provenance chain (`WSC/flats/PROVENANCE.md`); out of scope for this
  unit and unchanged by U1/U2.

---

## 6. STATUS.md RECONCILIATION

`WSC/STATUS.md` has been rewritten from this audit, not from the fragments. The
six `WSC/status-fragments/*.md` are merged and superseded (kept as the per-task
record). Changes forced by §1-§5 rather than by any fragment's own claim:

* **P1** and **P2**: the verdict `NOT-REACHABLE-AT-UPLC` is WITHDRAWN. Both are
  proved at UPLC over named shapes, re-verified here.
* **P6**: `PROVED-ON-SOURCE-MODEL only` → also at UPLC at SHAPE G6 / 3300, with
  the 2500 vacuity failure recorded in the same row (it is the most instructive
  negative result in the campaign).
* **P4**: arms 1-3 are no longer "no shape has been written".
* **Composition**: "the file does not exist" → exists and is green, as a
  REDUCTION with an un-instantiated `LeafSet`.
* Every row now carries budget + shape + scope, and the two words the task forbids
  (`PROVEN-BY-DESIGN`, and any unbounded claim) do not appear.
* `WSC/Props/P1_Transfer.lean`'s `DirWF_partition_conjunct_missing` docstring is
  marked **SUPERSEDED** (comment-only edit) with the three declarations that
  superseded it.

---

## 7. FINDINGS, ranked by severity

### F1 — CRITICAL (not a defect, a framing risk). The top claim's antecedent is never constructed.

`WSC.Composition.top_claim` and `no_programmable_tokens_outside_mini_ledger` take
`leaves : LeafSet hp Shape`. **No `LeafSet` term exists in the library** — grep
over `WSC/**/*.lean` returns only binders, docstrings and the structure
declaration. U2 proved the *ingredients* for two of the four fields
(`leafP1_of_shapedGlobalContainment`, `p4_disjuncts_of_custody`), both of which
still consume a residue (`ShapedGlobalContainment` = shape bridge + the 4400
global budget bridge; `LocalCustodyOk ∨ …` from the shaped arms), and `p2` /
`nopre` are untouched. **Nothing in this repository proves the top-level claim.
What exists is a machine-checked reduction of it to four named obligations plus 26
axioms.** Every external quotation must say so. Not fixable here; it is the
remaining work.

### F2 — CRITICAL. No shape-coverage argument exists, and one shape is known not to generalize.

Every UPLC result for P1, P2, P4 arms, P5, P6 is bounded by a shape as well as a
budget. `WSC/SHAPE-BRIDGE.md` §10 enumerates three routes to coverage and offers
none; `ShapeBridge.M1Covers` is noted **false as stated**. §5.2 above shows this is
not pedantry: P2b is *provable* at SHAPE S1 precisely because S1's one-policy /
one-token-name values evade the two counterexamples that make the general
statement fail on the source model. The honest framing of the whole shaped layer
is **bounded model checking beneath the axiomatic layer**, and STATUS.md now says
that in those words.

### F3 — HIGH. The shape bridge is proved, but nothing consumes it.

U1's result is real and I re-verified all 25 of its verdicts, including the 16
kernel-checked `exec`-level `rfl` bridges (axioms: `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`). But `WSC/Honest.lean`'s budget bridges and
`Composition.lean`'s `LeafSet` still name unshaped preps, so the bridge sits
unused. U1's own §8.3 recommendation — restate `LR_BUDGET_*` against
`ShapeBridge.XRun K` — is four axiom statements and no new proving, and it would
also delete `PropExecFaithful` (F8) from the trust base. **Highest-value next
action in the campaign.** Not done here: it is an axiom-base change and belongs to
`Honest.lean`'s owner with an audit row.

### F4 — MEDIUM, corrected here. "The top theorem is `sorry`-free" is false.

`WSC/status-fragments/V4.md` states that `top_claim` and
`no_programmable_tokens_outside_mini_ledger` are "`sorry`-free Lean theorems".
`#print axioms` says both depend on `sorryAx` (via `p3_lifted` → the
blaster-closed P3 theorem). The claim is corrected in the new STATUS.md; the
fragment is left as the historical record. Nothing about the mathematics changes —
the P3 verdict is ✅ Valid — but a reviewer who greps for `sorryAx` must not be
surprised.

### F5 — MEDIUM, measurement. `K-MEASUREMENTS.md` §5.1's prep table is wrong by ~49x, and it changed agents' behaviour.

`WSC/goldens/K-MEASUREMENTS.md` §5.1 publishes **2,143 s = 35.7 min** for
`programmableLogicGlobal` prepped at 1600. In this clean-room rebuild
`WSC.Prep.Global1600` elaborated in **44 s** (cold, `lake build`, log line
`[384/401]`). That is a **48.7x** overstatement. `STATUS.md` §0.2 already warned
the table is "15-53x pessimistic — read it for shape only, never for numbers", and
this confirms it with a hard number; the cause is the `lake env lean` /
`--load-dynlib` artifact plus the substrate bump. **It had a real cost:** task U2
explicitly declined to build `P1_Transfer`, `P5_NonMember` and the entire shaped
layer, citing "a 35.7-min `#prep_uplc`", and shipped edits validated against a
partial build. Fixed by measurement, not by editing K-MEASUREMENTS (not my file);
recorded in STATUS.md §0 and §5.

### F6 — MEDIUM. `set_option warn.sorry false` makes the build-log sorry census incomplete.

15 modules set it, hiding ~42 `admit`s. Any future "expected `sorry` whitelist =
N" claim (U1 reported 19) is a count of unsuppressed warnings only. The correct
instrument is `#print axioms` → `sorryAx`, which is now reproducible in one command
(`WSC/Shaped/Probe/U3Census.lean`). Not "fixed" by deleting the options — that
would bury 40+ expected warnings in every build — but it is now documented in two
places.

### F7 — LOW, one-liner available (not applied). `GlobalNonVacuous` is recorded open although it is proved.

`WSC/Honest.lean` records `GlobalNonVacuous appliedGlobal1600.prop` as
undischargeable; `ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600` proves exactly
it (✅ Valid, `ShapeBridge.lean:1436`, re-verified). The repair is one `:=` in a
`Honest.lean`/`Composition.lean` docstring plus a theorem. **Not applied: those two
files' hygiene is U2's unit and an `import WSC.ShapeBridge` in `Honest.lean` would
create a cycle** (`ShapeBridge` imports the shaped preps which import `Honest`).
The correct home is a downstream module, exactly as `P6Bridge.lean` is for P6.

### F8 — LOW but structural, pre-existing and unnamed until U1. `prop` vs `exec`.

Every leaf theorem hypothesises `isSuccessful (appliedX.prop …)`. Every K
measurement, every concrete accepting instance, every `native_decide` witness runs
`appliedX.exec`. `#prep_uplc` emits the two as separate terms
(`PreProcess.lean:43-46`) and `appliedBase.prop = appliedBase.exec` is **not**
definitional (`rfl` fails — `BridgeProbe2FAILS.lean`). So the non-vacuity witnesses
and the theorems technically speak about two different terms. U1 states this
honestly and refuses to axiomatize it, citing Blaster defect D6 as proof the
transformation is not unconditionally well-behaved. Mitigations already in place:
every vacuity probe is stated on `.prop`, so the accept classes are certified
non-empty on the term the theorems use. Discharge route: have `#prep_uplc` emit
`X.prop_eq_exec` from the per-rewrite lemmas Blaster already proves.

### F9 — LOW, fixed here. Stale docstrings inside `Composition.lean`'s `LeafSet`.

`LeafSet.p4`'s docstring said "arm 4 only is PROVED-SHAPED … Arms 1-3 need K ≥
1,257/1,681 and no shape has been written" — contradicted by V3 (which landed all
three) and by §10.3 of the same file. `LeafSet.p1`'s said the leaf is discharged
"MODEL+AXIOM … STILL-OPEN" with a reconciliation costing "`TS3` + `TS5`" —
contradicted by P1Shaped (UPLC, no faithfulness axiom) and by §7.1 of the same file
(`TS3` only; measured). Both corrected in place, comment-only, with the measured
axiom lists quoted.

### F10 — LOW, fixed here. `WSC.ShapeBridge` was not in the default build target.

`lake build WSC` did not check the shape bridge (U1 flagged it and did not own
`WSC.lean`). Added the import; measured cost 36 s and 25 of the 98 verdicts, both
included in §1's numbers.

### F11 — INFORMATIONAL. `WSC/Props/P5_Witness1600.lean` is `#eval`s, not theorems.

The "concrete non-vacuity witness at budget 1600 / budget-ERROR at 1553" that U2
cites as `WSC.Witness1600` consists of two `#eval outcome (cekExecuteProgram …)`
commands printing strings. That is evidence a human can read in a build log, not a
kernel-checked proposition, and `#print axioms` cannot be run on it. The
theorem-grade version exists elsewhere
(`P5ShapedWitness.exec_accepts_at_1600_unshaped`, `native_decide`, re-verified
here), so nothing rests on the `#eval`s — but they should not be cited as if they
were theorems.

### F12 — INFORMATIONAL, carried forward unchanged.

* Blaster defect **D6** (`#prep_uplc` emits kernel-ill-typed `Blaster.dite'` when a
  CIP-153 `Value` builtin result stays symbolic) still blocks SHAPES T3/T4, hence
  containment dispatch Paths B/C and input-side aggregation at UPLC.
  Reproductions: `Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`, both deliberately
  non-building and both **excluded from the build** — verified that nothing imports
  them.
* **Substrate is not reproducible off this machine**: `lakefile.lean` pins
  PlutusCoreBlaster by absolute local path to the unpushed branch
  `cip153-value-builtins` (ARCHITECTURE E11). Every "proved against production
  bytecode" claim for the global/seize validators inherits this.
* `LeafSet.p4`'s `LR5` claim (U2's finding): `WSC.LR5` does not entail
  `seizeCred ∈ txInfoWdrl` from `seizeScopedToNodeOf`; isolated as
  `SeizeWdrlOfScoped`, needs a strengthened `LR5` with a `Conway/TxInfo.hs`
  audit row.
* `ValueAlgebra` + `LedgerCanon` uninstantiated, so `LR_BALANCE_SLOT` is still an
  axiom even though `LR_BALANCE_SLOT_of_valueAlgebra` proves its exact statement
  from `LR7` plus those two residues.
* Minting budget bridge exists at 900 only; P4's Local/DT/DS arms cost K =
  1681/1257/1466 and need a bridge at 2500 with `WithinBudget`'s `K_mint` clause
  raised in step.

---

## 8. WHAT A REVIEWER SHOULD NOT BELIEVE

1. **Do not believe "the WSC containment property is proved."** It is reduced, in
   machine-checked form, to four leaf obligations (two with proved ingredients and
   an unproved residue, two open) plus 26 project axioms. The reduction is the
   deliverable.
2. **Do not believe any UPLC result is universally quantified over transactions.**
   Every one is bounded by a CEK step budget AND by a fixed `Data` skeleton. Quote
   both bounds or quote neither. There is no coverage theorem, and §5.2 exhibits a
   theorem that provably does not generalize past its shape.
3. **Do not believe "`sorry`-free".** 62 theorem-position results in this library
   are closed by `blaster`'s `admit`; their certification is the `✅ Valid` verdict
   of a Z3 run recorded in the build log, not a kernel check. `top_claim` inherits
   `sorryAx` through P3.
4. **Do not believe the prep-cost figures in `WSC/goldens/K-MEASUREMENTS.md`
   §5.1.** Off by up to ~49x on this substrate (F5). Measure before you conclude
   something is unaffordable.
5. **Do not believe the witnesses and the theorems are about the same term.**
   Theorems: `.prop`. Witnesses and all K numbers: `.exec`. Equality unproved
   (F8).
6. **Do not believe the source-model results and the shaped results are the same
   strength.** The model route (`globalModel_faithful`, `seizeModel_faithful`)
   quantifies over all contexts and all step counts but trusts a hand
   transcription; the shaped route trusts no transcription but is doubly bounded.
   Neither dominates.
7. **Do not believe this builds anywhere else.** The substrate pin is an absolute
   local path to an unpushed branch.

## 9. REPRODUCTION

```
# 1. clean-room rebuild of everything (93.7 s, 401 jobs, 98 ✅ markers)
cp -a <CLAB> <SCRATCH>/clab-audit && cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge

# 2. the axiom census of §3 (2.7 s warm)
lake build WSC.Shaped.Probe.U3Census

# 3. marker + sorry census from the log of step 1
grep -o 'WSC/[^ ]*: ✅ [A-Za-z ]*'                  <log>   # expect 98, all ✅
grep -c "declaration uses 'sorry'"                  <log>   # expect 21 (§2)
grep -c '^error:'                                   <log>   # expect 0
```
