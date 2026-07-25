# WSC containment campaign — FINAL AUDIT (task E5, the seal)

**What this file is.** The authoritative statement of what is and is not
established, and the last technical gate before the campaign is quoted outside this
repository. Nothing below is taken on any earlier agent's word — including the four
stage-11 agents (E1, E2, E3, E4) whose work this audit gates. Every number was
re-measured here, in three independent clean-room rebuilds on 2026-07-25; every
claim that could not be reproduced is corrected in place and listed in §8.

**This revision SUPERSEDES the C4 audit**, which superseded A3, which superseded U3.
Their bodies are folded in finding by finding; the originals remain in `git log`
(`300f9e0`, `416087d`). Where this audit disagrees with C4 the disagreement is
stated, not patched over.

Audited revision: branch `wsc-containment-proofs`, the E5 commit on top of
`8163803`, tree clean.
Environment: 32-core box, Lean 4.24.0, Z3 4.15.2, `maxHeartbeats 0`,
Blaster git `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce` (branch
`beta-lambda-cache-optimization`, pinned by rev in `lake-manifest.json`),
PlutusCoreBlaster by local path at rev `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`
(branch `cip153-value-builtins`, unpushed — see §6.2).

**THE HEADLINE CHANGES SINCE C4.**

1. **Audit F1's obligation gap is closed: N = 0.** There is now a `LeafSet` with
   **no** remaining leaf hypothesis, over a class that is not empty — and a **second**
   one for the seize purpose. But the number that matters is not N; it is the
   **ratio**, and it is measured in §3.4: *on each side, one of four leaves is the
   production bytecode and three are the shape.*
2. **The most damning practical caveat, D5, is materially repaired.** The substrate
   is now pinned by revision in three places and carries an offline `git bundle`
   that this audit independently applied and byte-compared. It is not fully closed —
   the branch is still unpublished.
3. **Shape coverage is now stated in Lean, and it is PROVED FALSE** at the smallest
   bound the family already covers, with three node-realizable transactions the real
   bytecode accepts in exactly the certified witness's 2,603 steps.
4. **One stage-11 unit delivered nothing at all** (§7.2, finding **F20**), so F17,
   F18 and F19 were all still open when this audit began. F17 is now **measured and
   answered** here, though not landed as a theorem. **F18 is RESOLVED by task G2** —
   see §8: the faithful rule is not expressible in `TxInfo`, so the predicates are
   renamed `…AllPlutus`, the direction of the error is now a pair of theorems rather
   than a comment, and every negative use is audited individually (6 unaffected,
   6 downgraded with the side condition in the type, 1 measurement re-read).

---

## 0. THE ONE-PARAGRAPH ANSWER

The library is internally consistent and its measurements reproduce: **431 jobs,
1 m 39 s – 1 m 57 s over three runs, 159 solver verdicts all ✅, zero errors, zero
unexplained `sorry`s**, source reconciliation exact, and the leaf theorems say what
they claim to say in ground-truth vocabulary. Six safety properties of the four
production validators are genuinely proved against the **real compiled bytecode**,
whose provenance this audit re-verified end to end (4/4, §6.1). Three things changed
since C4 and they are the only reasons to re-read this file:

1. **Both composed results now have complete `LeafSet`s — and the honest measure is
   the ratio, not the count.** `RealizableLeaves.containment_on_realizable_class`
   (transfer, over `T1RShapeNS`) discharges `p1` from the production
   `programmableLogicGlobal` bytecode with its acceptance hypothesis **consumed**,
   and discharges `p2`, `p4`, `nopre` **from the shape**, with their acceptance
   hypotheses **unused and bound as `_`**.
   `RealizableLeaves.containment_on_seize_class` (seize, over `S1RShape`) is the
   mirror image: `p2` is the production `programmableSeize` bytecode with its
   acceptance hypothesis consumed, and the other three are the shape. **One of four
   leaves is the code, on each side.** Closing `p2` on the transfer side cost
   **nothing** in trust base — the axiom sets are set-equal, measured in §3.1.
2. **The coverage question has an answer, and it is "no".** `WSC/Coverage.lean`
   states coverage in Lean and refutes it for the twelve re-cut shapes at
   `SizeBound 2 2 2 2 0` — SHAPE T1R's own size — with three counterexamples that
   are ledger-valid, Conway-redeemer-exact, accepted by the real CEK, and cost
   **exactly 2,603 steps**, byte-identical to the certified inhabitant. The machine
   cannot tell them apart from a covered transaction; only the skeleton can. No
   project axiom, no `sorryAx`.
3. **Reproducibility moved from "one machine" to "one machine plus a verified
   artifact"** (§6.2).

The top-level sentence *"in an honest deployment, programmable tokens cannot exist
outside the mini-ledger"* is still **not proved**, and the reasons are now sharper
rather than merely structural: there is no shape-coverage argument **and coverage is
now known to be false for this family**, every bytecode result is still bounded twice
(a CEK step budget AND a fixed `Data` skeleton), and 28 project axioms plus `sorryAx`
still stand under both composed results. The deliverable is: six real, controlled,
non-vacuous properties of the production bytecode over named bounded families that
are node-realizable; a machine-checked reduction of the top claim to four leaf
obligations plus 28 axioms; that reduction discharged **completely** over two
realizable classes, with one quarter of the work done by the code on each; and a
machine-checked refutation of the coverage step that would connect the two. Not the
claim.

---

## 1. CLEAN-ROOM REBUILD

### 1.1 Method

```
cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-E5
cd <SCRATCH>/clab-E5
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
Confirmed by the log: **93 distinct `WSC.*` modules re-elaborated**, including all
shaped/unshaped `#prep_uplc` modules, all 4 `#import_uplc` sites, and all 159 solver
invocations.

**Run 3 was executed after this task's own changes were applied** (§6.2), to confirm
they are inert with respect to the build. They are.

### 1.2 Result, against the audited baselines

| measurement | A3 (`80cdac7`) | C4 (`300f9e0`) | **E5 (this audit)** |
|---|---|---|---|
| exit status | 0 — 405 jobs | 0 — 429 jobs | **0 — `Build completed successfully (431 jobs)`** |
| wall clock | 1 m 38.50 s | 1 m 30.22 / 1 m 42.57 s | **1 m 39.29 s / 1 m 46.56 s / 1 m 57.07 s** (three runs — **quote the range 1:39–1:57**, never a point) |
| user + sys CPU | 275.9 + 33.6 s | 380.4 + 56.6 s | **402.7–434.9 s + 50.3–54.0 s** (417–456 %) |
| max RSS | 1.65 GB | 1.65 GB | **1.50–1.52 GB** |
| WSC modules re-elaborated | 67 | 90 | **93** |
| `error:` lines | 0 | 0 | **0** (hard requirement — met, all three runs) |
| solver verdicts | 101: 66 V + 35 F | 158: 101 V + 57 F | **159: 102 `✅ Valid` + 57 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` | 0 | 0 | **0** (all three runs) |
| `declaration uses 'sorry'` | 20 | 20 | **20** (census §2) |
| `unused variable` | 5 | 5 | **5** — all at `Composition.lean:2442-2446` (§5.4) |

Note the RSS change is a **reduction** (1.65 → 1.50 GB) and the median wall clock is
up ~10 s; both are consistent with +2 modules of ordinary Lean and no new solver load.

### 1.3 The verdict delta reconciles exactly

`158 → 159` is `+1`, and it is accounted for:

* **E1** (`ad0e2e9`): **+1 module, +1 verdict** — `bridge_S1R`, 1 `✅ Valid` at
  `RealizableLeavesS1R.lean:166`. Everything else E1 added in both modules is
  ordinary Lean, `rfl`, or `native_decide`. Verified by differencing the per-file
  marker table: `RealizableLeaves.lean` still contributes exactly 1.
* **E4** (`4919968`, `8163803`): **+1 module, +0 verdicts** — `WSC/Coverage.lean`
  runs no solver at all. Verified: it appears nowhere in the marker table.
* **E2**: **+0 / +0** — it produced nothing (§7.2).
* **E5** (this task): **+0 / +0** — documentation and the substrate artifact only.

`101 + 1 = 102` ✅ Valid and `57 + 0 = 57` ✅ Expected Falsified.

Per-file marker table, complete (regenerable from the log):

| file | ✅ Valid | ✅ Expected Falsified |
|---|---|---|
| `WSC/ShapeBridge.lean` | 19 | 6 |
| `WSC/Props/Shaped/P4DelegateShaped.lean` | 7 | 4 |
| `WSC/Props/Shaped/P4DelegateShapedR.lean` | 7 | 4 |
| `WSC/Props/Shaped/P4LocalShaped.lean` | 7 | 3 |
| `WSC/Props/Shaped/P4LocalShapedR.lean` | 6 | 2 |
| `WSC/Props/Shaped/P1Shaped.lean` | 5 | 5 |
| `WSC/Props/Shaped/P1ShapedR.lean` | 5 | 5 |
| `WSC/Props/Shaped/P2Shaped.lean` | 5 | 3 |
| `WSC/Props/Shaped/P2ShapedR.lean` | 5 | 3 |
| `WSC/Props/Shaped/P4Shaped.lean` | 4 | 2 |
| `WSC/Props/Shaped/P4ShapedR.lean` | 4 | 2 |
| `WSC/Props/Shaped/P4ShapedIdx.lean` | 3 | 2 |
| `WSC/Props/Shaped/P4ShapedRIdx.lean` | 3 | 2 |
| `WSC/Props/P3_Base.lean` | 3 | 2 |
| `WSC/Props/P3_BaseRun.lean` | 3 | 1 |
| `WSC/Props/Shaped/P5Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P5ShapedR.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6ShapedR.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Unshaped.lean` | 1 | 1 |
| `WSC/Goldens/Witnesses.lean` | 1 | — |
| `WSC/Prep/Global.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/P4_Minting.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/Shaped/RealizableLeaves.lean` | 1 | — |
| **`WSC/Props/Shaped/RealizableLeavesS1R.lean`** | **1** | — |
| `WSC/Coverage.lean` | **0** | **0** |
| **total** | **102** | **57** |

### 1.4 Source reconciliation — the check that rules out a skipped stanza

Counted over the 93 built modules, with block comments and docstrings stripped first
(A3 did not strip them, which is why its tactic count needed a manual correction):

* **57** active (column-0) `#blaster … (solve-result: 1)` stanzas = "expect
  Falsified" → **57 × `✅ Expected Falsified`**.
* **2** active `#blaster … (solve-result: 0)` stanzas = "expect Valid, i.e. expect
  VACUOUS" (`WSC/Prep/Global.lean:83` `global_vacuity_probe_600`;
  `WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous`) → **2 × `✅ Valid`**.
* **100** `blaster` tactic invocations in theorem position → **100 × `✅ Valid`**.
  (95 written `:= by blaster` on one line; **5** written `:= by` with `blaster`
  indented on the next line — `P3_BaseRun.lean:93,112,141`,
  `Goldens/Witnesses.lean:152`, `P3_Base.lean:210`. A naive one-line grep misses
  those five and lands on 154 instead of 159; recorded so the next auditor does not
  chase the discrepancy.)
* 57 + 2 + 100 = **159**, and the per-file split matches §1.2's table one-for-one.
  **No stanza is unaccounted for and none is skipped.**

### 1.5 Slowest cold modules

`WSC.Prep.Global1600` ≈ 42 s in-parallel, `WSC.ShapeBridge` ≈ 38 s,
`WSC.Shaped.MintingLocalShapedIdx` ≈ 30 s, `WSC.Props.Shaped.P2Shaped` ≈ 25 s,
`WSC.Props.Shaped.P2ShapedR` ≈ 24 s, **`WSC.Props.Shaped.RealizableLeavesS1R` 20 s**
(new; its `native_decide` seize witnesses dominate), `WSC.Composition` 5.4 s,
`WSC.Props.Shaped.RealizableLeaves` 2.6 s, **`WSC.Coverage` 1.7–2.2 s**. Everything
else ≤ 7 s.

---

## 2. SORRY / ADMIT CENSUS

20 `declaration uses 'sorry'` warnings, classified — locations re-extracted from the
log, not carried over:

| class | count | detail |
|---|---|---|
| **(a)** blaster `admit` on a declaration that reported ✅ Valid | **19** | all in `WSC/ShapeBridge.lean` |
| **(b)** PCB pre-existing, not WSC code | **1** | `PlutusCore/UPLC/CekMachine.lean:299:4` — unchanged |
| **(c)** anything else = DEFECT | **0** | — |

**The warning count is NOT a census and must never be quoted as one (§8 F4).**
`grep -rl 'set_option warn.sorry false' WSC/` returns **38** modules (C4: 37; E1's
`RealizableLeavesS1R` is the +1 — `WSC/Coverage.lean` deliberately does **not**
suppress and emits zero warnings), so the ~100 further `admit`-closed theorems in
them emit no warning at all. The authoritative instrument is `#print axioms` →
`sorryAx` (§3), and by that instrument **every one of the 100 `by blaster` theorems
in the library is admit-closed.**

Literal-source grep over `WSC/**/*.lean`, comments stripped:

* **no** literal `sorry`, `admit` or `stop` in tactic position anywhere. The
  remaining textual hits are prose inside docstrings. Verified at this revision.
* **51** `axiom` declarations: `WSC/Honest.lean` (**38**), `WSC/Composition.lean`
  (**10**), `WSC/Props/P1_Transfer.lean` (**2**), `WSC/Model/SeizeModel.lean` (**1**).
  **Unchanged by stage 11** — E1 and E4 added none.
* **Zero `axiom` declarations under `WSC/Prep/`, `WSC/Shaped/` or
  `WSC/Props/Shaped/`** — machine-verified at this revision, and this is the shaped
  layer's central claim: it adds no assumption. **It survives E1 and E4 intact**,
  including `RealizableLeavesS1R.lean`. (`WSC/Coverage.lean` is not under those
  directories; it declares no axiom either — verified.)

---

## 3. AXIOM CENSUS

The rebuild log carries **173** `#print axioms` results, all distinct names
(C4: 142). Of these, **37** carry `sorryAx`, **72** use `native_decide`, and **124**
carry **zero project axioms**.

> **Parsing trap, recorded because it cost this audit time.** `#print axioms` output
> **wraps across log lines**. A line-oriented `grep 'depends on axioms' | grep -c
> sorryAx` returns **17**, not 37 — it only sees names whose axiom list happens to
> fit on the first line. Parse for `'NAME' depends on axioms: [` … `]` across
> newlines. C4's published "27 with `sorryAx`" was produced by the line-oriented
> method and is **corrected here**.

Legend: **(i)** Lean-standard `propext`/`Classical.choice`/`Quot.sound`;
**(ii)** `native_decide` = `Lean.ofReduceBool` + `Lean.trustCompiler`;
**(iii)** `sorryAx` = blaster's `admit`; **(iv)** project axioms, counted.

### 3.1 The number a reviewer needs

There are now **three** strongest-available claims and they are not comparable, so
all three are quoted:

**(a) `Composition.containment_on_contained_class` — 26 project axioms.** Over the
`ContainedTx` accounting class. Uses **no UPLC result**; its acceptance hypotheses
are provably unused.

**(b) `RealizableLeaves.containment_on_realizable_class` — 28 project axioms, no
leaf hypothesis.** Over `T1RShapeNS`, a non-empty shape class. Uses the production
`programmableLogicGlobal` bytecode for `p1`, **consuming the acceptance
hypothesis**. The 28 are the same 26 **plus exactly two**:

* `WSC.LR_BUDGET_global` — the ledger↔meter bridge at `K_global = 4400`, whose
  non-vacuity hypothesis is *discharged*, not assumed
  (`NonVacuity.globalNonVacuous_at_4400`, `native_decide` on the real CEK);
* `WSC.TS3` — reached through `Composition.coveringIn_of_coveringRaw`, the
  raw↔ground-truth reconciliation of the directory exemption predicate.

**(c) `RealizableLeaves.containment_on_seize_class` — 28 project axioms, no leaf
hypothesis.** Over `S1RShape`. Uses the production `programmableSeize` bytecode for
`p2`, **consuming the acceptance hypothesis**. Its 28 are the same 26 plus
`WSC.LR_BUDGET_seize` and `WSC.nodeStepsSeize`. `TS3` disappears because `p1` no
longer needs the raw↔ground-truth covering reconciliation.

Measured set differences (from the parsed log, not from any report):

```
axioms(containment_on_realizable_class) Δ axioms(containment_on_realizable_class_of_p2)  =  ∅
axioms(containment_on_realizable_class) ∖ axioms(containment_on_contained_class)
      =  {WSC.LR_BUDGET_global, WSC.TS3}                       (∅ in the other direction)
axioms(containment_on_seize_class)      ∖ axioms(containment_on_contained_class)
      =  {WSC.LR_BUDGET_seize, WSC.nodeStepsSeize}             (∅ in the other direction)
axioms(containment_on_seize_class)      Δ axioms(containment_on_realizable_class)
      =  {LR_BUDGET_seize, nodeStepsSeize}  vs  {LR_BUDGET_global, TS3}
```

**Two facts a reviewer should take from this.** First, the two-axiom delta is the
price of making the bytecode load-bearing, and it is the single most informative
number in this audit: result (a) is cheaper in axioms and says nothing about the
validators; results (b) and (c) each cost two more and each say something about one
validator. Second — new in stage 11 — **closing `p2` cost nothing at all**: the
axiom set of the hypothesis-free (b) is *set-equal* to that of the C4 result that
assumed `p2`. The obligation was removed by a class restriction, not bought with a
new assumption. That is the honest reading, and §3.4 gives the honest price.

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

**Read 26/28 as a floor, not a ceiling.** The library declares 51; the 21 that no
top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_minting`, `DIRWF`, `TS1`–`TS5`
(less `TS3`), `TS_MINTING_IDENTITY`, `LR_REDEEMER_COVERAGE`, and the two `*_faithful`
axioms — are what a *fuller* bytecode discharge of the leaves would add.

### 3.2 Per-theorem table (project-axiom count; flags)

| theorem | (i) | (ii) | (iii) | (iv) |
|---|---|---|---|---|
| **`RealizableLeaves.containment_on_realizable_class`** | ✓ | ✓ | ✓ | **28** (§3.1b), **no leaf hypothesis** |
| **`RealizableLeaves.no_tokens_outside_mini_ledger_on_realizable_class`** | ✓ | ✓ | ✓ | **28** (identical set) |
| **`RealizableLeaves.containment_on_seize_class`** | ✓ | ✓ | ✓ | **28** (§3.1c), **no leaf hypothesis** |
| **`RealizableLeaves.no_tokens_outside_mini_ledger_on_seize_class`** | ✓ | ✓ | ✓ | **28** (identical set) |
| `RealizableLeaves.containment_on_realizable_class_of_p2` (C4, retained) | ✓ | ✓ | ✓ | 28 + one open `p2` |
| **`RealizableLeaves.realizableLeavesNS`** | ✓ | ✓ | ✓ | **12** — `Deployed`, `LR_BUDGET_global`, `LR_CTX`, `NodeAccepts{Global,Minting,Seize}`, `OnChain`, `TS3`, `nodeSteps{Base,Global,Minting}`, `LedgerStep` |
| **`RealizableLeaves.realizableLeavesS1R`** | ✓ | ✓ | ✓ | **13** — the above with `{LR_BUDGET_seize, NONNEG, nodeStepsSeize}` for `{LR_BUDGET_global, TS3}` |
| **`RealizableLeaves.p2_of_noSeizeWdrl`** (closed leaf, transfer side) | ✓ | **—** | **—** | **7** — and **no `sorryAx`, no `native_decide`**: no bytecode result is reachable from it |
| **`RealizableLeaves.p1_of_noGlobalWdrl`** (closed leaf, seize side) | ✓ | **—** | **—** | **7** — likewise |
| **`RealizableLeaves.p2_on_S1RShape`** (bytecode leaf, seize side) | ✓ | ✓ | ✓ | **10** — `Deployed`, `LR_BUDGET_seize`, `LR_CTX`, `NONNEG`, `NodeAcceptsSeize`, `OnChain`, `nodeSteps{Base,Global,Minting,Seize}` |
| **`RealizableLeaves.shapedGlobalContainment_T1RNS`** (bytecode leaf, transfer side) | ✓ | ✓ | ✓ | **7** — `LR_BUDGET_global`, `LR_CTX`, `NodeAcceptsGlobal`, `OnChain`, `nodeSteps{Base,Global,Minting}` |
| `RealizableLeaves.p4_on_T1RShape` / `nopre_on_T1RShape` | ✓ | — | **—** | 6 each (field signature only; **no bytecode**) |
| `RealizableLeaves.p4_on_S1RShape` / `nopre_on_S1RShape` | ✓ | — | **—** | 7 each (likewise) |
| **`RealizableLeaves.exec_T1R`, `exec_S1R`** | ✓ | — | **—** | **0 — kernel-checked `rfl`** |
| **`RealizableLeaves.bridge_T1R`, `bridge_S1R`** | ✓ | — | ✓ | **0** |
| **`RealizableLeaves.realizable_inhabitant`, `_NS`, `_S1R`** | ✓ | ✓ | **—** | **0 — the classes are non-empty and node-realizable, on no assumption** |
| **`RealizableLeaves.inhabitant_accepted_by_bytecode`** | ✓ | ✓ | **—** | **0** |
| `RealizableLeaves.witness_noSeizeWdrl`, `t1RShapeNS_witness`, `s1RShape_witness` | ✓ | — | — | **"does not depend on any axioms"** |
| **`Coverage.not_covers_at_T1R_size`, `_size'`, `_with_three_reference_inputs`** | ✓ | ✓ | **—** | **0 — no project axiom, no `sorryAx`** |
| **`Coverage.missed_transactions_are_realizable_and_accepted`, `_cost_exactly_2603_steps`** | ✓ | ✓ | **—** | **0** |
| `Coverage.family_invariants`, `ctxOk_in_family`, `wdrl_range_char`, `unshaped_covers` | ✓ | — | — | **0** |
| `Coverage.skeletons_at_{T1R,M1R,minimal_transfer}_size` | — | ✓ | — | **0** |
| `Coverage.p3_lives_over_a_covering_class` | ✓ | — | ✓ | 0 (inherits P3's blaster `admit` — expected, and stated in the module) |
| `Composition.containment_on_contained_class` / `no_escape_on_contained_class` / `top_claim` | ✓ | ✓ | ✓ | **26** |
| `Composition.containedLeaves` | ✓ | **—** | **—** | **11**. **No `sorryAx`, no `native_decide`, no `blaster` verdict** — exactly how you can tell no bytecode result is used |
| `Composition.preservation` | ✓ | ✓ | ✓ | 22 |
| `P1R_T1/T2/T6/T7`, `P5R_shaped_indexed/_exists`, `P6R_*`, `P4*_R*`, `P2a_R_*`, `P2b_R_containment` | ✓ | — | ✓ | **0** |
| `P5R_shaped_groundtruth` | ✓ | — | ✓ | 3 — `Deployed`, `OnChain`, `TS3` |
| the 12 `*_class_coverage` and 12 `*_realizable` theorems | ✓ | ✓/— | **—** | **0** |
| `ShapeRealizability.t1_class_is_empty` | ✓ | — | **—** | **5** |
| `NonVacuity.*`, all concrete CEK witnesses (`K_T1R_is_2603`, `K_is_784`, …) | ✓ | ✓ | **—** | **0** |

### 3.3 Four properties of the list a reviewer should notice

1. **Every top-level theorem carries `sorryAx`.** All of them reach `p3_lifted`,
   which reaches the blaster-closed run-form P3; the shaped ones additionally reach
   `P1R_T1`/`bridge_T1R` or `P2b_R_containment`/`bridge_S1R`. The kernel did **not**
   check them; their status is "checked modulo a `✅ Valid` Z3 verdict recorded in the
   build log". The sentence "the top theorem is `sorry`-free" is **false as stated**.
2. **A P1 result and now a P2 result both appear in top-level dependency graphs.**
   In `containment_on_contained_class` no P1/P2/P4/P5/P6 result appears anywhere; in
   `containment_on_realizable_class`, `P1R_T1` and `bridge_T1R` are reached; in
   `containment_on_seize_class`, `P2b_R_containment` and `bridge_S1R` are. That is
   why those two carry `sorryAx` **through a shaped leaf** and why
   `NodeAcceptsGlobal` / `NodeAcceptsSeize` are not merely mentioned in a field type
   but consumed.
3. **Three of seven published budget instantiations are now exercised** —
   `LR_BUDGET_base` at 600 (`p3_lifted`), `LR_BUDGET_global` at 4400
   (`shapedGlobalContainment_T1R`), and — **new in stage 11** — `LR_BUDGET_seize` at
   3800 (`p2_on_S1RShape`). `LR_BUDGET_minting` is still applied by nothing (§8 F15).
4. **Lean's `unused variable` linter is still the honest instrument it was in A3.**
   Five warnings, all at `Composition.lean:2442-2446` — A2's inline `LeafSet` — and
   **none** in `RealizableLeaves.lean`, `RealizableLeavesS1R.lean` or `Coverage.lean`,
   because the bytecode leaves really do use their acceptance hypotheses and the
   shape leaves bind theirs as `_` deliberately (§5.4).

### 3.4 THE RATIO — the honest measure, and why "N = 0" must never be quoted alone

C4 reported an **N = 1** obligation gap and asked whether closing it would make the
bytecode do more work. **It does not, and the artifact says so itself.** Verified
here by reading the proof terms and by the axiom flags in §3.2, not from any report:

| composed result | class | `p1` | `p2` | `p4` | `nopre` | leaf hypotheses |
|---|---|---|---|---|---|---|
| `containment_on_realizable_class` | `T1RShapeNS` (transfer) | **BYTECODE** — `WSC.P1R_T1`, `programmableLogicGlobal` @ 4400, acceptance hyp. **used** | SHAPE + ledger rule | SHAPE | SHAPE | **0** |
| `containment_on_seize_class` | `S1RShape` (seize) | SHAPE + ledger rule | **BYTECODE** — `WSC.P2b_R_containment`, `programmableSeize` @ 3800, acceptance hyp. **used** | SHAPE | SHAPE | **0** |

**One of four leaves is the bytecode on each side; three of four are the shape.**

The mechanism on the shape side is a real ledger argument, not hand-waving, and it is
the only genuinely new proof technique in stage 11:
`NoSeizeWdrl hp ctx := credentialInWithdrawals hp.seizeLogicCred …txInfoWdrl = false`
makes the `p2` leaf's *hypotheses contradictory* via `validScriptInfo`'s
`RewardingScript` clause (`CardanoLedgerApi/V3/Contexts.lean:1014`, transcribing
Conway rewarding `scriptsNeeded`, `Alonzo/UTxO.hs:375-384`): a rewarding script runs
only for a credential the transaction actually withdraws at. `WSC.NodeAcceptsSeize`
is bound as `_hacc`, and `p2_of_noSeizeWdrl` carries **no `sorryAx` and no
`native_decide`** — machine-checkable evidence that no seize-validator result is
reachable from it. The seize side is the mirror image with `NoGlobalWdrl`.

**What this means, stated so it cannot be softened.** Removing the last leaf
hypothesis did **not** make the composition say more about the validators. It made
explicit that in a pure-transfer class three of the four obligations are about things
the class does not do, and that on the seize side the load-bearing leaf is the other
one. **Quote the ratio, never just "N = 0".** Both module docstrings say this, and so
does `WSC.lean`'s stanza — checked.

**Two further restrictions, recorded because E1 flagged them and this audit confirms
them.** (i) The `T1R` class is now strictly *smaller*: `containment_on_realizable_class`
excludes transfers whose second script withdrawal *is* the seize script. That
exclusion is the entire content of "discharged by the shape" — a class restriction,
not a proof about `programmableSeize`. (ii) `S1RShape` carries conjuncts
`T1RShapeNS` does not: `SeizeWithinBudget`, which is `Composition.WithinBudget`'s
deliberately-absent seize clause and is about the **opaque** `WSC.nodeStepsSeize`, so
unlike every other conjunct it **cannot be checked at the witness**; and
`mlCS = key` / `mCS = key`, which restrict to the **seized** policy because
`P2b_R_containment` is about that policy alone while `LeafSet.p2` demands containment
for *every* policy. Without those, on seize acceptance alone `p2` is **false** for a
positive mint of a *non-seized* policy sent off-base — nothing the seize validator
checks constrains another policy's mint; that is `p4`'s job. The S1R module states
all of this at §2, §3.3 and §5 rather than asserting inhabitation of the full class.

---

## 4. VACUITY RE-VERIFICATION

The highest-risk failure mode in the library, and the reason is on the record: task
V3 stated P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and only the mandatory probe
revealed the class was accept-**UNSAT** — the theorem was empty. Preserved as
`WSC/Shaped/Probe/G6Vacuous2500.lean`.

### 4.1 The pairing census, run mechanically over the whole built set

For every module in the built set, every prep/run term appearing in a theorem's
hypothesis was collected by identifier extraction and matched against every term
appearing in a `*vacuity*`/`*vacuous*` stanza. Result: **20 prep/run terms carry
accept-hypothesis theorems, and every one of the 20 has at least one probe at that
same term.** Unchanged by stage 11 — and that is the correct outcome, because:

* **E1 added no accept-hypothesis theorem over a prep term.** `bridge_S1R` is an iff
  between two executions and `exec_S1R` an equality (both over
  `appliedSeizeRShaped3800`, which already carries `P2_R_vacuity_probe`);
  `p2_on_S1RShape` hypothesises `WSC.NodeAcceptsSeize`, an abstract axiom, not a prep
  term. The correct vacuity question for the `RealizableLeaves*` modules is **class
  inhabitation**, and §4c answers it for both classes.
* **E4 added no accept-hypothesis theorem at all.** `WSC/Coverage.lean`'s acceptance
  results are *positive witnesses* (`Runs.globalRun 4400` accepts three named
  contexts), which need no probe — a probe certifies that an accept class is
  non-empty, and a witness *is* that certificate.

Five terms appear with theorems but no probe; each was re-inspected and **none is an
accept-hypothesis theorem**: `appliedGlobalShapedIdx1600`,
`appliedGlobalShapedNIdx1600` (bridges — equalities/iffs), `appliedMinting800` (a
positive witness), `appliedMinting1300`, `appliedSeize` (never used in a theorem).

### 4.2 The re-cut groups

**Every one of the 12 re-cut shapes has a vacuity probe stated at ITS OWN prep term
AND ITS OWN shape builder**, verified by extracting the `applied*` and `*Ctx`
identifiers from each theorem and each probe and comparing them mechanically rather
than by reading docstrings. All 12 rows (T1R, T2R, T6R, T7R, G1R, G6R, M1R, M2R, L1R,
DT1R, DS1R, S1R) report **Falsified** in this rebuild, unchanged from C4. **A probe
at the OLD term would have certified nothing about the new one.**

### 4b. THE RE-CUT ITSELF — unchanged from C4, re-verified

The Conway rule (`hasExactSetOfRedeemers`,
`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`, cardano-ledger
`cd8b7fab8`) computes `redeemersNeeded` from `scriptsNeeded` filtered to scripts that
are **provided** and **not native**, then requires the redeemer-map key set to equal
it exactly. C3's CLAB transcription is an **over-approximation** (it omits both
filters, because `TxInfo` records neither a script's language nor the witness set) —
this is finding **F18**, restated in §8 with stage 11's disposition.

The rule reproduces the real node on **13/13** goldens
(`#redeemers = #script-inputs + #mint-policies + #script-withdrawals` exactly, with
the purpose multiset matching), all 13 satisfy `redeemerCoverageAllPlutus`, all 9 accepting
goldens satisfy `redeemersExactAllPlutus`, and `all_old_witnesses_fail_c3_coverage` proves
`redeemerCoverageAllPlutus = false` at all 5 pre-C2 witnesses. **The flip is machine-checked
in both directions.**

### 4c. ARE THE CLASSES REALLY NON-EMPTY?

A3's §9 warned: *"Do not believe that instantiating the `Shape` parameter with a
shaped context class would fix that. It produces a true theorem about an EMPTY
class."* That warning was correct then and is why this section exists.

* `ShapeRealizability.t1_class_is_empty` proves the PRE-re-cut SHAPE T1 class empty
  **unconditionally**, and `t1_no_honest_step` proves no `Reachable.step` can fire.
  Both retained, as the picture of what failure looks like.
* **Transfer side.** `realizable_inhabitant_NS` proves, with **0 project axioms and
  no `sorryAx`**, that `P1RShapedWitness.ctxOk` is (i) a member of `T1RShapeNS
  witnessParams`, (ii) `validRewardingContext`, (iii) `redeemersExactAllPlutus`. The
  refinement did **not** empty the class: `witnessParams.seizeLogicCred = SEIZE ∉
  {GLOBAL, TLS}`, by `rfl`, no axioms (`witness_noSeizeWdrl`). The real compiled
  bytecode accepts it in **2,603** steps.
* **Seize side.** `s1RShape_witness` proves `P2RWitness.ctxAccept` satisfies
  `S1RCore ∧ NoGlobalWdrl` by `rfl` with **no axioms**; `realizable_inhabitant_S1R`
  adds `validRewardingContext` and Conway `redeemersExactAllPlutus`; and
  `inhabitant_accepted_by_bytecode` shows the restrictions do not empty the *accept*
  class — `isSuccessful (Runs.seizeRun 3800 ppCS ctxAccept)`, exact K = **3,004**,
  pinned two-sided by `K_is_3004_and_3328`. **0 project axioms, no `sorryAx`.**

**The honest limit, stated precisely, and it now has one extra clause.** None of this
proves that a `Reachable` trace in the new classes can take a step, and it cannot:
`HonestTx` also requires `WSC.OnChain ctx`, an opaque axiom, so **no term in this
library can prove any concrete context on-chain**. That is true of every witness in
the campaign. **Additionally, the seize class's third conjunct `SeizeWithinBudget`
is about the opaque `WSC.nodeStepsSeize` and therefore cannot be checked at the
witness at all** — so `S1RShape`'s inhabitation is certified for two of its three
conjuncts, and the module says so instead of quietly claiming the third. "Not
provably empty, with the known obstruction removed" is weaker than "provably
inhabited on-chain", and this audit will not let the two be confused.

---

## 5. ANTI-TAUTOLOGY SPOT-CHECK

The question in each case: **is the postcondition a fact about the transaction, or is
it "the validator's own accumulator came out true"?** Re-read line by line at this
revision.

### 5.1 P1 containment at the realizable cut — `WSC.P1R_T1`

Postcondition, verbatim: `Model.outSum (.ScriptCredential plc) cs tn …txInfoOutputs ≥
Model.inSum … …txInfoInputs + Model.mintSigned cs tn …txInfoMint`.

* `Model.outSum` / `inSum` (`WSC/Model/Ground.lean:43-56`) are independent structural
  recursions over the context's own output/input lists, guarded by
  `WSC.payCred o == base` and summing CLAB's `valueOf`. **No validator function
  appears in the postcondition** — the validator appears only in the hypothesis.
* `plc` is not a free choice: it is the same variable the shape puts in the
  params-UTxO datum the validator reads.
* The escape route is REAL and proved so: `P1RShapedWitness.ctxEscape_quantities`
  gives `outSum = 3 < inSum = 5`, and `exec_rejects_escape` shows the real CEK
  **rejects** that context with 4,400 steps available (a genuine rejection, not budget
  exhaustion).
* The accepting witness is pinned two-sided: `K_T1R_is_2603`.

**Verdict: ground truth. Not true by construction.**

### 5.2 P2b containment — `WSC.P2b_R_containment`

Postcondition is `P2.sumOutAtBase … ≥ P2.sumInAtBase … + WSC.mintOf …`, universally
quantified over `tn`, in independent recursions; nothing from the seize validator's
`valueDelta` / `ptokenPairsContain` machinery appears.

**Doubt, recorded, and it is now MORE important than it was, because this theorem is
load-bearing in a composed result for the first time.** This conjunct is
FALSE-in-general on the source model — obligation B1 has two machine-checked
counterexamples (`ptokenPairsContain` is unsound with duplicate token names or
unsorted maps) — and it closes here *because* SHAPE S1R gives every value exactly one
policy and one token name. **`containment_on_seize_class` therefore inherits that
shape-dependence directly.** The re-cut removed the realizability defect; it did NOT
remove the shape-dependence, and stage 11 did not either. This is the sharpest doubt
in the library and it is why §8 F2-coverage remains CRITICAL.

### 5.3 P4-Local no-escape — `WSC.P4_local_noEscape_R`

Postcondition `noEscape (.ScriptCredential plc) ownCS (localRCtx …outputs) = true`,
where `noEscape` scans the transaction's own output list. Both disjuncts are live
(distinct free variables). `L1RWitness.exec_rejects_escaping_output` is the
excluded-case witness through the real CEK over a redeemer-covered context.

**Verdict: ground truth. Not true by construction.**

### 5.4 The same check applied to the three `LeafSet` terms, and to the new leaves

| | `Composition.containedLeaves` (A2) | `realizableLeavesNS` (E1) | `realizableLeavesS1R` (E1) |
|---|---|---|---|
| class non-empty? | yes | **yes, certified** | **yes, 2 of 3 conjuncts certified** |
| bytecode used? | **no** | **yes — `p1`** | **yes — `p2`** |
| acceptance hyps consumed? | **none** (5 linter warnings) | **1 of 4** | **1 of 4** |
| project axioms | 11 | 12 | 13 |

**The new closed leaves are not tautologies, and the check is mechanical.**
`p2_of_noSeizeWdrl` and `p1_of_noGlobalWdrl` carry **no `sorryAx` and no
`native_decide`**, so no bytecode result is reachable from them; they are `exfalso`
arguments from CLAB's `validScriptInfo` and nothing else. The added conjuncts are
decidable facts about the **withdrawal map alone** — they say nothing about value
flow, outputs, or what any validator computes, so they cannot be used to prove
containment of anything. That is the difference between "discharged by the shape" and
"assumed".

### 5.5 The coverage refutation (new)

`Coverage.not_covers_of_invariant` is the whole argument and it is three lines: a
context that satisfies `Valid` and `Bound` but violates `ShapeInvariants` cannot be
in any family member, because `family_invariants` proves every member implies
`ShapeInvariants`. The risk is a **mis-transcribed** family — a `rangeXYZ` that is
not really the shape's range would make `¬ Covers` trivially true. E4 anticipated
this: `ctxOk_in_family` puts the certified inhabitant *inside* `rangeT1R`
(`[propext]`), so the family is demonstrably non-trivial. **This audit regards that
as the correct control and confirms it is present.**

The 12 `inv_*` proofs are `simp only [rangeXYZ, forall_exists_index]; intros;
subst_vars; exact ⟨…⟩` — computation at every leaf assignment, **no solver**. The
three counterexamples each change **exactly one** `Data`-skeleton feature of `ctxOk`
(signatory list length; reference-input list length; validity-interval constructor
tag), leaving every leaf scalar untouched. **None is repairable by adding a shape
parameter — two are list lengths and one is a constructor tag.**

---

## 6. PROVENANCE AND REPRODUCIBILITY

### 6.1 The bytecode chain — re-verified 4/4, independently

The four `.flat` files are byte-identical to the `cborHex` of the named unapplied
production scripts at wsc-poc commit `7ae0024b185cf16f17e38c20c9ee97ae1410c51f`.
Re-run by this audit against the wsc-poc worktree, not carried over:

```
1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3  programmableLogicBase
ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2  programmableLogicGlobal
289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1  programmableSeize
7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048  programmableTokenMinting
```

**4/4 MATCH on both sides.** This is the campaign's strongest single fact and it is
now verified at four separate audits.

### 6.2 D5 — the substrate pin, materially repaired

The `PlutusCore` (PlutusCoreBlaster, "PCB") dependency is required from an absolute
local path on an **unpushed** branch. C4 recorded this as *"nothing here is currently
reproducible off this machine"* — the highest operational risk in the repository.

Stage 11's E3 unit built the repair but **left it uncommitted in a scratch
directory** (§7.3). This audit verified it and landed it. What now exists:

| record | where |
|---|---|
| revision `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`, branch, base, clean-tree status, and the shallow-clone caveat | `lakefile.lean` comment block |
| `"rev"` / `"inputRev"` on the PlutusCore entry | `lake-manifest.json` |
| the two branch commits as an **incremental git bundle** + `git am` patches | `WSC/substrate/` |
| apply/verify recipe and what it does *not* fix | `WSC/substrate/README.md` |
| full third-party build recipe | `WSC/REPRODUCE.md` |

**Verified here, not asserted.** The bundle was applied from a clone of the public
base into a scratch directory and byte-compared against the build machine's checkout:

```
bundle sha256   3d34a23d5e25ac09beddcdf6032ecb3d13c47d064239b09be8040842d1a82789  (39,068 bytes)
git bundle verify … → "is okay"; requires a04042c…; contains refs/heads/cip153-value-builtins
HEAD after apply : 9f9ca8c76baf3b5efdb63c33ca0091efa606b474   (canonical: identical)
tree after apply : e75862b26b5055e8cc36ea8cf393054e2417ca62   (canonical: identical)
diff -r -x .git -x .lake <canonical PCB> <reconstructed>  →  CLEAN
```

And the manifest claim was tested rather than believed: `lake build` **preserves** the
`"rev"` / `"inputRev"` keys on a `"type": "path"` entry across a full clean-room
rebuild (sha256 of `lake-manifest.json` unchanged after run 3).

**What is still open.** The branch is **not published**, so the bundle's custody is
the trust anchor; the `require` is still an absolute path, so building elsewhere is a
mandatory two-file manual edit; and lake does not *verify* the recorded rev for a path
dependency (`lake update` would drop it). **D5 is downgraded from HIGH/OPEN to
MEDIUM/PARTIALLY REPAIRED, not closed.** The one-line fix that retires it is to push
the branch and restore a git pin.

---

## 7. VERIFICATION OF THE FOUR STAGE-11 UNITS

This section is the point of task E5. Each unit's central claim is checked against
its artifact, and every gap is reported.

### 7.1 E1 — discharge `p2`, close F1 → **CLAIMS HOLD, with one labelling error**

| E1 claim | verdict |
|---|---|
| `p2` is NOT vacuously dischargeable over `T1RShape`; SHAPE T1R's second withdrawal `w1` is free and `Deployed` is opaque | **CONFIRMED** — `GlobalShapedP1.lean:225-226` and `RealizableLeaves.lean:140` read as described |
| `p2_of_noSeizeWdrl` discharges the leaf by the ledger rule, acceptance hypothesis bound as `_` | **CONFIRMED** — proof read line by line; `_hacc`; no `sorryAx`, no `native_decide` |
| axiom set of `containment_on_realizable_class` Δ `…_of_p2` = ∅ | **CONFIRMED by measurement** (§3.1) |
| 28 = 26 + `LR_BUDGET_global` + `TS3`; seize side 28 = 26 + `LR_BUDGET_seize` + `nodeStepsSeize` | **CONFIRMED by measurement** |
| `LR_BUDGET_seize` applied for the first time; F15 goes 2/7 → 3/7 | **CONFIRMED** |
| +1 job, +1 verdict (`bridge_S1R`), marker delta exactly +1 Valid | **CONFIRMED** — per-file table §1.2 |
| zero `unused variable` warnings in either module | **CONFIRMED** — all 5 are `Composition.lean:2442-2446` |
| **the ratio is 1 bytecode / 3 shape on each side** | **CONFIRMED, and this audit adopts it as the headline measure** (§3.4) |

**The one gap: a namespace labelling error in E1's report.** Its S1R axiom table
names `WSC.RealizableLeavesS1R.*`. That namespace **does not exist**: the module
`WSC/Props/Shaped/RealizableLeavesS1R.lean` declares everything in
`WSC.RealizableLeaves`. Every identifier in this audit uses the real name. The
theorems themselves are exactly as reported; only the report's prefix was wrong.
Cosmetic, but it would waste a reviewer's `#print axioms`.

**Answer to the question E5 was told to ask.** *Is the leaf load-bearing, or is it
discharged by the shape's narrowness?* **The latter, and E1 says so itself.** Counted
both ways: leaf hypotheses 1 → 0; bytecode-discharged leaves 1 → 1. The composition
does not say more about the validators than it did at C4. What changed is that the
gap is now visible as a *class restriction* rather than as an *assumption* — a real
improvement in honesty, not in strength.

### 7.2 E2 — F17 / F18 / F19 → **NOTHING WAS DELIVERED. New finding F20.**

`git log` shows no E2 commit. Its scratch workspace sits at `300f9e0` with a
**completely clean working tree**: no modified file, no untracked file, no log.
**The unit produced no artifact of any kind.**

Consequently **F17, F18 and F19 were all still open**, exactly as C4 left them, and
none of the four bar items E5 was asked to check for an "L2R" exists — there is no
L2R, and SHAPE L2 was never re-cut. This audit therefore did the cheapest of the
three itself, by measurement rather than by adding a theorem (§7.5).

### 7.3 E3 — reproducibility → **WORK IS CORRECT AND VERIFIED, BUT WAS NEVER LANDED**

E3 produced no report and made no commit. Its scratch workspace held modified
`lakefile.lean` + `lake-manifest.json` and an untracked `WSC/substrate/`.

**Did the reproduction rehearsal actually run end to end, and do its numbers match?**
This audit re-ran it from scratch. **Yes on both counts** — bundle size, sha256, HEAD,
tree and a full `diff -r` all match E3's documented values exactly (§6.2). The
shallow-clone caveat E3 documented is real and correctly diagnosed. **E3's technical
work is sound.**

**Two gaps, one of them serious:**

1. **It was not landed.** Left in a scratch directory, it repaired nothing — the
   canonical repository still had D5 wide open at `8163803`. E5 has landed it.
2. **Two dangling cross-references.** E3's new `lakefile.lean` comment block directs
   the reader to `WSC/REPRODUCE.md` ("Full third-party recipe") and
   `WSC/substrate/README.md` ("bundle verify/apply"). **Neither file existed.** A
   reproducibility fix whose own instructions point at missing files is not a fix.
   E5 authored both, from its own re-measurement.

Also recorded: E3's `lakefile.lean` block claims the base `a04042c` is `refs/heads/main`
of the **public** `input-output-hk/PlutusCoreBlaster`. This audit confirmed `a04042c`
is the base of the local branch and is reachable as `main` in the local clone, but
**could not verify the public remote from this environment**. Treat "it is on the
public remote" as E3's claim, not as measured here; `WSC/substrate/README.md` §3 tells
the reader to check it with one `git rev-parse`.

### 7.4 E4 — shape coverage → **CLAIMS HOLD; IT IS A LEAN ARTIFACT, NOT PROSE**

| E4 claim | verdict |
|---|---|
| coverage is *stated in Lean* and refuted, not argued in prose | **CONFIRMED** — `WSC/Coverage.lean`, 840 lines; `Covers`, `SizeBound`, 12 `range*` defs, `not_covers_*` |
| the three refutations carry **no project axiom and no `sorryAx`** | **CONFIRMED by measurement** — `[propext, ofReduceBool, trustCompiler, Quot.sound]` |
| witnesses are ledger-valid + Conway-redeemer-exact, accepted at 4400, at exactly 2603 steps | **CONFIRMED** — theorems present and building |
| the transcription control `ctxOk_in_family` exists | **CONFIRMED** (§5.5) |
| `WSC/Coverage.lean` adds **zero** solver verdicts and zero warnings | **CONFIRMED** — absent from the marker table; not among the 38 `warn.sorry` suppressors |
| `p3_lives_over_a_covering_class` inherits `sorryAx` from P3 | **CONFIRMED, and E4 stated it** |
| skeleton arithmetic | **RE-CHECKED**: 995,328 × 3.3 s ≈ 38 CPU-days; 9,269,489,664 × 3.3 s ≈ 970 CPU-years; 3.05×10¹⁴ × 3.3 s ≈ 3.2×10⁷ CPU-years. E4's figures are right. |

**No gap found between claim and artifact.** E4's own limits are accurate and this
audit adopts them: "coverage is false" ≠ "coverage is impossible" (the impossibility
argument is **arithmetic only** and is not a theorem); realizability of the
counterexamples is **necessary, not sufficient**; and `SizeBound`'s choice of five
dimensions is a modelling decision, which is exactly where an overclaim would hide.

One process note: E4 appended an `import` stanza to `WSC.lean`, which it did not own,
and said so. That is the right disposition — without it the module would be outside
`lake build WSC` and invisible to this audit.

### 7.5 F17, measured here rather than left open

C4 called F17 "the cheapest open item" and E2 did not do it. This audit **measured
the answer** in a scratch module (deliberately not committed — E5 owns documents, not
Lean sources):

```lean
theorem m2r_exec_accepts_at_900 :
    isSuccessful (appliedMintRShapedIdx900.exec M1RWitness.ppCS M1RWitness.mlh
      "OWNCS" "TOK" (-3) "OWNER" 100 5 "DEST" 60 2 "MINTLOGIC" 0 "MLRED" 40 "" 0 0 1 "" 0) :=
  M1RWitness.isHaltB_sound _ (by native_decide)
```

* **It builds, and the real compiled `programmableTokenMinting` bytecode ACCEPTS the
  SHAPE-M2R witness on `.exec`.**
* `#print axioms` → `[propext, Classical.choice, Lean.ofReduceBool,
  Lean.trustCompiler, Quot.sound]` — **0 project axioms, no `sorryAx`**, the same
  shape as M1R's `exec_accepts_at_900`.
* **Exact K = 784**, measured by search over `isHaltB` at
  `mintingPolicyInputs900 … M2RWitness.ctx` — **byte-identical to SHAPE M1R's
  `K_is_784`**, as the "the re-cut cost zero CEK steps" result predicts (the
  withdrawal index lives in the redeemer *payload*, not in the map's keys).

**F17 is therefore answered but not landed.** Landing it is a two-theorem paste into
`WSC/Props/Shaped/P4ShapedRIdx.lean`'s `M2RWitness` namespace, after which M2R meets
4/4 bars and STATUS §2's only "3/4" row disappears. This audit leaves the paste to
whoever owns that file, with the measurement done.

---

## 8. FINDINGS, RANKED

### F2-coverage — CRITICAL, and now SHARPER: coverage is not merely absent, it is FALSE

No argument exists that the shapes exhaust the transactions the claim is about, and
stage 11 replaced that absence with a **machine-checked refutation**: at
`SizeBound 2 2 2 2 0` — SHAPE T1R's own size — three node-realizable transactions
that the production bytecode accepts in exactly 2,603 steps lie outside all twelve
re-cut shapes (`Coverage.not_covers_at_T1R_size`). Two differ from the certified
inhabitant by a **list length**, one by a **constructor tag**; none is repairable by
adding a shape parameter.

The arithmetic says the gap cannot be closed by enumeration: the smallest bound
admitting a real transfer (1 input, **2** reference inputs — the global validator
cannot run without its params reference input plus the directory node its redeemer
indexes — 1 output) already contains ≈9.27×10⁹ `Data` skeletons ≈ **971 CPU-years**
for one property at the measured 3.3 s/shape. **This is now the binding constraint on
the entire deliverable**, and `WSC/COVERAGE.md` recommends against a coverage
programme on exactly these numbers.

### F1 — CRITICAL → **NARROWED TO A RATIO, NOT CLOSED**

C4's N = 1 obligation gap is gone; two composed results now have complete `LeafSet`s.
But **one of four leaves is the bytecode on each side and three are the shape**
(§3.4), so the composition does not say more about the validators than it did. For
the general class nothing is proved. **The correct citation is the ratio; "N = 0" on
its own is misleading and this audit treats quoting it alone as an overclaim.**

### D6 — HIGH, OPEN. Blaster emits kernel-ill-typed `dite'` on symbolic CIP-153 `Value` results

Blocks SHAPES T3/T4, hence P1's containment dispatch Paths B/C and input-side
aggregation, which are unreachable at any shape. Needs an upstream fix. Unchanged by
stage 11.

### F8 — MEDIUM, OPEN, and now BINDING ON BOTH COMPOSED RESULTS

`PropExecFaithful` (`X.prop = X.exec`) is still unproved and deliberately not
axiomatized. Theorems are on `.prop`, witnesses and all measured K on `.exec`. It
binds all 12 re-cut groups and — since stage 11 — **both** composed results, through
`bridge_T1R` and `bridge_S1R`.

### F4 — MEDIUM, OPEN BY NATURE. "`sorry`-free" is false

**100** theorem-position results are closed by `blaster`'s `admit`; every top-level
theorem inherits `sorryAx`. And the build log's `sorry` warning count is **not** a
census — 38 modules suppress it.

### D5 — was HIGH → **MEDIUM, PARTIALLY REPAIRED** (§6.2)

Revision recorded in three places; offline bundle present and independently verified
to reconstruct the exact tree. Still: branch unpublished, path absolute, rev not
enforced by lake.

### F20 — MEDIUM, NEW. A stage-11 unit delivered nothing, and a second did not land its work

E2 produced no artifact at all (§7.2). E3 produced correct work and left it in a
scratch directory with two dangling cross-references (§7.3). **Process finding, but a
real one:** at `8163803`, the canonical repository's most damning practical caveat was
still fully open despite a unit having been assigned to it and having *solved* it.
E5 landed E3's work and wrote the two missing documents. **A campaign that measures
its own claims must also check that its units' claims reached the repository** — the
verdict counts, the axiom census and the marker table would all have looked perfectly
healthy while D5 stayed open, because none of them can see work that was never
committed.

### F17 — was MEDIUM → **ANSWERED BY MEASUREMENT, NOT YET LANDED** (§7.5)

SHAPE M2R's witness **is** accepted by the real bytecode, at exactly **K = 784**, with
0 project axioms. Two theorems remain to be pasted into `P4ShapedRIdx.lean`.

### F18 — **RESOLVED by task G2** (stage 11). Not expressible; renamed, bounded, and audited use by use

**Verdict on expressibility: NOT EXPRESSIBLE in PlutusV3 `TxInfo`, and now proved so
by construction.** The ledger's `redeemersNeeded` keeps a needed `(purpose, hash)`
pair only if `Map.lookup hash scriptsProvided` succeeds AND the script found there
satisfies `not (isNativeScript script)`
(`Alonzo/Rules/Utxow.hs:245-262`, `isNativeScript = isJust . getNativeScript`,
`cardano-ledger-core/src/Cardano/Ledger/Core.hs:586-587`). Of the two filters:

* the `scriptsProvided` filter is a **no-op** on any transaction that reaches the
  rule — `babbageMissingScripts` (`Babbage/Rules/Utxow.hs:191-206`, run at `:344`)
  already rejects unless every needed hash is provided, so the lookup always
  succeeds. Dropping it costs nothing;
* the `isNativeScript` filter is **not recoverable**. Every needed script HASH is
  derivable from `TxInfo`, but `isNativeScript` is a predicate on the script BODY,
  and `TxInfo` carries no script bodies and no language tags — its only
  script-shaped field is `TxOut.txOutReferenceScript : Option ScriptHash`
  (`CardanoLedgerApi/V2/Tx.lean:78-83`), a bare `ByteString`
  (`V1/Scripts.lean:15-16`); the witness script set has no `TxInfo` field at all.
  **The missing information is exactly one bit per needed script, and `TxInfo` does
  not contain it.**

**What G2 landed** (`CardanoLedgerApi/V3/Contexts.lean`,
`WSC/Props/Shaped/ShapeRealizability.lean` §2.2/§2.3, `WSC/Realizability.lean`,
`WSC/Honest.lean`, `WSC/Props/Shaped/GlobalRealizability.lean` §4):

1. **Renamed at every use site.** `redeemerCoverage` → `redeemerCoverageAllPlutus`,
   `noExtraRedeemers` → `noExtraRedeemersAllPlutus`, `redeemersExact` →
   `redeemersExactAllPlutus`, the `Prop` `RedeemerCoverage` →
   `RedeemerCoverageAllPlutus`, and the three consequence lemmas to
   `…_of_coverageAllPlutus`. `LR_REDEEMER_COVERAGE` keeps its name (renaming an
   axiom would renumber the census) but its statement now literally reads
   `redeemerCoverageAllPlutus` and its docstring carries the over-strength warning.
2. **The faithful rule is stated, modulo an oracle**, and the direction claims are
   now THEOREMS rather than commentary — all six at `[propext, Quot.sound]`, no
   project axioms, no `sorryAx`: `coveredByNonNative`, `redeemerCoverageModNative`,
   `noExtraRedeemersModNative`, with `redeemerCoverageModNative_allPlutus` (ours is
   the `fun _ => false` instance), `redeemerCoverageModNative_of_allPlutus` (**the
   positive direction: ours implies the true rule for EVERY language assignment**),
   `coveredByNonNative_strictly_weaker` and `noExtra_not_conservative` (**the two
   negative directions, by explicit counterexample**).
3. **Every negative use audited individually** — the table is
   `ShapeRealizability.lean` §2.3. Result: **6 of 13 unaffected** (all the
   SPENDING-route ones: `t1_class_is_empty`, `t1Shape_is_empty`,
   `t1_leafSet_is_vacuous`, `t2/t6/t7_class_is_empty` — they use
   `LR_SPEND_RUNS_VALIDATOR` + `validScriptInfo`'s first conjunct, never
   `scriptsNeeded`, and `Deployed` pins the script to a compiled Plutus V3
   validator); **6 downgraded** to an explicit non-native side condition
   (L1/DT1/M1 on `w0`, G1/S1/T1-withdrawal-route on `w1`, DS1 on both) because in
   every one of those shapes the witness credential is a FREE `ByteString`
   parameter that nothing pins to a Plutus script; **1 measurement**
   (`all_old_witnesses_fail_c3_coverage`) whose statement survives verbatim and
   whose *interpretation* as "unrealizable" is downgraded.
4. **The downgrade is in the types, not only the prose.** The six conditional
   emptiness theorems now take `RedeemerCoverageAt w` — coverage at the ONE
   credential the proof turns on — which is strictly weaker than before and has
   two visible suppliers: `RedeemerCoverageAt_of_allPlutus` (over-strong) and
   `RedeemerCoverageAt_of_true` (the true rule + `¬ isNative w`).
   `WSC.g6_class_is_empty`, the one negative result that was stated
   UNCONDITIONALLY via the axiom, is joined by `g6_class_is_empty_nonNative`,
   which carries `¬ isNative w1` explicitly and whose census is
   `[propext, Classical.choice, Quot.sound, WSC.OnChain]` — **no
   `LR_REDEEMER_COVERAGE`.**

**Residual risk: LOW, and now bounded.** Nothing positive changes — no
realizability inhabitant, no leaf, and neither composed containment theorem
consumes any `*_under_coverage` theorem or `g6_class_is_empty`. What is weaker is
the JUSTIFICATION for retiring the pre-C2 shapes: "empty" becomes "empty unless
the uncovered withdrawal is witnessed by a native timelock". **This weakens the
library's self-criticism, never its claims.** "Unconditional" in the surviving
docstrings now means what it says only for the six spending-route results.

Verified green at 431 jobs, **159 verdicts (102 ✅ Valid + 57 ✅ Expected
Falsified), 0 errors, 20 sorry warnings, 5 unused-variable — delta 0 against the
sealed baseline**, since G2 added no `blaster`/`solve` invocation.

### F19 — LOW, OPEN. SHAPE L2 was never re-cut

`P4_local_noEscape_shapedIdx` still ranges over SHAPE L2, whose class is **proved
empty** under `RedeemerCoverageAllPlutus`. C2 marked it as such rather than passing over it.
Its value was the index-dependence measurement, which the withdrawal map does not
affect — so the loss is small, but the library contains one headline-adjacent theorem
over a class known to be empty, and **it must not be quoted.**

### F15 — INFORMATIONAL. Budget instantiations: 3 of 7 exercised

`LR_BUDGET_base` @600, `LR_BUDGET_global` @4400, and now `LR_BUDGET_seize` @3800.
`LR_BUDGET_minting` is applied by nothing.

### F5, F7, F13, F14, F16 — CLOSED, unchanged since C4.

---

## 9. WHAT A REVIEWER SHOULD NOT BELIEVE

1. **Do not believe "the WSC containment property is proved."** It is (a)
   machine-checked as a *reduction* to four leaf obligations plus 26–28 project
   axioms, (b) discharged outright over one inert accounting class, and (c)
   discharged **completely** over two **node-realizable shape classes** — in each of
   which **the code does one quarter of the work and the shape does three quarters**.
   None of the three is the claim.
2. **Do not quote "N = 0" without the ratio.** Closing the last leaf hypothesis cost
   zero axioms and added zero bytecode content (§3.4). It is a statement about
   bookkeeping honesty, not about the validators.
3. **Do not believe the shapes cover anything.** Coverage is now **proved false** for
   this family at the smallest bound the family itself covers, with witnesses the real
   CEK accepts in the same number of steps as the certified inhabitant (§8
   F2-coverage). Every result is "over this layout".
4. **Do not believe the shapes are unrealizable — and do not believe they are
   node-buildable either.** A3's blanket "every shape is empty" is obsolete for 11 of
   12. What replaced it is narrower than it sounds: each re-cut shape has a concrete
   inhabitant satisfying CLAB's ledger predicate **and** both halves of the Conway
   redeemer rule, while `OnChain` remains an opaque axiom, so no term here proves any
   context genuinely on-chain. Fees, witness-set agreement and the UTxO set are still
   unmodelled.
5. **Do not believe any UPLC result is universally quantified over transactions.**
   Every one is bounded by a CEK step budget AND a fixed `Data` skeleton. Quote both
   bounds or quote neither. §5.2 exhibits a theorem that provably does not generalise
   — and it is now load-bearing in a composed result.
6. **Do not believe "`sorry`-free".** 100 theorem-position results are `admit`-closed;
   every top-level theorem inherits `sorryAx`. And do not use the build log's `sorry`
   warning count as a census — 38 modules suppress it.
7. **Do not believe the witnesses and the theorems are always about the same term.**
   For the shaped layer — including both composed results, via `bridge_T1R` and
   `bridge_S1R` — theorems are on `.prop`, witnesses and all measured K on `.exec`,
   equality unproved (F8). Name the layer when quoting this.
8. **Do not believe the source-model and shaped routes are the same strength.** The
   model route quantifies over all contexts and all step counts but trusts a hand
   transcription; the shaped route trusts no transcription but is doubly bounded.
   Neither dominates.
9. **Do not believe the prep-cost figures in `K-MEASUREMENTS.md` §5.1** (F5). Measure
   with `lake build`, never `lake env lean`.
10. **Do not quote SHAPE L2's theorem** (F19 — the class is proved empty).
11. **Do not believe this builds elsewhere without work.** It now *can* (§6.2,
    `WSC/REPRODUCE.md`), but only after reconstructing the substrate from the bundle
    and editing two files. The branch is still unpublished.
12. **Do believe, because it is machine-verified:** the four `.flat` files are
    byte-identical to the `cborHex` of the named unapplied production scripts at
    wsc-poc `7ae0024` (§6.1, 4/4, re-verified here); the redeemer-coverage rule
    reproduces the real node's output on 13/13 goldens (§4b); the re-cut cost zero CEK
    steps; and the substrate bundle reconstructs the pinned tree byte-identically
    (§6.2).

---

## 10. REPRODUCTION

Full third-party recipe, including substrate reconstruction: **`WSC/REPRODUCE.md`**.
The short form:

```bash
# 1. clean-room rebuild
#    expect: 431 jobs, 1:39-1:57, 159 ✅ markers (102 Valid + 57 Expected Falsified),
#            0 errors, 0 ⚠️/❌, 20 expected `sorry` warnings, 93 WSC modules,
#            5 `unused variable` warnings (all Composition.lean:2442-2446), RSS 1.50 GB
cp -a <CLAB> <SCRATCH>/clab-audit && cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c   # 102 Valid, 57 Exp. Falsified
grep -cE '⚠️|❌' build.log; grep -c 'error:' build.log             # 0  0
grep -c "declaration uses 'sorry'" build.log                       # 20  (NOT a census — §2)
grep -c 'unused variable' build.log                                # 5

# 3. source reconciliation (57 + 2 + 100 = 159) over the BUILT modules only.
#    STRIP BLOCK COMMENTS FIRST, and count `by`-newline-`blaster` too (5 of them, §1.4).

# 4. axiom census — PARSE ACROSS NEWLINES (§3); a line grep undercounts sorryAx 17 vs 37
#      Composition.containment_on_contained_class        -> 26
#      RealizableLeaves.containment_on_realizable_class   -> 28 (= 26 + LR_BUDGET_global + TS3)
#      RealizableLeaves.containment_on_seize_class        -> 28 (= 26 + LR_BUDGET_seize + nodeStepsSeize)
#      RealizableLeaves.realizable_inhabitant{,_NS,_S1R}  -> 0, no sorryAx
#      Coverage.not_covers_at_T1R_size                    -> 0, no sorryAx

# 5. axiom-declaration census
grep -rn '^axiom ' --include='*.lean' WSC/ | wc -l                                  # 51
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0
grep -rl 'set_option warn.sorry false' --include='*.lean' WSC/ | wc -l              # 38

# 6. the re-cut, checked in both directions
#      RealizableShapes.all_recut_witnesses_redeemersExact
#      RealizableShapes.all_old_witnesses_fail_c3_coverage
#      Goldens.Audit.every_golden_is_redeemer_covered            # 13/13

# 7. PROVENANCE re-verification (§6.1) — 4/4
sha256sum WSC/flats/*.flat

# 8. SUBSTRATE re-verification (§6.2) — see WSC/substrate/README.md §3
git bundle verify WSC/substrate/pcb-cip153-value-builtins.bundle
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artefact is the
entire content of F5.
