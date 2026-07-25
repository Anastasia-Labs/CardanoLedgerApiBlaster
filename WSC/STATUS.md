# WSC containment campaign — AUTHORITATIVE STATUS

**Read this first, then `WSC/AUDIT.md`.** Everything below is machine-checked or
measured *in this repository*, with the file/line or the measurement cited. Where a
result is not there yet, this table says so in those words.

**Revision: this file was rewritten at task C4 (2026-07-25) from an independent
clean-room rebuild at the C4 HEAD on branch `wsc-containment-proofs`, not from any
task report.** It supersedes the A3 revision and the C1/C2/C3 status fragments, which
are folded in and kept as the per-task record. Any disagreement between a fragment and
this file is resolved in favour of this file, and the disagreements are itemised in
`WSC/AUDIT.md` §8.

---

## 0. THE SEVEN SENTENCES THAT MUST NEVER BE DROPPED

1. **The top claim is NOT PROVED.** *In an honest deployment, programmable tokens
   cannot exist outside the mini-ledger (the `programmableLogicBase` payment
   credential).* What exists is (a) a machine-checked **reduction** of it to four leaf
   obligations plus **26 project axioms** (`WSC.Composition.top_claim`); (b) that
   reduction **discharged outright over one inert accounting class**
   (`containment_on_contained_class`, over `ContainedTx`); and (c) — new in stage 9 —
   that reduction **discharged three of four fields over one node-realizable shape
   class**, `WSC.RealizableLeaves.containment_on_realizable_class_of_p2`, carrying
   `p2` as its single remaining hypothesis and depending on **28** project axioms.
2. **In (b) the class does the work; in (c) the code does one quarter of it.**
   `containedLeaves`'s four fields are proved from ledger accounting; **no UPLC result
   is used** and the acceptance hypotheses are provably unused (Lean's own five
   `unused variable` warnings at `Composition.lean:2442-2446`). In (c), `p1` is
   discharged from `WSC.P1R_T1` — the production `programmableLogicGlobal` bytecode at
   K = 4400 — and **its acceptance hypothesis is genuinely consumed**; but `p4` and
   `nopre` are discharged by the SHAPE (a pure-transfer transaction mints nothing and
   registers nothing) and `p2` is assumed. **N = 1.**
3. **Everything about the bytecode is BOUNDED BY A CEK BUDGET.** `#prep_uplc … n`
   bakes a finite step budget into the term the theorems quantify over; exceeding it
   evaluates to `Error`, which makes `isSuccessful` false and any `accept → POST`
   theorem vacuous past the bound. **No result covers unboundedly large
   transactions.**
4. **The shaped results are ALSO bounded by their SHAPE, and there is still NO
   COVERAGE ARGUMENT — but the shapes are no longer UNREALIZABLE.** This sentence
   changed in stage 9 and the change must be quoted precisely.
   *Was:* every shape was **proved empty** as a class of ledger transactions (a
   one-entry redeemer map alongside two script withdrawals; Conway
   `hasExactSetOfRedeemers`), so the six properties were true statements about empty
   sets.
   *Now:* **11 of 12 shapes were re-cut** to carry exactly the redeemer entries the
   rule demands, every property was re-proved over them, and each re-cut shape has a
   certified inhabitant satisfying `validXContext` **and both halves** of the Conway
   rule. **Coverage is untouched:** `SHAPE-BRIDGE.md` §10 still offers no route,
   `ShapeBridge.M1Covers` is still **false as stated**, and P2b is still provable at
   SHAPE S1R *because* S1R's one-policy/one-token-name values evade the two
   counterexamples that defeat it in general — the re-cut re-used those value terms by
   name and so did not weaken that dependence at all.
   **Honest label for the whole shaped layer: exhaustive symbolic checking of the real
   compiled code over named bounded families of `Data` skeletons that are
   node-realizable, with no argument that the families cover the transactions the
   claim is about.** Never quote a budget without its shape.
5. **`DirWF` / `DIRWF_L` is the single escape-critical assumption.** P5 is exactly as
   strong as it. `mkDirectoryNodeMP` at UPLC is what would turn it from ASSUMED into
   PROVEN. Task V4 added its missing fourth (interval) conjunct and made the two
   bridges that consume it PROVED THEOREMS
   (`WSC.covering_node_excludes_registration`,
   `WSC.Composition.covering_excludes_ledger_registration`), so the surface is the
   same size but discharging it is now an implication rather than a gap.
6. **"`sorry`-free" is FALSE for this library, including for every top-level
   theorem.** **99** theorem-position results are closed by `blaster`'s `admit`; what
   certifies them is the `✅ Valid` verdict in the build log, not the Lean kernel. Every
   top-level theorem inherits `sorryAx` — the older ones through P3, the new one
   through P3 *and* through `P1R_T1`/`bridge_T1R`. **And the build log's `sorry`
   warning count is NOT a census:** 37 modules set `warn.sorry false`. The instrument
   is `#print axioms` → `sorryAx`.
7. **This checkout builds on ONE MACHINE ONLY.** `lakefile.lean` requires
   PlutusCoreBlaster from an absolute local path on an **unpushed** branch, and
   `lake-manifest.json` records **no revision at all** for it. Without its CIP-153
   `Value` builtins `programmableLogicGlobal.flat` does not decode (verified negative
   control against PCB `main`: *"Could not decode program!"*). Until that is fixed,
   **no claim in this repository is independently checkable.**

---

## 1. VERIFIED BUILD STATE (task C4 clean-room rebuild)

| measurement | value |
|---|---|
| command | `rm -rf .lake/build/lib/lean/WSC*` then `lake build WSC WSC.ShapeBridge` |
| exit status | 0 — **429 jobs** |
| wall clock | **1 m 30.22 s** and **1 m 42.57 s** on two independent runs (user 380.4 s + sys 56.6 s, 484 % CPU). Quote the range |
| max RSS | **1.65 GB** (1,648,992 KB) |
| WSC modules re-elaborated | **90** |
| solver verdicts | **158** = **101 `✅ Valid`** + **57 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` | **0** |
| `error:` lines | **0** (hard requirement — met) |
| `declaration uses 'sorry'` | **20** (19 blaster `admit` in `ShapeBridge`, 1 pre-existing in PCB — **not a census**, §0.6) |
| `unused variable` | **5**, all at `Composition.lean:2442-2446` — Lean's own confirmation of §0.2 |
| source reconciliation | 99 `blaster` tactics + 2 `solve-result: 0` + 57 `solve-result: 1` = **158**, exact |
| `axiom` declarations | **51** (Honest 38, Composition 10, P1_Transfer 2, SeizeModel 1) |
| `axiom` under `Prep/`, `Shaped/`, `Props/Shaped/` | **0** — the shaped layer adds no assumption |

Stage-by-stage reconciliation from the A3 baseline: **405 → 429 jobs**, **101 → 158
verdicts**. C3 `+0/+0` (CLAB definitions, `native_decide` golden theorems, one new
axiom, audit prose — no `blaster` invocation); C1 `+11 modules / +18 verdicts`
(9 V + 9 F); C2 `+12 / +38` (25 V + 13 F); C4 `+1 / +1` (1 V, `bridge_T1R`).
`66+9+25+1 = 101` and `35+9+13+0 = 57`.

---

## 2. PROPERTY STATUS TABLE

All six are **PROVED at UPLC against the production bytecode**, over the **re-cut**
shapes. The pre-re-cut theorems are retained, still `✅ Valid`, but range over classes
proved empty and **must not be quoted**.

| # | Status | Theorem(s) | Budget / shape | Witness K | Realizability | 4-point bar |
|---|---|---|---|---|---|---|
| **P1** | PROVED, Path A only | `P1R_T1/T2/T6/T7` (`P1ShapedR.lean`) | 4400 / T1R,T2R,T6R,T7R | 2603 / 3572 / 3150 / 3572 | `t1R…t7R_realizable` | **4/4** each |
| **P2** | PROVED, both conjuncts | `P2a_R_structure`, `P2b_R_containment`, `P2_R_gates_are_earned` (`P2ShapedR.lean`) | 3800 / S1R | 3004 / 3328 | `s1r_realizable(Exact)` | **4/4** |
| **P3** | PROVED, unshaped | `P3_base_requires_global_or_seize_run` (`P3_BaseRun.lean`) | 600 / — | golden 208 | n/a (unshaped) | n/a |
| **P4** | PROVED, all four arms | `P4_disjunction_at_{L1R,DT1R,DS1R}`, `P4_burnonly_arm_R` | 900 / M1R,M2R; 2500 / L1R,DT1R,DS1R | 784 / 1681 / 1257 / 1466 | `m1r,m2r,l1r,dt1r,ds1r_realizable` | **4/4** except M2R **3/4** (D11) |
| **P4a** | PROVED | `P4a_R_*`, `P4a_RIdx_*`, `P4a_local_R` | as P4 | as P4 | as P4 | as P4 |
| **P5** | PROVED | `P5R_shaped_indexed/_exists/_groundtruth` (`P5ShapedR.lean`) | 1600 / G1R | 1541 | `g1R_realizable` | **4/4** |
| **P6** | PROVED | `P6R_shaped_member_adds_to_requirement`, `_mint_stays_at_base`, `_noBaseInputs` | 3300 / G6R | 2837 | `g6R_realizable` | **4/4** |

The four-point bar is: theorem `✅ Valid`; vacuity probe at **its own** prep term and
**its own** shape reporting `✅ Expected Falsified`; concrete accepting CEK witness;
shape realizability theorem. **11 of 12 re-cut shapes meet it in full.**

**Every witness K is unchanged by the re-cut** — evidence that the validators never
dereference `txInfoRedeemers`, except `DelegateSeize`, whose K was re-measured (1466).

Scope caveats per property are in `WSC/README.md` §2.2 and are binding.

---

## 3. COMPOSITION (`WSC/Composition.lean`, `WSC/Props/Shaped/RealizableLeaves.lean`)

Three `LeafSet` terms now exist. They are not interchangeable, and the table is the
whole point:

| term | class | class empty? | `p1` from | acceptance used? | project axioms at the top |
|---|---|---|---|---|---|
| `ShapeRealizability.t1VacuousLeaves` | SHAPE T1 (pre-re-cut) | **PROVED EMPTY** | `absurd` | — | worth nothing; `t1_no_honest_step` proves no step can fire |
| `Composition.containedLeaves` | `ContainedTx` (inert accounting) | no | ledger accounting | **NO** (5 linter warnings) | **26** |
| **`RealizableLeaves.realizableLeaves`** | **`T1RShape`** (re-cut, realizable) | **no — certified inhabitant** | **`WSC.P1R_T1`, the bytecode** | **YES** | **28** (= 26 + `LR_BUDGET_global` + `TS3`), plus `p2` assumed |

**The two-axiom delta is the price of making the bytecode load-bearing** and is the
most informative number in the audit. `RealizableLeaves.realizable_inhabitant` proves
the class non-empty with **0 project axioms and no `sorryAx`**.

**The honest limit on "non-empty":** `WSC.OnChain` is an opaque axiom, so no term in
this library can prove any concrete context genuinely on-chain, and `HonestTx`
requires that. For SHAPE T1 emptiness is a **theorem**; for SHAPE T1R there is no
emptiness proof and the one obstruction that emptied its predecessor is
machine-checked absent. That is weaker than "provably inhabited on-chain", and the
difference must not be elided.

---

## 4. THE SHAPE BRIDGE AND THE BUDGET BRIDGES

* `WSC/ShapeBridge.lean` proves the bridge for **16** shapes, all at `exec` level by
  kernel-checked `rfl` (no `sorryAx`; `inputs_M1` depends on **no axioms at all**).
  **None of those 16 is consumed by anything** — they are all at pre-re-cut shapes.
* **One bridge IS consumed, as of stage 9:** `RealizableLeaves.exec_T1R` (`rfl`) and
  `bridge_T1R` (`blaster`, `✅ Valid`, ~1 s), applied in
  `shapedGlobalContainment_T1R`. The other 11 re-cut shapes have **no** `ShapeBridge`
  entry; writing them is mechanical, consuming them is not.
* **Budget bridges: two of seven published instantiations are now exercised.**
  `LR_BUDGET_base` at `K_base = 600` (in `p3_lifted`) and — new — `LR_BUDGET_global`
  at `K_global = 4400` (in `shapedGlobalContainment_T1R`), whose non-vacuity side
  condition is *discharged* by `NonVacuity.globalNonVacuous_at_4400`, not assumed.
  `LR_BUDGET_minting` and `LR_BUDGET_seize` are still applied by **nothing**.

---

## 5. AXIOM BASE — WHAT IS ASSUMED

51 declarations; **28** reached by the strongest composed result; **0** under the
shaped layer. See `WSC/README.md` §3.2 for the enumerated 26 + 2, and
`WSC/AUDIT.md` §3 for the per-theorem table.

New in stage 9: **`LR_REDEEMER_COVERAGE`** (`WSC/Honest.lean`, LR-CTX audit row S) —
Conway UTXOW's `MissingRedeemers`, which `validScriptContext` deliberately does not
carry, and the only axiom added in the stage. It is reached only by the emptiness
proofs of the **retired** shapes, so it weakens negative results and strengthens
nothing (see D12).

---

## 6. DEFECTS — CURRENT LEDGER

| id | severity | status | summary |
|---|---|---|---|
| **F1** | CRITICAL | **NARROWED** | The top claim is discharged where the code does one quarter of the work. `p1` is bytecode; `p4`/`nopre` are the shape; `p2` is assumed. For the general class nothing is proved. |
| **F2-coverage** | CRITICAL | **OPEN, unchanged** | No argument that the shapes exhaust the transactions the claim is about. This is now the binding constraint. |
| **F2-realizability** | CRITICAL | **REPAIRED (11/12)** | Shapes re-cut to satisfy Conway `hasExactSetOfRedeemers`; verified in both directions (new shapes pass, old shapes fail, 13/13 goldens match). SHAPE **L2** not re-cut. |
| **D5** | HIGH | OPEN | Unpushed local PCB branch, **no revision in the manifest**. Highest operational risk; blocks all external reproduction. |
| **D6** | HIGH | OPEN | Blaster emits kernel-ill-typed `dite'` when a CIP-153 `Value` builtin stays symbolic. Blocks SHAPES T3/T4, hence P1 dispatch Paths B/C and input-side aggregation. Needs an upstream fix. |
| **F8** | MEDIUM | OPEN | `PropExecFaithful`: theorems on `.prop`, witnesses on `.exec`, equality unproved and deliberately not axiomatized. All 12 re-cut groups inherit it; so does the composed result, via `bridge_T1R`. |
| **F4** | MEDIUM | OPEN by nature | "`sorry`-free" is false; 99 results are `admit`-closed and every top-level theorem carries `sorryAx`. |
| **D11 / F17** | MEDIUM | OPEN | SHAPE **M2R has no CEK acceptance witness** — `appliedMintRShapedIdx900.exec` is executed nowhere. Meets 3 of the 4 bars. **Cheapest open item in the repository.** |
| **F19** | LOW | OPEN | SHAPE **L2 not re-cut**; `P4_local_noEscape_shapedIdx` still ranges over a class proved empty. Must not be quoted. |
| **D12 / F18** | LOW | RECORDED | CLAB's `redeemerCoverage` is strictly stronger than the ledger rule (it cannot express `isNativeScript`). Positive uses are conservative; the *negative* uses — the retired shapes' emptiness — inherit the all-Plutus reading. "Unconditional" in those docstrings means "no `RedeemerCoverage` hypothesis", not "no assumption". |
| **`SeizeWdrlOfScoped`** | MEDIUM | OPEN, newly tractable | `LR5` does not entail `seizeCred ∈ txInfoWdrl`. The same rule in the other direction is now audit row S. |
| **`ValueAlgebra`/`LedgerCanon`** | MEDIUM | OPEN | Uninstantiated, so `LR_BALANCE_SLOT` stays an axiom. `valueOf` is not additive over `merge` without canonicity (machine-checked counterexample). ~330 lines. |
| **F5** | MEDIUM | **CLOSED** | Prep-cost table was ~47× pessimistic (`lake env lean` without `--load-dynlib`). Re-measured; `K-MEASUREMENTS.md` §5.1a carries correct figures. |
| **F7** | — | **CLOSED** | Every `*NonVacuous` obligation discharged, all `native_decide`, 0 project axioms. |
| **F13 / F14** | — | **CLOSED (C3)** | Stale seize ExBudget rows corrected; the false `PROVENANCE.md` note removed. |
| **F16** | — | **CLOSED (C4)** | A closed inhabitation statement about a named concrete context now exists (`t1RShape_witness`). |

---

## 7. WHAT WOULD MOVE THE NEEDLE, IN ORDER

1. **A shape-coverage argument.** Nothing else in this list changes the strength of
   the deliverable as much. Until it exists, every result is "over this layout".
2. **Push the PCB branch and pin a real revision (D5).** Cheap, and until it is done
   nothing here is independently checkable.
3. **`p2` at the composed level**, which needs a union `Shape` over the re-cut shapes
   and a P2 discharge at each — entangled with (1). Closing it takes N from 1 to 0 for
   that class.
4. **Bridge and consume the other 11 re-cut shapes** (`exec_<S>R` by `rfl`,
   `bridge_<S>R` by `blaster`, ~1 s each on the evidence of `bridge_T1R`).
5. **Fix D6 upstream**, unlocking SHAPES T3/T4 and P1's remaining dispatch paths.
6. **Add M2R's CEK witness (D11)** — one `native_decide`, the cheapest item here.
7. **Re-cut SHAPE L2 (F19)**, or retire its theorem.
8. **Instantiate `ValueAlgebra` + `LedgerCanon`**, removing `LR_BALANCE_SLOT` from the
   axiom base.
9. **Restate the 12 shaped groups on `Runs.XRun K`** with 12 fresh vacuity probes, to
   delete `PropExecFaithful` campaign-wide. Real risk: one may come back `Valid`, i.e.
   vacuous, as happened to P6 at 2500.

---

## 8. REPRODUCTION

```bash
# the whole library, clean-room
#   C4: 429 jobs, 90-105 s, 158 ✅ markers (101 V + 57 F), 0 errors,
#       20 expected `sorry` warnings, 90 WSC modules, 5 `unused variable`
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# the axiom census behind §5 and AUDIT.md §3
grep -E 'depends on axioms' build.log      # 142 lines, 27 with sorryAx
#   containment_on_contained_class             -> 26
#   containment_on_realizable_class_of_p2      -> 28 (26 + LR_BUDGET_global + TS3)
#   realizable_inhabitant                      -> 0, no sorryAx

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

# PROVENANCE re-verification (AUDIT.md §6.1) -- 4/4 on both counts
sha256sum WSC/flats/*.flat
```

Companion documents: `WSC/AUDIT.md` (**authoritative** — the clean-room re-audit, five
censuses, the provenance re-verification, the honesty-regression checks, the ranked
findings, and "what a reviewer should not believe"), `WSC/README.md` (reviewer-facing
summary), `WSC/EXEC-SUMMARY.md` (one page, no Lean), `WSC/ARCHITECTURE.md` (binding;
ADDENDUM v3 overrides the base text), `WSC/SHAPE-BRIDGE.md`,
`WSC/SHAPING-RESULTS.md`, `WSC/SPIKE-FINDINGS.md`, `WSC/LR-CTX-AUDIT.md`,
`WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md`.
