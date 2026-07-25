All jobs terminal, no orphans. Assembling the final report.

REPORT — TASK E2 TRACTABILITY SPIKE (aggregate-fold + nested-pairing shapes, Lean-recursion and UPLC levels)

**Workspace**: `/tmp/claude-1000/-home-gumbo-iohk-wsc-poc/90398e28-5aaf-4f66-9a8f-cb0205ebd5ab/scratchpad/clab-spike` (cp -a of `/home/gumbo/iohk/CardanoLedgerApiBlaster`, main @ 5dab3c4; warm `.lake` cache confirmed: `lake build CardanoLedgerApi` replayed 336 jobs in 5.2s). Deps: Blaster `beta-lambda-cache-optimization` @ 59db213ca639, PlutusCore (PCB) main @ 4ef48606303c, Lean 4.24.0, Z3 4.15.2. All experiments in `Tests/Spike/` (34 files, 1072 LOC Lean + `toy_allnonneg.uplc`). No commits made (per task: report is the deliverable; copy workspace).

**MISSING CONTEXT CAVEAT**: `arch-final.md` and the five `inv-*.md` reports were NOT present at the stated scratchpad paths (dir contained only `clab-spike`; the two other session scratchpads were empty). I proceeded from `Tests/Scripts/WstImportSmoke/Smoke.lean` (import idiom), the Governance example (`#import_uplc` → `#prep_uplc … 9000` → `blaster`, Tests/Scripts/Governance/), Lean-blaster README, and memory notes. Flagged as open issue 1.

---

## DECISION TABLE

**Level 1 — Lean recursion (spec-shape proxies), all over `List (ByteString × Int)` unless noted.** "one-shot" = bare `blaster`, no induction. unfold-depth default 100 (Solver/Command/Options.lean:29); `timeout` option caps Z3 only.

| # | Shape | Strategy | Result | Wall |
|---|-------|----------|--------|------|
| A1 | lockstep pairwiseGe ⟹ Σxs ≥ Σys | one-shot, depth 100 and depth 5 | **Undetermined** (both; full Z3 timeout; clean rerun `A1_OneShot_Clean.lean`: "unsolved goals" after 30s) | 120s/attempt |
| A1 | same | `induction xs generalizing ys <;> blaster` | **Valid** (2 goals; implicit ys case-split handled) | 1.6s file |
| A2 | containment walk `checkContained` ⟹ per-key `amtOf` bound (uniq-keys precond) | one-shot | **Undetermined** | 60s |
| A2 | same | naive `induction xs <;> blaster` | nil Valid; **cons Undetermined** (needs `¬mem → amtOf=0`, itself inductive — Z3 cannot invent it) | 120s |
| A2 | same + foldl-spec (`sumOf` accumulator) | 2 aux lemmas (`amtOf_zero_of_not_mem`, accumulator-generalization `sumOfAcc_eq`) by `induction <;> blaster`, fed via quantified `have`; final composition no induction | **all Valid** (4 thms/7 goals) | **3.4s file** |
| A3 | TWO-LEVEL nested Value containment (real P1/L1.1 shape: cs→tn→amt walk ⟹ flattened per-(cs,tn) sum) | 3 lemmas, multi-level `have`-feeding | **all Valid** (6 goals) | **2.9s file** |
| B1 | nested pairing walk (key-lookup `findAmt`, per-pair v≤w) ⟹ ∀ paired ∃-witness; also getD form | plain `induction xs <;> blaster`, NO aux lemmas | **all Valid** | 2.6s file |
| B2 | positional classify-and-pair cursor walk (EXACT reworked-seize shape: walk all inputs, programmable ones consume outputs in order) ⟹ ΣsumProg ≤ Σouts | naive: **cons Valid, nil Undetermined** (needs Σnonneg≥0); with 1 aux lemma | **all Valid** | 1.8s file (4m naive) |
| B3 | pairing with 4-field per-pair preservation (addr/datum/refScript/amt — Lemma-B width) | plain induction | **Valid** | 1.5s file |
| E | WRONG containment (uniqueness dropped) | `#blaster (gen-cex: 1) (solve-result: 1)` | **Falsified with genuine duplicate-key cex** (soundness check) | 1.0s |
| F | REAL CIP-153 `valueContains` denotation (inlined verbatim from PCB `cip153-value-builtins` @ 830819b, Value/Basic.lean:27/57/114/175; stdlib `List.all/any/find?`) | split lemmas + have-feeding (F2 file) | inner lemma G0 **Valid**; G1/G2/G3 **cons Undetermined**; first formulation also hit hard translate errors (`createPredQualifierAppAux` on quantified have; match-in-goal sensitive) | 7m file |

**Level 2 — UPLC through real CEK symbolic execution** (`#prep_uplc` budget = raw CEK step count; exhaustion → `State.Error` → `isSuccessful` false: PCB CekMachine.lean:229–234 `runSteps … | 0,_ => State.Error`).

| # | Program / budget | Obligation | Result | Wall |
|---|------------------|-----------|--------|------|
| toy | hand-written textual `toy_allnonneg.uplc` (Z-recursion fold, chooseList/head/tail/ifThenElse; parsed via importer adapted from PCB Tests/Conformance/ConformanceUtils.lean; concrete exec sanity: [3,4]→accept, [3,-1,4]→reject, []→accept) @600 | accept(x::t, symbolic t) ⟹ 0 ≤ x | **Valid** | 4.4s file (2 thms) |
| toy @600 | accept([a,b,c]) ⟹ full spec fold (ground spine, symbolic ints) | **Valid** | same file |
| toy @600 | accept(xs) ⟹ spec, `induction xs <;> blaster` | **HARD FAIL: "Inductive datatype with instance parameters not supported: `Fin"** (CEK residual datatypes in translated goal); identical failure for manually-stated cons+IH (`ToyConsProbe.lean`) ⟹ not an induction-tactic artifact: `prop t` on a fully-symbolic list is untranslatable, plus budget-misalignment (embedded unroll of tail has fewer remaining steps than `prop t` — budget monotonicity is a meta-theorem SMT doesn't have) | 4.6s |
| toy @9000 | prep + ground-3 theorem | **Valid** — budget alone scales gently (4.4s→41.0s for 15× budget on a 1-arg program) | 41.0s |
| seize (real bytecode, `programmableSeize.flat` 3932B, sha256 289e9e8d…, unapplied 2-param prod export) @600 | prep only | completes | **11.1s** |
| seize @600 | 2 weak clauses + vacuity probe | clauses "Valid" but **BOTH VACUOUS** — probe `#blaster (solve-result: 1) [∀ cs ctx, valid → ¬accept]` returned **Valid** = no accepting context within 600 steps | 26.4s file |
| seize @1000 | prep + 2 clauses + probe | same: **still budget-vacuous** | 51.6s |
| seize @2000 | prep only | **NEVER COMPLETED**: attempt 1 killed by `timeout 1800` at 29m23s; attempt 2 killed by harness at ~77min wall (47+ CPU-min) | >4600s |
| seize @9000 | prep only | **NEVER COMPLETED** (harness-killed ~62min, 42+ CPU-min) | >3700s |
| seize SHAPED @9000/@3000 (inputs fn fixing spines: 1 input, 2 ref-inputs, 1 output, 1 wdrl; scalars/Data symbolic) | prep | default heartbeats: dies at 200k-heartbeat cap in 44s (`maxHeartbeats 0` required); then **NEVER COMPLETED** (killed ~60min/~63min) ⟹ fixing list spines does NOT collapse the blowup — symbolic Data fields (redeemer, datums, mint) still branch | >3600s each |
| governance (repo's own 4264B example, `proposingInputs`) @9000 | prep only (baseline) | **>29m22s, timeout-killed** — the shipped precedent is equally prep-expensive on this box; seize is not an outlier | >1762s |

**Harness capability checks (D2/U3):**
- `induction xs <;> blaster` / `induction … with | cons hd t ih => …; blaster` as leaf tactic: **works** (verified ~12×; also `Tests/Recursor.lean` replays).
- Feeding proven lemmas: **`have h := lemma` works, both fully-quantified and instantiated** (A2/A3/B2 all depend on it). **`@[simp]` registration does NOT feed blaster** (D2: same cons goal Undetermined at full 90s with the lemma simp-registered). `#blaster [theoremName]` **re-proves from scratch** (Undetermined for inductive lemmas) — no proof reuse at command level.
- Pinned Blaster branch names the command **`#blaster`, not `#solve`** (Blaster/Command/Syntax.lean:44; README documents `#solve`).
- Valid closes via `admit` ⟹ every blaster-proved theorem carries a `declaration uses 'sorry'` warning — final-audit tooling must whitelist these.
- Undetermined leaves an optimize-TRANSFORMED goal; chaining `sorry` after a failed blaster produces a kernel type mismatch (`id sorry` artifact) — classify failures with bare `blaster` runs.
- Falsification + counterexample generation: fast and readable (E: 1s).
- `(timeout: n)` caps Z3 only; Lean-side optimize/prep is uncapped (and `#prep_uplc` can instead die on `maxHeartbeats` depending on inputs-fn shape).

---

## VERDICTS

**(a) P2 (seize, nested pairing walk): needs A+B decomposition AND bounded-length precondition; one-shot NOT plausible.**
- The nested-pairing/cursor SHAPES are trivially cheap at Lean level (B1/B2/B3: seconds, at most one aux lemma) — the proof-theoretic content of Lemma B is a non-problem.
- At UPLC level, unbounded-list induction against `prop` is **blocked twice over** (Fin-translation gap on symbolic-list residuals + budget misalignment), and full-symbolic-ctx prep at any budget where seize can actually accept (>1000; 600/1000 proven accept-UNSAT) costs >75 min (never completed) on 32-core/61GB. Bounded/ground spines with symbolic scalars close in seconds at toy scale, but shaped real-seize prep at 3000/9000 still never completed — fixing spines alone is insufficient while redeemer/datum/mint stay symbolic Data. P2-at-UPLC therefore needs: fixed spines + concrete redeemer constructor/indices (SeizeAct with concrete idxs) + per-shape published K, proven shape-by-shape (bounded-transaction model checking, consistent with the LR-BUDGET stance), with the postcondition split into single clauses and aux lemmas have-fed.
**(b) P1 (transfer, aggregate-fold containment): B2 algebra-assisted is plausible, CONDITIONAL on blaster-friendly restatement of the Value denotations; do NOT jump to B3 yet.**
- The full two-level containment⟹spec algebra (A3, including the accumulator-fold spec bridge L0) closes in 2.9s with hand-rolled pattern-match recursions. With CIP-153 builtins the on-chain containment is ONE builtin call, so the UPLC fold-unrolling cost problem largely disappears for P1 — the burden moves to Lean-level lemmas about `PLC.valueContains`, which is exactly the tractable class.
- BUT the denotations as written (stdlib `List.all/any/find?`, projection lambdas) mostly do NOT close (F: 3 of 4 lemmas Undetermined + one translation-error class). Required bridge: either restate walks as pattern-match recursions + tiny equivalence lemmas, or upstream a blaster-friendly rewrite on the PCB `cip153-value-builtins` branch (conformance tests keep it honest). If that bridge fails in practice, then B3 source-model.
**(c) Harness gaps**: no automatic lemma reuse (`have`-threading only — plan proofs as explicit lemma DAGs); `#blaster`-vs-`#solve` naming; admit/sorry audit noise; Z3-only timeouts (prep and optimize unbounded — cap with external `timeout`, expect `maxHeartbeats` surprises); translation gaps (Fin/CEK residuals on fully-symbolic list args; stdlib list combinators; quantified-have sensitivity to match-in-goal). None blocks Phase A given the strategy in (a)/(b); the prep-cost wall is THE budget-critical risk and argues for shape-restricted contexts and/or a Blaster-side prep optimization (e.g. memoized/opaque recursive-CEK abstraction) before attempting P2 at 9000-class budgets.

**Source-line evidence for fidelity-critical facts**: seize is rewarding-purpose, 2 params (`mkProgrammableSeize :: PAsData PCurrencySymbol :--> PScriptContext :--> PUnit`, wsc-poc `src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1264`, `pisRewardingScript` condition ~:1294); seize walks all inputs/classifies by credential (comment :1266–1276); `pisScriptInvokedEntries` `phead`s the withdrawal list (:361–373, condition :1297); CLAB ledger rule ALREADY forces rewarding-cred ∈ wdrl (`validScriptInfo`, clab-spike `CardanoLedgerApi/V3/Contexts.lean:988–990`) and ≥1 input (:1008) — so "accept ⟹ wdrl ≠ []"/"inputs ≠ []" are hypothesis-implied, NOT bytecode-derived: weak-clause Valids at 600/1000 measure residual-processing cost only; the vacuity probes carry the real bytecode signal. Budget = raw CEK steps (PCB `CekMachine.lean:229–234, 246–252`); `#prep_uplc` requires a `PlutusScript`-typed def and multi-arg inputs fns are supported (PCB `PreProcess.lean:110–153`); `unfold-depth` default 100 (Lean-blaster `Solver/Command/Options.lean:29`); real denotation defs inlined from PCB `cip153-value-builtins` @ 830819b `Value/Basic.lean:27,57,114,175` (spike's pinned PCB predates them).

**Key commands + tail output (representative)**: `lake env lean Tests/Spike/A3_Nested2Level.lean` → 6× `✅ Valid`, real 0m2.900s; `…A2_NaiveInduction.lean` → `✅ Valid` + cons "unsolved goals", real 1m59.7s; `…ToyBounded.lean` → 2× `✅ Valid`, real 0m4.371s; `…ToyTheorems.lean` → evals `true/false/true`, nil `✅ Valid`, cons "Inductive datatype with instance parameters not supported: `Fin", real 0m4.578s; `…C_Prep600.lean` → real 0m11.118s; `…C_Vacuity600.lean` → "❌ Unexpected Valid" (= accept-UNSAT), real 0m16.753s; `…C_Thm1000.lean` → 2× Valid + "❌ Unexpected Valid", real 0m51.566s; `timeout 1800 … C_Prep2000.lean` → EXIT=124 @ real 29m23s (retry harness-killed ~77min); `timeout 1800 … Tests/Scripts/Governance/Governance.lean` → EXIT=124 @ real 29m22s; `…ToyPrep9000.lean` → `✅ Valid`, real 0m41.048s; `…E_Falsify.lean` → "✅ Expected Falsified" + cex, real 0m0.974s.

**Open issues**: (1) context files `arch-final.md`/`inv-*.md` absent from the stated scratchpad paths — spike ran without them; re-validate my framing against ADDENDUM E2 when the doc resurfaces (canonical copy reportedly `CLAB/WSC/ARCHITECTURE.md` on `wsc-containment-proofs`, not present in either checkout's git). (2) The minimum non-vacuous seize budget is unknown (>1000; every prep ≥2000 exceeded 60–90 min caps) — recommend measuring actual CEK steps of a concrete accepting seize run (via `cekExecuteProgramWithBudget` on a constructed concrete ctx) before choosing K. (3) Governance-precedent build times need recalibration: the shipped `#prep_uplc … 9000` example alone is >29min on this hardware — Phase A CI budgeting must plan for hours-scale `lake build` of proof libs (consistent with the canonical-checkout agent's `WSC/Imports.lean` observed at 34+ CPU-min). (4) F-layer translation limitations should be raised upstream (Lean-blaster): stdlib `List.all/any/find?`, `Fin`-bearing residuals, simp-set consumption. (5) Harness kills background jobs at ~60 min — the four ">Nmin, incomplete" entries are lower bounds, not completions.