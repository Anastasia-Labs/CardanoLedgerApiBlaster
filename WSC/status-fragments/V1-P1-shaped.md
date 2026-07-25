# Status fragment — task V1: **P1 (containment) PROVED AT UPLC over shaped contexts**

Written instead of editing `WSC/STATUS.md` (cross-agent collision policy). A later
audit pass should merge the rows below. Measured 2026-07-25, 32-core box, warm
`.lake`, `maxHeartbeats 0`, **under `lake build`** (never `lake env lean`), Lean
4.24.0, Z3 4.15.2, CLAB @ `09bd428` + this work, PCB `cip153-value-builtins`,
Blaster `beta-lambda-cache-optimization`.

## 1. Headline

`WSC/STATUS.md` §1's **P1** row says **NOT-REACHABLE-AT-UPLC**, with P1 proved only
on the source model behind the whole-validator axiom `globalModel_faithful`. That
is now superseded for four shapes:

| obligation | before | after |
|---|---|---|
| **P1** — accept ⟹ `outAtBase ≥ inAtBase + mintOf` for a non-exemptable policy | no UPLC statement at all; symbolic `#prep_uplc` at the needed budget extrapolated at **7–182 YEARS** (`WSC/goldens/K-MEASUREMENTS.md` §5.2); model-level `P1_model` STATED-not-proved | **`✅ Valid` against the real compiled bytecode at budget 4400 over SHAPES T1, T2, T6, T7** — `WSC/Props/Shaped/P1Shaped.lean` `P1_T1`, `P1_T2`, `P1_T6`, `P1_T7`; whole module **3.4 s** |

**No faithfulness axiom.** `#print axioms` on all four theorems returns exactly
`[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` is blaster's
`admit`, as on the pre-existing reviewed `P3_base_requires_global_or_seize`. In
particular `WSC.Model.globalModel_faithful` and every `WSC/Honest.lean` axiom are
ABSENT (`WSC/Shaped/Probe/P1Axioms.lean`).

## 2. Proposed STATUS.md row replacement (P1)

> **PROVEN-AT-UPLC over SHAPES T1/T2/T6/T7 (K = 4400), SIGNED form, no faithfulness
> axiom** — `WSC/Props/Shaped/P1Shaped.lean`. Bounded TWICE (CEK budget AND shape);
> the source-model route (`WSC/Props/P1_Transfer.lean`) remains the only statement
> that quantifies over ALL `ScriptContext`s and still rests on
> `globalModel_faithful`. Only **1 of 3** containment dispatch paths is covered at
> UPLC (Path A); Paths B/C are blocked by an upstream Blaster codegen defect (§5)
> and Path C is proved at Lean level (`pathC_sound`). Input-side aggregation
> (≥ 2 mini-ledger inputs) is blocked by the same defect; output-side aggregation
> IS proved (SHAPES T6/T7).

## 3. The measurement ladder (report ALL rungs, including the failures)

| shape | what it adds | prep | K of its witness | main obligation | controls |
|---|---|---|---|---|---|
| **T1** | 1 mini-ledger in, 1 mini-ledger out, 1 policy/token, EMPTY mint, + external source + escape route; PATH A | **0.97 s @2700, 1.00 s @4400** | **2603** | **`✅ Valid`** | neg. control `✅ Valid`; tightness `✅ Falsified`; vacuity `✅ Falsified`; accepting witness + excluded-case witness |
| **T2** | = T1 + `txInfoMint = [(cs,{tn:q})]`, `q` free, SIGN UNCONSTRAINED, `Member` proof | 1.0 s | **3572** (mint and burn) | **`✅ Valid`** | vacuity `✅ Falsified`; mint witness; burn witness; `mintPos` refutation |
| **T6** | = T1 + a SECOND mini-ledger OUTPUT (containment must aggregate) | 1.0 s | **3150** | **`✅ Valid`** | vacuity `✅ Falsified`; accepting witness where NEITHER output alone suffices (3 + 2 ≥ 5); excluded-case witness |
| **T7** | = T6 + the T2 mint | 1.0 s | **3572** | **`✅ Valid`** | vacuity `✅ Falsified`; burn witness |
| **T4/T5** | = T1/T2 + a SECOND mini-ledger INPUT (input-side aggregation) | **PREP EMITS KERNEL-ILL-TYPED TERM** — see §5 | 3001 / 3970 (measured anyway, `WSC/Shaped/Probe/T4Probe.lean`) | not stated | shapes + K + model cross-check retained |
| **T3** | = T1 with TWO token names ⟹ containment dispatch takes PATH B→C | **PREP EMITS KERNEL-ILL-TYPED TERM** — see §5 | 2083 (`WSC/Shaped/Probe/T1Probe.lean`) | not stated | shape retained as the defect reproduction |

Prep-cost note: the shaped prep is **budget-independent**, confirming
`WSC/SHAPING-RESULTS.md` §2.5 on a new validator path (0.97 s at 2700 vs 1.00 s at
4400). That is the entire reason P1 is reachable; nothing about the postcondition
got easier.

## 4. Why the theorems are not true by construction (the design point)

`validRewardingContext` contains `isBalanced`
(`CardanoLedgerApi/V3/Contexts.lean:1180-1187`). **On a 1-input/1-output shape the
ledger balance rule ALONE forces `qOut = qIn + mint`, so P1 would be
hypothesis-implied.** The task brief's suggested minimal shape is therefore
unusable, and every shape here carries

* a second INPUT at a pubkey address holding the same policy (external source), and
* a second OUTPUT at a pubkey address holding the same policy (the ESCAPE ROUTE),

so the balance rule only says `qIn + … + mint = qOut + … + qEsc`. Controls:

1. `P1ShapedWitness.ctxOk_escape_output_nonempty` — in the ACCEPTING witness the
   escape output carries **4** units of the protected policy: containment is not
   achieved by making escapes impossible;
2. `P1ShapedWitness.exec_rejects_escape` / `P1ShapedOutWitness.exec_rejects_T6_escape`
   — ledger-legal contexts (`validRewardingContext = true`) that move 2 units of a
   registered policy out of the mini-ledger, REJECTED by the real CEK at 4400;
3. `P1ShapedWitness.exec_accepts_exempt_escape` — the SAME violation is ACCEPTED
   once the directory node's interval is widened to cover the policy, which proves
   the hypothesis `coveringNodeExists … = false` is LOAD-BEARING and exhibits P1's
   scope boundary as executable bytecode behaviour rather than prose;
4. vacuity probes at all four shapes `Falsified`, plus four concrete accepting
   witnesses with exact step counts.

## 5. NEW DEFECT — **D6 (upstream Blaster): `#prep_uplc` emits kernel-ill-typed terms whenever a CIP-153 Value builtin's result stays symbolic**

Two independent reproductions, both with CORRECT residuals and both
kernel-rejected:

* `WSC/Shaped/Probe/T4PrepFAILS.lean` (`punionValue` / `pinsertCoin`, i.e. PHASE 3
  of `pvalueFromCred`, ProgrammableLogicBase.hs:446-458). The else-branch binder's
  TYPE was De-Morgan-normalized (`¬(A ∧ B)` ⇝ `¬A ∨ ¬B`) without updating the
  `Blaster.dite'` motive:
  ```
  (kernel) application type mismatch
    Blaster.dite' (¬ qIn0+qIn1 < -2^127 ∧ ¬ -1+2^127 < qIn0+qIn1) …
  argument has type    (qIn0+qIn1 < -2^127 ∨ -1+2^127 < qIn0+qIn1) → State
  but function has type (¬(¬ … ∧ ¬ …) → State) → State
  ```
* `WSC/Shaped/Probe/T3PrepFAILS.lean` (`pvalueContains`, i.e. containment dispatch
  PATH C, :619-647). Same shape of bug with Bool polarity
  (`¬(true = b)` ⇝ `false = b`).

Impact, stated precisely:

* **PATHS B and C of `poutputsContainExpectedValueAtCred` are unreachable at UPLC**
  at ANY shape, so ARCHITECTURE Tier 3.1's "all three paths independently" stands
  at 1/3 at UPLC (Path A) + Path C proved at Lean level (`pathC_sound`, no
  `sorry`) + Path B still only STATED (`L1_1b_pathB_sound`).
* **`pvalueFromCred` PHASE 3 is unreachable at UPLC** at ANY shape — `punionValue`
  sums the LOVELACE entry of the two canonical values it merges, so the range guard
  fires on `inAda0 + inAda1` for every two-contributing-input shape regardless of
  policies. Hence ARCHITECTURE §3-P1's lemma L1.3 stays out of reach at UPLC for
  ≥ 2 mini-ledger inputs. (The OUTPUT side aggregates with plain Integer addition
  inside Path A and IS proved — SHAPES T6/T7.)
* Fix belongs upstream in Blaster's `Optimize` layer: propositional rewrites of a
  `Blaster.dite'` else-branch binder must rewrite the motive too. Both files are
  kept as regression reproductions; neither is imported, so `lake build WSC`
  is unaffected.

## 6. Findings confirmed / carried

* **ARCHITECTURE §3-P1's `mintPos` form is REFUTED against the PRODUCTION
  BYTECODE**, not just against the model. `P1ShapedWitness.mintPos_form_REFUTED`
  + `exec_accepts_burn_at_4400` + `ctxBurn_valid` + `ctxBurn_no_covering_node`:
  a ledger-legal burn of 4 out of a mini-ledger input of 5, leaving 1, is ACCEPTED
  by the real CEK at K = 3572, and has `outSum = 1 < 5 = inSum + mintPos` while
  `1 ≥ 5 + (−4)` holds. The SIGNED form is the one to quote (and the one
  ARCHITECTURE §5.2's Preservation reduction consumes).
* **`DirWF`'s missing interval-PARTITION conjunct** (`P1_Transfer.lean`
  `DirWF_partition_conjunct_missing`, deferred U10) is exactly the residual trust
  surface of the shaped P1 too: the hypothesis `coveringNodeExists … = false` is
  carried explicitly and §4 control 3 shows it is load-bearing.
* **`globalModel_faithful` gains 8 new differential-test vectors.** The source
  model's verdict equals the real bytecode's on all eight new witnesses
  (`model_agrees_on_witnesses`, `model_agrees_on_out_witnesses`) — 6 accepts and
  2 rejects — and these are the first vectors that exercise the mini-ledger
  INPUT-side aggregation and the containment scan with a genuine escape route.

## 7. Open issues

1. **D6 (above)** — the single biggest blocker to widening P1 at UPLC.
2. **One proof index at a time**, as for P5 (SHAPING-RESULTS §6.2): T1/T2/T6/T7 pin
   `paramsRefIdx = 0` and the transfer proof's node index to 1. Not re-measured
   here; the G3 evidence says a symbolic index reintroduces `dropList`'s branch
   structure.
3. **Shape coverage**: still no argument that the shaped family covers the
   transactions the composition layer needs. The honest framing (SHAPING-RESULTS
   §7 item 4) is a bounded-model-checking layer beneath the axiomatic one.
4. **Path B** (`L1_1b_pathB_sound`) is neither proved at Lean level nor reachable
   at UPLC.
5. `WSC/STATUS.md` §1's P1 row, §3's defect list (add D6) and ARCHITECTURE §3-P1's
   `mintPos` statement all need editing by the audit pass; not touched here.

## 8. Reproduction

```
lake build WSC.Props.Shaped.P1Shaped     # 3.4 s: 5× Valid, 5× Expected Falsified,
                                         #        34 native_decide witness statements
lake build WSC.Shaped.Probe.P1Axioms     # the #print axioms audit
lake build WSC.Shaped.Probe.T1Probe      # K = 2603 (T1), 3572 (T2), 2083 (T3)
lake build WSC.Shaped.Probe.T6Probe      # K = 3150 (T6), 3572 (T7)
lake build WSC.Shaped.Probe.T4Probe      # K = 3001 (T4), 3970 (T5)
lake build WSC                           # whole library, 7.5 s warm

# the two recorded upstream-defect reproductions (EXPECTED TO FAIL)
lake build WSC.Shaped.Probe.T3PrepFAILS
lake build WSC.Shaped.Probe.T4PrepFAILS
```

File map:

```
WSC/Shaped/GlobalShapedP1.lean          SHAPES T1, T2, T3 + the "why not 1-in/1-out" note
WSC/Shaped/GlobalShapedP1Prep.lean      prep of SHAPE T1 @4400
WSC/Shaped/GlobalShapedP1MintPrep.lean  prep of SHAPE T2 @4400
WSC/Shaped/GlobalShapedP1Out.lean       SHAPES T6, T7 (output-side aggregation)
WSC/Shaped/GlobalShapedP1OutPrep.lean   preps of T6/T7 @4400
WSC/Shaped/GlobalShapedP1Agg.lean       SHAPES T4, T5 (input-side aggregation; no prep)
WSC/Props/Shaped/P1Shaped.lean          the four P1 theorems, controls, 34 witness stanzas
WSC/Shaped/Probe/{T1,T4,T6}Probe.lean   K measurements + ledger/model sanity
WSC/Shaped/Probe/P1Axioms.lean          #print axioms audit
WSC/Shaped/Probe/T3PrepFAILS.lean       upstream defect D6 reproduction (Path C)
WSC/Shaped/Probe/T4PrepFAILS.lean       upstream defect D6 reproduction (union/Phase 3)
```
