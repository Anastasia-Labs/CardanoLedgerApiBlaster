# H2 (2026-07-28) — re-cut SHAPES T3R / T4R and reach the containment dispatch's other arms

**Substrate.** wsc-poc `main` @ **2306678** (PR #112) · PlutusCoreBlaster
`cip153-value-builtins` @ **3fdd3fb** · Blaster `wsc-d6-dite-branch-retype` @
**4d320dd** · CLAB `wsc-containment-proofs`, on top of H1's `5951288`.
All three substrate HEADs re-verified at the start of the task, not taken on
trust.

---

## 1. THE PROBLEM, AS IT ACTUALLY STOOD

`poutputsContainExpectedValueAtCred` (`ProgrammableLogicBase.hs:518-670`)
dispatches three ways. ARCHITECTURE Tier 3.1 wants each to independently imply
the aggregate bound. Before this task only **PATH A** was reachable at UPLC,
and the campaign attributed that to Blaster defect **D6**.

D6 was fixed at N5 and re-tested at N6, and the N6 audit was careful to say that
this did **not** verify the paths — SHAPES T3 and T4 are PRE-re-cut and provably
unbuildable on a node (audit **F2**):

| shape | script inputs | mint policies | script wdrls | redeemers Conway demands | redeemers supplied |
|---|---|---|---|---|---|
| T3 | 1 | 0 | 2 | **3** | **1** |
| T4 | **2** | 0 | 2 | **4** | **1** |

A P1 theorem at either would have ranged over an EMPTY class. **That is the gap
this task closes, and it is the re-cut, not the substrate.**

## 2. WHAT LANDED

| file | lines | what |
|---|---|---|
| `WSC/Shaped/GlobalShapedP1BC.lean` | 346 | SHAPES **T3R** (T3 + the 3-entry `p1RRedeemers`) and **T4R** (T4 + the new 4-entry `p1AggRRedeemers`, two `Spending` entries) |
| `WSC/Shaped/GlobalShapedP1BCPrep.lean` | 31 | `#prep_uplc appliedGlobalShapedT3R` / `appliedGlobalShapedT4R`, both at budget **4400** (SHAPE T1R's) |
| `WSC/Props/Shaped/P1ShapedBC.lean` | 936 | P1 at both shapes to the four-point bar + the dispatch-path evidence |

Nothing else about either shape changed: every amount, policy, credential and
hash that was symbolic is still symbolic, and P1's two design requirements — a
NON-BASE input and a NON-BASE output, so `isBalanced` alone cannot force the
conclusion — are preserved verbatim. `P1BC_T3R_tightness` is the machine-checked
form of that (`✅ Expected Falsified`: the ledger rules alone do **not** imply
containment at this shape).

## 3. THE FOUR-POINT BAR

| property | shape | (a) theorem `✅ Valid` | (b) vacuity probe at OWN term + shape | (c) two-sided CEK witness | (d) realizability |
|---|---|---|---|---|---|
| **P1** | **T3R** | `P1BC_T3R` ✅ — stated for **BOTH** token names | `P1BC_T3R_vacuity_probe` ✅EF (+ `P1BC_T3R_tightness` ✅EF) | `K_T3R_B_is_1936` (1936/1935), `K_T3R_C_is_2228` (2228/2227), `K_T3R_C2_is_2228` | `t3R_realizable`, `t3R_realizable_pathC` + class `t3R_class_covered` |
| **P1** | **T4R** | `P1BC_T4R` ✅ | `P1BC_T4R_vacuity_probe` ✅EF | `K_T4R_is_2696` (2696/2695) | `t4R_realizable` + class `t4R_class_covered` |

Point-level realizability packages, per witness: `validRewardingContext = true`,
`redeemersExactAllPlutus = true` (**both** halves of Conway's
`hasExactSetOfRedeemers`), `RedeemerCovered`, and acceptance by the REAL compiled
bytecode inside the theorem's budget. All by `native_decide`, no solver.

Postconditions are `Model.outSum` / `inSum` / `mintSigned` — `WSC/Model/Ground.lean`,
functions of `ScriptContext` fields and CLAB's `valueOf` only. No
validator-computed accumulator appears in any conclusion.

## 4. WHICH PATH EACH SHAPE RUNS — proved, not asserted

* **PATH A is excluded at T3R — PROVED.** `T3R_not_path_A`: two ledger-legal,
  redeemer-covered contexts the real CEK REJECTS, one short on `tn0` with `tn1`
  whole, the other its mirror (`ctxEsc_quantities`). PATH A polices exactly one
  `(cs, tn)` pair; whichever it were, one of the two leaves it whole and PATH A
  would accept. Both are rejected.
  Class-level corroboration, holding for EVERY leaf assignment: the mint field
  is empty, so `expectedProgrammableOutputValue` is `totalProgTokenValue_`
  outright (`:1226-1229` takes its THEN branch — no `punionValue`, no filter),
  and `pcheckTransferLogicAndGetProgrammableValue` `pcons`es whole
  currency-symbol pairs through unchanged (`:917-926`), never individual token
  names. So the expected value IS the mini-ledger input's non-ada map, which this
  shape builds with two token names, and the `:655-656` guard is false.

* **PATH C is executed and returns True at `ctxC` — PROVED.**
  `T3R_pathC_is_taken` + the argument in `P1ShapedBC.lean`'s header.
  `expectedProgrammableOutputValue` (`:1225-1268`) is `plet`-bound before the
  containment call at `:1270-1276` and its definition mentions `ptxInfo'inputs`,
  `ptxInfo'referenceInputs`, `ptxInfo'mint`, `ptxInfo'signatories`,
  `ptxInfo'wdrl` and the redeemer — **not `ptxInfo'outputs`**. `ctxB` and `ctxC`
  agree on every one of those and differ only in two output quantities, so both
  present the same expected value `E`. If `ctxC` had accepted on PATH B then
  `E = {cs:{TOKA:6,TOKB:5}}`, and `ctxB` would fall through to PATH C and be
  rejected for `6 ≤ 5`. `ctxB` is accepted. ∎

* **PATH B is reached and MEASURED — and cannot be proved by any accept/reject
  test.** On ledger-valid contexts with node-representable quantities `B ⟹ C`
  (if output 0's map equals `E` exactly, the sum over all mini-ledger outputs
  contains `E`, every other contribution being `> 0` by `validTxOutValue`), so
  no acceptance or rejection distinguishes them. B is a pure performance fast
  path. What IS machine-checked:
  * `T3R_pathB_condition` — the two sides of the `equalsData` at `:638`, in
    ground-truth vocabulary: the mini-ledger output's non-ada value map EQUALS
    the mini-ledger input's at `ctxB` and DIFFERS at `ctxC`. At this shape those
    ARE the two sides, because one contributing input means `pvalueFromCred`
    finishes in PHASE 2 with `ptail # (pasMap # firstVd)` and no arithmetic, the
    empty mint sends `:1226-1229` down its THEN branch (no union, no filter), and
    the transfer walk conses whole currency-symbol pairs through unchanged.
  * the **292-step gap**: `K = 1936` at `ctxB` vs `K = 2228` at `ctxC`, both
    pinned two-sided, over two contexts differing in ONE integer leaf by ONE.
    `ctxC2`, which over-supplies BOTH token names, costs the same 2228 —
    consistent with both being on PATH C and inconsistent with the cost tracking
    the quantities.

  ⚠ ONE KNOWN SEPARATOR, recorded not exploited: `punionValue` errors on
  overflow (`|q| > 2^127 − 1`) and `accumulateOutputsAtCred` calls it, so two
  mini-ledger outputs summing past that bound take B to `True` and C to
  `perror`. CLAB's `validTxOutValue` has no upper bound on a quantity; a node's
  CDDL does. Hence "B ⟹ C on ledger-valid contexts **with node-representable
  quantities**".

* **T4R's PHASE 3** — measured the same way: `K = 2696` against SHAPE T1R's
  2343 over the same skeleton plus one mini-ledger input. This is
  ARCHITECTURE §3-P1's lemma **L1.3** (`valueFromCred` counts EVERY base input),
  which `WSC/Props/P1_Transfer.lean` records as STATED-NOT-PROVED, discharged by
  the bytecode on a node-realizable shape.

## 5. TIER 3.1 — BEFORE AND AFTER

| | before H2 | after H2 |
|---|---|---|
| PATH A (single-asset scan) | **PROVED** at UPLC, 5 shapes (T1R/T2R/T6R/T7R/T8R) | unchanged |
| PATH B (wholesale `Data` equality) | not reachable at any node-realizable shape | **REACHED**; condition evaluated (`T3R_pathB_condition`), execution separated by cost (292 steps). **Not provable by any accept/reject theorem** — it is subsumed by C |
| PATH C (builtin `pvalueContains`) | Lean-level only, on the SOURCE MODEL (`pathC_sound`), behind a fidelity axiom | **PROVED EXECUTED AND TRUE at UPLC** over a class with a certified inhabitant |
| input-side builtin accumulation | not reachable | **PROVED** at SHAPE T4R (`P1BC_T4R`) |

**The sentence that may be quoted:** *2 of 3 dispatch paths verified at UPLC over
realizable classes with certified witnesses (A and C); the third (B) is reached
and measured but is semantically subsumed by C, so no theorem can separate it.*
Anything stronger is an overclaim. In particular this is still SHAPE-bounded:
the implication holds over the T3R/T4R classes, not over all contexts, exactly
like every other result in this library.

## 6. CENSUS

Two clean-room runs (`rm -rf .lake/build/{lib/lean,ir}/WSC` then `lake build WSC`,
in a copy — never in the canonical tree):

| measurement | N6 | H1 | **H2** |
|---|---|---|---|
| jobs | 440 | 440 | **444** |
| solver verdicts | 170 = 108 V + 62 EF | 170 = 108 V + 62 EF | **175 = 110 V + 65 EF** |
| `⚠️ Undetermined` / `❌` | 0 | 0 | **0** |
| `error:` lines | 0 | 0 | **0** |
| `declaration uses 'sorry'` | 20 | 20 | **20** |
| `unused variable` | 5 | 5 | **5** |
| WSC modules | 102 | 103 | **106** |

H1 added no solver verdicts (its T8R work is `native_decide` throughout). The
+5 are H2's: `P1BC_T3R`, `P1BC_T4R` (`✅ Valid`) and `P1BC_T3R_vacuity_probe`,
`P1BC_T3R_tightness`, `P1BC_T4R_vacuity_probe` (`✅ Expected Falsified`).

Axiom census (`#print axioms`, both output forms):

| result | axioms |
|---|---|
| `P1BC_T3R`, `P1BC_T4R` | `propext, sorryAx, Classical.choice, Quot.sound` — `sorryAx` is `blaster`'s `admit`, as for every shaped theorem (F4) |
| `t3R_realizable`, `t3R_realizable_pathC`, `t4R_realizable` | `propext, Classical.choice, ofReduceBool, trustCompiler, Quot.sound` |
| `t3R_class_covered`, `t4R_class_covered` | `propext, Classical.choice, Quot.sound` — **no `sorryAx`, no project axiom** |
| `T3R_not_path_A`, `T3R_pathC_is_taken`, `T3R_pathB_condition`, all four `K_*` | `propext, (Classical.choice,) ofReduceBool, trustCompiler, Quot.sound` |

## 7. COVERAGE FAMILY

`Coverage.recutFamily` went **FOURTEEN → SIXTEEN**: `rangeT3R` (44 free leaves)
and `rangeT4R` (42) joined, with `inv_T3R` / `inv_T4R` and the two extra
`family_invariants` cases. Total free leaves 500 → **586**. Growing the family
only strengthens §6's negative results, which go through `family_invariants` and
needed no other change. Both new members carry a certified inhabitant, so the
post-F23 description "all node-realizable" still holds.

## 8. WHAT IS STILL OPEN ON THIS AXIS

* PATH B cannot be separated by a theorem (see §4). This is a fact about the
  bytecode, not a gap in the method, and no further re-cut fixes it.
* T3R/T4R are single-policy shapes. A multi-POLICY expected value (two currency
  symbols) also takes the B/C arm — the guard at `:655-656` fails on
  `pnull # csPairsRest` rather than on the token-name count — and would exercise
  `pvalueContains` across two currency symbols, plus the transfer walk's
  per-policy proof lockstep twice over. No shape in this library has two policies
  at the mini-ledger. Not attempted here.
* T3R has one mini-ledger output. A two-mini-ledger-output ×
  two-token-name shape would put PATH C's `accumulateOutputsAtCred` aggregation
  and the B/C dispatch on the same shape; SHAPE T6R covers the aggregation on
  PATH A only. Not attempted here.
* Everything binding on the rest of the library binds here unchanged: F8
  (`PropExecFaithful`), F4 (`sorry`-free is false), the `coveringNodeExists`
  non-exemption hypothesis, and the budget bound `LR_BUDGET_global`.
