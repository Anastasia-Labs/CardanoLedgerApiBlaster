> **⚠️ SUPERSEDED (task U3, 2026-07-25).** This fragment has been merged into
> `WSC/STATUS.md`, which is now the single authoritative table, and audited in
> `WSC/AUDIT.md`. It is kept as the per-task record only. Where it disagrees with
> `WSC/STATUS.md`, `WSC/STATUS.md` wins — the disagreements found by the U3 audit
> are itemised in `WSC/AUDIT.md` §7.

# status fragment — unit Z6: **shaped P2 (seize) at UPLC, BOTH conjuncts**

Author: Philip DiSarro. Measured 2026-07-25, 32-core box, warm `.lake`, all
timings under `lake build` (never `lake env lean` — SHAPING-RESULTS §5.1),
`maxHeartbeats 0`, Lean 4.24.0, Z3 4.15.2, CLAB @ `09bd428` + this work,
PlutusCoreBlaster `cip153-value-builtins`, Blaster
`beta-lambda-cache-optimization`.

**DO NOT hand-merge blindly** — this fragment lists the rows unit Z6 would have
changed in `WSC/STATUS.md`, per the stage's no-edit rule on that file.

---

## 1. Headline

P2 was the library's only property routed *entirely* through a hand-transcribed
source model, and its containment conjunct was not proven anywhere. Both facts
change:

| | before Z6 | after Z6 |
|---|---|---|
| seize `#prep_uplc` at an accept-capable budget | **never completes** (77 min @2,000; 62 min @9,000) | **3.0 s @ 3,800** (shaped) |
| P2(a) structure preservation | proven on `seizeModel`, + `seizeModel_faithful` | **also proven on the BYTECODE**, `Valid`, axiom-free apart from `blaster`'s `admit` |
| P2(b) containment of the seized delta | **NOT PROVEN** anywhere (bridge B1 FALSE without ledger canonicity) | **PROVEN on the BYTECODE** over SHAPE S1 |
| P2 vacuity at UPLC | budget 600/1,000 probes `Valid` ⇒ every UPLC P2 statement provably vacuous | probe at SHAPE S1 @3,800 **`Falsified`** ⇒ non-vacuous, plus two executable accepting witnesses |

**Why conjunct 2 closes here and not on the model.** `WSC/Props/P2_Seize.lean` §5
records obligation B1 with two machine-checked counterexamples:
`ptokenPairsContain` is not pointwise sound when a token map has DUPLICATE names,
nor when the maps are UNSORTED. Both are forbidden on chain by `validTxOutValue`,
but the model route would have to propagate that canonicity through four token
combinators (obligation B2), which was not attempted. At SHAPE S1 every value is
`Shape.adaPlusOne` — ada plus ONE policy carrying ONE token name — so every token
map has exactly one entry and is duplicate-free and sorted **structurally**.
Neither counterexample can be instantiated, and Z3 discharges containment
directly against the bytecode. This is the clearest example so far of what the
shaped route buys that the model route cannot: the shape supplies, verifiably and
for free, the canonicity side conditions a general proof has to earn.

## 2. Rows to change in `WSC/STATUS.md`

* **P2 row.** Keep the existing source-model text verbatim (it is still the only
  UNBOUNDED P2 statement). Append: *(b) containment is additionally
  **PROVEN-AT-UPLC over SHAPE S1 at K = 3,800** —
  `WSC/Props/Shaped/P2Shaped.lean:P2b_shaped_containment`; (a) likewise —
  `:P2a_shaped_structure`. "NOT-REACHABLE-AT-UPLC" is **withdrawn**: it rested on
  prep cost and on the 600/1,000 vacuity probes, and shaping removes both.*
* **§3 defects.** Add **D4** (new): `#prep_uplc` mis-types `Blaster.dite'`
  else-branches whose condition is a compound `Bool`
  (`Blaster/Optimize/Rewriting/OptimizePropNot.lean:53` rewrites the binder
  `¬ (true = e)` to `false = e` while the head keeps `true = e`; the kernel then
  reports `application type mismatch`). Blocks any shape in which a `Data`
  equality the validator performs has ≥ 2 free scalar leaves. Diagnosed, worked
  around, NOT fixed. Full detail in `WSC/Shaped/SeizeShaped.lean`'s header.
* **P2′ row.** Unchanged, but the blocker is now only "no `DelegateSeize`-shaped
  context written", and a shaped P2 exists to compose with.

## 3. The measurement ladder, including the failures

### 3.1 K measurement first (no prep, no solver)

`WSC/Shaped/Probe/S1K.lean` runs the imported production flat through
`cekExecuteProgram` on concrete SHAPE S1 instances and bisects.

| instance | what it is | `validRewardingContext` | verdict / K |
|---|---|---|---|
| `ctxAccept` | pair absorbs a +2 mint of the seized policy, keeps all seized tokens, output 1 outside the mini-ledger | `true` | **halts, K = 3004** |
| `ctxResidual` | 5 seized tokens + the +2 mint land in output 1, which IS at the base credential (the real goldens' shape) | `true` | **halts, K = 3328** |
| `ctxEscape` | ledger-legal ESCAPE of the seized policy past the mini-ledger | `true` | **REJECTS at 3,800 and at 20,000** |
| `ctxStolen` | `ctxAccept` with the continuing output's STAKING credential changed | `true` | **REJECTS at 3,800 and at 20,000** |

Cheapest accepting seize GOLDEN = 2,570; the other = 4,647
(`WSC/goldens/K-MEASUREMENTS.md` §3). So SHAPE S1 sits between them. Budget
**3,800** was chosen to cover BOTH accepting instances: at 3,000 the
residual-output run — the one every real seize performs — would have fallen
outside the theorem.

### 3.2 Prep — the wall is gone

| prep | budget | wall |
|---|---|---|
| `appliedSeize` (symbolic, WSC/Prep/Seize.lean) | 600 | ~11 s, but **provably vacuous** |
| symbolic | 2,000 | **never completed** (killed at 77 min, K-MEASUREMENTS §5.1) |
| symbolic | 9,000 | **never completed** (killed at 62 min) |
| **`appliedSeizeShaped3800` (SHAPE S1)** | **3,800** | **3.0 s** |

Same flat, same `WSC.seizeInputs` application order. This is the third validator
for which shaped prep is essentially budget-independent (cf. SHAPING-RESULTS
§2.5).

### 3.3 The shape ladder — three FAILED prep variants, then success (DEFECT D4)

The first shape attempted was the natural one: independent payment credentials
and staking credentials on the pair, independent non-ada policies and token
names, and `some rIn` / `some rOut` reference scripts. **Prep failed in 1.8 s**
with `(kernel) application type mismatch` on a `Blaster.dite'` node. Measured
ladder:

| variant | difference | prep outcome |
|---|---|---|
| V0 | pair with independent `mlCS/o0CS`, `mlTn/o0Tn`, independent staking creds, `some rIn`/`some rOut` | **FAILS** — offending condition `true = (i0Qty == o0Qty && i0Tn == o0Tn && i0CS == o0CS)` (the `:1795` remaining-currency-list equality, reached when the seized policy is ada) |
| V1 | policy + token name unified, staking creds dropped, refscripts still `some` | **FAILS** — offending condition `true = (dIn == dOut && rIn == rOut)` (the `:1462-1463` `[datum, refScript]` list equality) |
| V2 | as V1 + refscripts `none` on both | **succeeds** |
| **V3 = SHAPE S1** | as V2 + payment credential unified (`mlH`) and the two STAKING credentials restored as independent variables (`inStk`, `oStk`) | **succeeds, ~1 s** |

Diagnosis: `Blaster.dite'`'s else-branch binder gets rewritten from
`¬ (true = e)` to `false = e`
(`Blaster/Optimize/Rewriting/OptimizePropNot.lean:53`) while the `dite'` head
keeps `true = e`. For a single `==` the head is normalized to a `Prop` equality
`a = b` and the mismatch never arises; for a COMPOUND `Bool` (`&&`) it cannot be,
and the kernel rejects the residual. Every `Data` equality with ≥ 2 free scalar
leaves triggers it.

V3 was chosen over V2 deliberately: it trades the payment-credential half of the
pair's address clause (which becomes one condition `mlH = plc` shared by input and
output) for the STAKING half — the mini-ledger's ownership field, and the clause a
seizure would have to break in order to hand tokens to a different holder. That
half is now earned from the bytecode, and `ctxStolen` shows the attempt is
ledger-legal and rejected.

**Honest residue of D4** (also in the module SCOPE): at SHAPE S1 the paired input
and output necessarily agree on payment credential, non-ada policy id and token
name, and both carry no reference script — so `pairPreserved`'s reference-script
clause is true by construction, and pairs differing in those three fields are
outside the theorem. Argument (not a theorem in this repo) that nothing about
ACCEPTING runs is lost: a differing non-seized policy hits `goOuter`'s `perror` at
:1810/:1815, and a differing token name leaves a positive residual requirement
that `checkBalanceInvariant` refuses at :1508. First thing to redo when D4 is
fixed upstream.

### 3.4 The solver rung — full control set, all stanzas

`lake build WSC.Props.Shaped.P2Shaped` — **26 s** for the whole module
(5 `blaster` obligations + 3 `#blaster` probe stanzas + 7 `native_decide`
witnesses + the `#print axioms` audit).

| stanza | expected | measured |
|---|---|---|
| `P2a_shaped_structure` (conjunct 1) | `Valid` | **✅ Valid** |
| `P2b_shaped_containment` (conjunct 2) | `Valid` | **✅ Valid** |
| `P2_shaped_gates_are_earned` (`pCS = ppCS` ∧ `nCS = dirCS` ∧ `w1 = ilsH`) | `Valid` | **✅ Valid** |
| `P2a_shaped_negative_control` | `Valid` | **✅ Valid** |
| `P2b_shaped_negative_control` | `Valid` | **✅ Valid** |
| `P2a_shaped_tightness` | `Falsified` | **✅ Falsified** |
| `P2b_shaped_tightness` | `Falsified` | **✅ Falsified** |
| **`P2_shaped_vacuity_probe` @3,800** | `Falsified` | **✅ Falsified** (non-vacuous) |

Note the cost of the mint rung: with an EMPTY mint field the same eight stanzas
closed in **3.9 s**; adding a symbolic one-policy/one-token-name mint took the
module to **26 s**. The mint is therefore doing real solver work, not decoration —
and `postconditions_on_the_four_instances` pins it as load-bearing: on `ctxAccept`
the inequality is `12 ≥ 10 + 2`, TIGHT.

### 3.5 Axiom audit

```
WSC.P2a_shaped_structure            [propext, sorryAx, Classical.choice, Quot.sound]
WSC.P2b_shaped_containment          [propext, sorryAx, Classical.choice, Quot.sound]
WSC.P2_shaped                       [propext, sorryAx, Classical.choice, Quot.sound]
WSC.P2ShapedWitness.exec_accepts_at_3800                    [propext, Classical.choice,
                                                             Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
WSC.P2ShapedWitness.exec_rejects_escaping_seize              (same)
WSC.P2ShapedWitness.exec_rejects_stolen_staking_credential   (same)
```

`sorryAx` is `blaster`'s `admit` (SPIKE-FINDINGS), identical to the pre-existing
reviewed `P3_base_requires_global_or_seize`. **No `WSC/Honest.lean` axiom and no
`seizeModel_faithful` appears in any of them** — the shaped route is independent
of the source model. The three executable witnesses depend on `native_decide`'s
compiler trust and NOT on `sorryAx`, so they are independent of both the solver
and `admit`.

## 4. What this does to `seizeModel_faithful`

Written into that axiom's docstring as a clearly-marked APPENDED block
(`WSC/Model/SeizeModel.lean`, nothing existing rewritten). Summary:

* **It does NOT discharge the axiom.** The axiom is unbounded in both dimensions
  the shaped theorem bounds (all `ScriptContext`s, all step counts); a
  budget-and-shape-bounded theorem cannot imply it, and this library has no
  shape-coverage argument (SHAPING-RESULTS §7 limit 1). P2-via-the-model remains
  the only UNBOUNDED P2 statement and still rests entirely on the axiom.
* **It narrows the residual risk**, in four named ways: the prep justification the
  docstring gives is obsolete as a tooling claim; two of the four "un-exercised by
  the goldens" risks (the `perror` polarity of `checkBalanceInvariant` :1508 and of
  the per-pair conjunction :1469) are now exercised by machine-checked runs of the
  real bytecode; the bytecode satisfies the SAME two ground-truth predicates the
  model route derives; and conjunct 2 is no longer unproven everywhere.

## 5. Open issues left by Z6

1. **DEFECT D4 is worked around, not fixed.** Fixing it upstream (Blaster) would
   let SHAPE S1 free the pair's payment credential, non-ada policy, token name and
   reference scripts, removing bound 2b entirely. This is the single highest-value
   follow-up and it is in Blaster, not in WSC.
2. **No `LR_BUDGET_seize`.** Unlike P3/P5, the 3,800-step bound is not bridged to
   node acceptance by any axiom in `WSC/Honest.lean` — there is no seize budget
   axiom. Either add one (with the same ExUnits argument the others use) or state
   plainly that the shaped P2 is a bounded-model-checking result only.
3. **One mini-ledger input.** SHAPE S1's second input is at a PUBKEY address, so
   it is never at the base credential. A two-mini-ledger-input shape would
   exercise the walk's pairing cursor across two pairs (and the
   `seize-2-inputs-partial-with-noise` golden's shape). Prep is affordable; not
   attempted.
4. **Redeemer indices are all concrete.** The loosening rung that SHAPING-RESULTS
   §2.4 ran for the minting policy (SHAPE M2) and §6.2 for the global validator
   (SHAPE G3) was not run for seize. Freeing `outputsStartIdx` in particular would
   require restating conjunct 1 index-free.
5. **Shape coverage.** Same unresolved question as for P4/P5: a shaped theorem is
   a statement about a named finite family of transaction shapes and the
   composition layer cannot consume it as a universal one.
6. `WSC/STATUS.md` and `WSC/SHAPING-RESULTS.md` still describe P2 as
   NOT-REACHABLE-AT-UPLC (STATUS §P2 row; SHAPING-RESULTS §7 table last row and
   "what to do next" item 3). Those are now wrong and are listed here for the
   audit pass rather than edited in place.

## 6. Reproduction

```
cd <CLAB checkout>
lake build WSC.Shaped.SeizeShaped        # 3.0 s — shaped prep at budget 3800
lake build WSC.Shaped.Probe.S1K          # K = 3004 / 3328, validity of all 3 instances
lake build WSC.Props.Shaped.P2Shaped     # 26 s — 5 Valid, 3 Falsified, 7 native_decide, axiom audit
lake build WSC                           # 43 s — whole tree, clean
```

## 7. Files

```
WSC/Shaped/SeizeShaped.lean        SHAPE S1 + prep at 3800; DEFECT D4 diagnosis in the header
WSC/Shaped/Probe/S1K.lean          K bisection + ledger-validity of the concrete instances
WSC/Props/Shaped/P2Shaped.lean     P2(a) + P2(b) at UPLC, controls, 4 concrete instances, axiom audit
WSC/Model/SeizeModel.lean          APPENDED block in `seizeModel_faithful`'s docstring (§4)
WSC.lean                           three new imports
WSC/status-fragments/z6-p2shaped.md  this file
```
