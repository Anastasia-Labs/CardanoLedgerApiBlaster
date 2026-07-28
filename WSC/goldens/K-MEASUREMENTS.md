# K-MEASUREMENTS — true CEK step counts of the WSC golden runs

**Current as of task N2, wsc-poc `main` @ `2306678` (PR #112, "Seize path:
per-pair value delta via CIP-153 builtins, witnessed base delegation").**
Everything below §8 is the pre-#112 document, preserved verbatim and clearly
marked SUPERSEDED — the deltas are the interesting part, so the old numbers are
kept rather than deleted.

**Headline (updated by task N5).** All **13 of 13** goldens are now measured:
the N2 blocker is CLEARED. PlutusCoreBlaster `3fdd3fb` adds the missing CIP-153
builtin `ScaleValue` (flat tag 100), so the post-#112 `programmableSeize` script
decodes, runs and pins K two-sided like every other golden. Every golden got
cheaper — K falls by 6.5 % to 43 % — which is what an optimisation PR should do,
and the three seize rows are the biggest winners (−23 %, −43 %, −26 %).

The same task found and fixed a SECOND, pre-existing defect that only the seize
rows could expose: PCB's `unValueData` and `valueData` cost entries carried
plutus-core **1.57** coefficients while the rest of its table is **1.63**, the
version wsc-poc pins. The four `programmableLogicGlobal` goldens reference both
builtins but never evaluate them on the paths their contexts take, so no golden
had ever exercised the wrong numbers. With the fix, PCB's metered CEK reproduces
the Haskell ledger `ExBudget` **exactly, to the unit, on all NINE accepting
goldens** — previously 7 of 9. §7 records the whole diagnosis.

---

## 1. Method (unchanged)

`K` = the minimal CEK step budget at which the run's outcome appears, which for
a halting program is exactly its step count. Measured by
`WSC/goldens/KMeasure.lean.disabled` run from a `cp -a` of PlutusCoreBlaster
(branch `cip153-value-builtins` @ `9f9ca8c`), over the fully-applied programs in
`WSC/goldens/applied/*.flat` (prod script + params + golden `ScriptContext` all
baked in as `Data` constants, so `initialState body` starts exactly the
computation the ledger ran).

Every K below is pinned **TWO-SIDED**, as required: `runSteps @ K` reaches the
terminal state and `runSteps @ K-1` does not (`Error`, i.e. budget starvation),
and `runSteps @ 10·K` is re-classified to show the outcome is stable at 10×
budget rather than an artefact of a tight budget. The runner reports all three
per golden; the raw log is quoted in §6.

## 2. The goldens, post-#112

| golden | accepts | outcome @K | **K** | @K−1 | @10K | ExBudget CPU | ExBudget mem | PCB budget = ledger? |
|---|---|---|---|---|---|---|---|---|
| programmableLogicBase.base-spend-transfer-tx | yes | Halt | **194** | Error | Halt | 4,617,501 | 10,724 | **exact** |
| programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT | no | Error | 193 | Error | Error | — | — | n/a |
| programmableTokenMinting.mint-burnonly | yes | Halt | **784** | Error | Halt | 14,213,355 | 43,421 | **exact** |
| programmableTokenMinting.mint-delegate-transfer-topup | yes | Halt | **1,257** | Error | Halt | 26,453,981 | 69,372 | **exact** |
| programmableTokenMinting.mint-local-registered-by-ref | yes | Halt | **1,681** | Error | Halt | 34,116,362 | 92,870 | **exact** |
| programmableTokenMinting.mint-local-empty-withdrawals-REJECT | no | Error | 1,627 | Error | Error | — | — | n/a |
| programmableSeize.seize-1-input | yes | Halt | **2,305** | Error | Halt | 51,415,864 | 126,764 | **exact** |
| programmableSeize.seize-2-inputs-partial-with-noise | yes | Halt | **2,905** | Error | Halt | 72,531,075 | 159,980 | **exact** |
| programmableSeize.seize-1-input-missing-residual-output-REJECT | no | Error | 1,677 | Error | Error | — | — | n/a |
| programmableLogicGlobal.transfer-nonmember-covering-node | yes | Halt | **1,453** | Error | Halt | 27,817,781 | 80,469 | **exact** |
| programmableLogicGlobal.transfer-member-single-policy | yes | Halt | **2,782** | Error | Halt | 56,258,707 | 151,501 | **exact** |
| programmableLogicGlobal.transfer-mixed-many-policies | yes | Halt | **3,441** | Error | Halt | 74,010,662 | 188,987 | **exact** |
| programmableLogicGlobal.transfer-containment-violation-REJECT | no | Error | 2,370 | Error | Error | — | — | n/a |

`PCB budget = ledger` is an independent-implementation agreement check: PCB's
budget-metered CEK run of the applied program reproduces the ledger `ExBudget`
recorded in the golden JSON **exactly, to the unit**, for all 9 accepting
goldens (the ExBudget itself comes from Haskell
`PlutusLedgerApi.V3.evaluateScriptCounting` at PV11). The seize ExBudget column
is still populated — the ledger evaluator has no trouble with `ScaleValue`; it
is only PCB that cannot read the script.

## 3. DELTA vs pre-#112 — the point of the re-measurement

Baseline = the pre-#112 table (now §9 below), measured against wsc-poc
`f918ec6`.

| golden | K before | K after | ΔK | Δ% | ExBudget CPU before → after | Δ% |
|---|---|---|---|---|---|---|
| base-spend-transfer-tx | 208 | **194** | −14 | **−6.7 %** | 4,525,794 → 4,617,501 | **+2.0 %** ⚠ |
| base-…-REJECT | 286 | **193** | −93 | **−32.5 %** | — | — |
| mint-burnonly | 784 | **784** | 0 | 0 % | 14,215,312 → 14,213,355 | −0.01 % |
| mint-delegate-transfer-topup | 1,257 | **1,257** | 0 | 0 % | 26,455,938 → 26,453,981 | −0.01 % |
| mint-local-registered-by-ref | 1,681 | **1,681** | 0 | 0 % | 34,116,362 → 34,116,362 | 0 % |
| mint-local-empty-withdrawals-REJECT | 1,627 | **1,627** | 0 | 0 % | — | — |
| seize-1-input | 3,002 | **2,305** | −697 | **−23.2 %** | 60,231,630 → 51,415,864 | **−14.6 %** |
| seize-2-inputs-partial-with-noise | 5,079 | **2,905** | −2,174 | **−42.8 %** | 105,501,594 → 72,531,075 | **−31.3 %** |
| seize-…-REJECT | 2,261 | **1,677** | −584 | **−25.8 %** | — | — |
| transfer-nonmember-covering-node | 1,554 | **1,453** | −101 | **−6.5 %** | 29,160,036 → 27,817,781 | −4.6 % |
| transfer-member-single-policy | 3,262 | **2,782** | −480 | **−14.7 %** | 62,665,145 → 56,258,707 | −10.2 % |
| transfer-mixed-many-policies | 3,726 | **3,441** | −285 | **−7.6 %** | 78,031,424 → 74,010,662 | −5.2 % |
| transfer-containment-violation-REJECT | 2,737 | **2,370** | −367 | **−13.4 %** | — | — |

Reading of the deltas, with the caveats that matter:

* **Minting is a control, and it behaves like one.** The minting bytecode is
  byte-identical across `f918ec6 → 2306678` (cborHex sha256 `7274240514ff` both
  sides) and all four minting K's are UNCHANGED to the step. This is the
  strongest evidence that the measurement is sound: the goldens' contexts,
  script parameters and two of the redeemers all changed underneath (see
  MANIFEST.md), yet a validator whose bytecode did not change did not move by a
  single step. The ~0.01 % CPU wobble on two of them comes from the ctx change,
  not the script.
* **Global falls 6.5–14.7 %**, which is the `pownerWdrlIdxs` witness replacing a
  withdrawal-map scan doing exactly what #112 says it does.
* **Seize's ledger CPU falls 14.6 % on one input and 31.3 % on two** — the
  saving grows with the number of seized pairs, consistent with a per-pair
  scan being replaced by a per-pair builtin. Its K is unknown.
* ⚠ **Base is the one place a number ROSE, and it deserves to be flagged.** K
  falls 208 → 194, but ledger CPU RISES 4,525,794 → 4,617,501 (+2.0 %). Fewer,
  more expensive steps: the new body does `dropList 6` plus an indexed lookup
  where the old one walked a 2-entry withdrawal map, and on a map this small the
  hand-rolled walk was not the bottleneck. The in-source rationale
  (`ProgrammableLogicBase.hs:713-719`) claims the win at scale, and these
  goldens have 2- and 3-entry withdrawal maps, so they are simply not where the
  claimed ~4.2M saving lives. **This is not evidence against #112 — it is
  evidence that the goldens do not cover the case #112 optimises.** A golden
  with a large withdrawal map would settle it; none exists today.
* The base REJECT's −32.5 % is not an optimisation signal: the rejecting path
  now fails at the indexed credential comparison instead of after a full scan,
  so it exits earlier.

## 4. Per-validator K for `LR-BUDGET`

Same two numbers with the same two jobs as before (conflating them is the
easiest way to publish a vacuous theorem):

* **K_novac** = MIN over accepting goldens — a prep at budget ≥ K_novac provably
  admits an accepting run, so the mandatory vacuity probe will be Falsified.
* **K_cover** = MAX over accepting goldens × margin — what `LR-BUDGET_v` must
  quantify over to cover these transaction shapes.

| validator | K_novac (witness) | K_max (accepting goldens) | K_cover ×1.5 | K_cover ×2 | change vs pre-#112 |
|---|---|---|---|---|---|
| programmableLogicBase | **194** (base-spend-transfer-tx) | 194 | 291 | 388 | 208 → 194 (−6.7 %) |
| programmableTokenMinting | **784** (mint-burnonly) | 1,681 | 2,522 | 3,362 | unchanged |
| programmableSeize | **UNKNOWN** | UNKNOWN | — | — | was 3,002 / 5,079; now unmeasurable (§7) |
| programmableLogicGlobal | **1,453** (transfer-nonmember-covering-node) | 3,441 | 5,162 | 6,882 | 1,554 → 1,453 / 3,726 → 3,441 |

Caveat, unchanged and still binding: K_novac is an UPPER bound on the true
minimum accepting budget (a hand-minimised accepting ctx could halt in fewer
steps); it is exactly what a non-vacuity claim needs — a witness — not a lower
bound on the threshold. K_cover covers only transactions no bigger than these
goldens.

For seize, `LR-BUDGET` currently has **no measured witness at all**. Any seize
budget claim made before §7 is fixed is unbacked, and a seize vacuity probe
cannot be interpreted, because we do not know whether the chosen budget is above
or below the accepting floor.

## 5. Applied-flat fidelity re-verification

`WSC/goldens/KVerify.lean.disabled` + `WSC/goldens/verify-applied.py`, re-run on
the regenerated flats:

```
ALL-MATCH (of 13 decodable; 0 BLOCKED)
```

Each decodable applied program's `Apply` spine, after the script's own top-level
`Force`/let application (spine arg 0), carries exactly `paramsHex… ++
[scriptContextHex]` from the sibling JSON, byte-identical after re-serialisation
with PCB's `PlutusCore.Cbor.encodeData`. No file is a bare top-level lambda
(`KMeasure`'s `shape=Apply(applied)` column), so no measurement is
arity-vacuous. Polarity is preserved: the 7 measurable accepting goldens `Halt`,
the 3 measurable rejecting goldens `Error`, still `Error` at 10× the budget.

## 6. Raw runner output (task N2)

Command:

```
cd <SCRATCH>/pcb-n2 && lake env lean KMeasureN2.lean
```

(`KMeasureN2.lean` = `WSC/goldens/KMeasure.lean.disabled` with the `applied/`
path rewritten to the scratch copy of this repo; PCB copy at
`cip153-value-builtins` @ `9f9ca8c`.)

```
programmableLogicBase.base-spend-transfer-tx: K=194 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=103 | pcbBudget[cpu=4617501,mem=10724]
programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: K=193 outcome=error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=103 | pcbBudget[n/a(rejecting)]
programmableTokenMinting.mint-local-registered-by-ref: K=1681 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 | pcbBudget[cpu=34116362,mem=92870]
programmableTokenMinting.mint-burnonly: K=784 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 | pcbBudget[cpu=14213355,mem=43421]
programmableTokenMinting.mint-delegate-transfer-topup: K=1257 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 | pcbBudget[cpu=26453981,mem=69372]
programmableTokenMinting.mint-local-empty-withdrawals-REJECT: K=1627 outcome=error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1285 | pcbBudget[n/a(rejecting)]
programmableLogicGlobal.transfer-member-single-policy: K=2782 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=2789 | pcbBudget[cpu=56258707,mem=151501]
programmableLogicGlobal.transfer-nonmember-covering-node: K=1453 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=2789 | pcbBudget[cpu=27817781,mem=80469]
programmableLogicGlobal.transfer-mixed-many-policies: K=3441 outcome=halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=2789 | pcbBudget[cpu=74010662,mem=188987]
programmableLogicGlobal.transfer-containment-violation-REJECT: K=2370 outcome=error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=2789 | pcbBudget[n/a(rejecting)]
```

Applied-program node counts are 103 (base), 1,285 (minting), 2,789 (global) —
constant within a validator family because each whole `Data` argument is a
single `Const` node.

## 7. ✅ RESOLVED (task N5): PCB could not decode the post-#112 seize script

**Symptom.** All three `programmableSeize` applied flats, and the UNAPPLIED
prod-exported `programmableSeize.json` as well, fail PCB's flat importer:

```
error: Decoding error in '…/programmableSeize.seize-1-input.flat': Could not decode program!
error: Decoding error in '…/seize-unapplied.flat': Could not decode program!
```

`programmableLogicGlobal` decodes fine, so this is not a general CIP-153
problem.

**Cause, measured rather than guessed.** Traversing the prod-exported UPLC terms
and collecting every `Builtin` node gives:

| validator | builtins referenced |
|---|---|
| programmableLogicBase | EqualsInteger, IfThenElse, FstPair, SndPair, HeadList, TailList, UnConstrData, UnMapData, UnIData, EqualsData, DropList |
| programmableLogicGlobal | + AddInteger, LessThanEqualsInteger, EqualsByteString, LessThanByteString, ChooseList, MkCons, NullList, MapData, UnListData, UnBData, **InsertCoin, UnionValue, ValueContains, ValueData, UnValueData** |
| programmableSeize | AddInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger, EqualsByteString, LessThanByteString, IfThenElse, FstPair, SndPair, ChooseList, MkCons, HeadList, TailList, ListData, IData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData, MkPairData, DropList, UnionValue, ValueData, UnValueData, **ScaleValue** |
| programmableTokenMinting | EqualsInteger, LessThanInteger, LessThanEqualsInteger, EqualsByteString, IfThenElse, FstPair, SndPair, ChooseList, MkCons, HeadList, TailList, ConstrData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData, DropList |

In seize but not global: `LessThanInteger, ListData, IData, MkPairData,
**ScaleValue**`. The first four are ordinary builtins PCB has had for a long
time. `ScaleValue` is a **seventh** CIP-153 Value builtin that PCB does not know
at all:

* plutus-core 1.63.0.0 assigns `ScaleValue` **flat tag 100** — decode side
  `PlutusCore/Default/Builtins.hs:2720` (`go 100 = pure ScaleValue`), encode
  side `:2616` (`ScaleValue -> 100`), declaration `:220`, meaning `:2467-2473`
  (`scaleValue : integer → value → value`).
* PCB's `builtinTable` (`PlutusCore/UPLC/FlatEncoding/Basic.lean:265-311`) stops
  at `(99, .UnValueData)`. `decodeBuiltinFun` reads a 7-bit tag — 100 fits in 7
  bits, so it is read successfully and then `List.lookup 100 builtinTable`
  returns `none`, failing the whole program decode. That is why the error is a
  flat "Could not decode program!" with no tag in it.
* PCB also has no `.ScaleValue` `BuiltinFun` constructor and no denotation in
  `PlutusCore/UPLC/BuiltinFunctions/Value.lean`, so adding the tag alone would
  make the program decode and then get stuck at evaluation.

**Blast radius.** This is not confined to K-measurement. Anything that imports
the post-#112 seize bytecode into Lean is blocked: `WSC/flats` (the unapplied
seize flat), any `#prep_uplc` over seize, and therefore P2 and the seize-side
shapes.

**Fix recipe** for whoever re-pins the substrate (this is a PCB change, and it
moves the ARCHITECTURE substrate pin, so it is deliberately NOT done here):

1. add `ScaleValue` to PCB's `BuiltinFun`;
2. add `(100, .ScaleValue)` to `builtinTable`
   (`PlutusCore/UPLC/FlatEncoding/Basic.lean`) and `"scaleValue" => some
   .ScaleValue` to the text decoder (`PlutusCore/UPLC/TextEncoding/Basic.lean`,
   next to the existing six at :403-408);
3. implement the denotation next to the other Value builtins
   (`PlutusCore/UPLC/BuiltinFunctions/Value.lean`), plus a cost-model entry;
4. re-pin `lakefile.lean` + `lake-manifest.json` to the new PCB revision and
   re-run this document's §6.

**RESOLUTION (task N5).** All four steps were carried out in PlutusCoreBlaster
`3fdd3fb` (on top of `9f9ca8c`), and the CLAB substrate pin moved with them. The
three seize rows in §2/§3 are now real two-sided measurements.

Two things worth recording that the fix recipe above did not anticipate:

* **The tag is confirmed on both sides of `instance Flat DefaultFun`**, read off
  the source rather than inferred. N2 cited plutus-core 1.63 line numbers; the
  local `/home/gumbo/iohk/plutus` checkout is **1.57**, where the same pair sits
  at `:2177`/`:2281`. Both agree the tag is 100. (N1 reported that no plutus
  source was on this machine; it is — 1.63.0.0 is in the nix store, as a source
  tarball, and that is what the coefficients below were read from.)

* **A second, INDEPENDENT defect surfaced the moment seize could be metered**,
  and it was NOT a ScaleValue problem. With `ScaleValue` costed correctly,
  seize-1-input still disagreed with the ledger by +1,725,250 CPU and −120 mem.
  Cause: `unValueData` and `valueData` carried plutus-core **1.57** coefficients
  in a table that is otherwise **1.63**:

  | builtin | PCB (1.57) | plutus 1.63 |
  |---|---|---|
  | `unValueData` CPU | `1000 + 204904·x + x²` | `1000 + 95933·x + x²` |
  | `unValueData` MEM | `11 + 1·x` | `1 + 11·x` (intercept/slope SWAPPED) |
  | `valueData` CPU | `199604 + 39211·x` | `1000 + 38159·x` |

  A full parameter diff of 1.57C against 1.63E shows exactly SEVEN builtins
  moved between the releases (`divideInteger`, `equalsByteString`, `modInteger`,
  `quotientInteger`, `remainderInteger`, `unValueData`, `valueData`); PCB already
  had the 1.63 values for the first five, so only the two CIP-153 entries added
  in `830819b` were stale.

  The arithmetic closes exactly, which is what makes this a diagnosis rather
  than a guess. seize-1-input calls `unValueData` twice and `valueData` once
  (`x = 1`), traced. From the MEMORY discrepancy alone,
  `20 − 10·(n₁+n₂) = −120` gives `n₁+n₂ = 14`; substituting into the CPU model
  predicts `108971·14 + 199656 = 1,725,250` — the observed CPU discrepancy, to
  the unit.

  **Why no golden caught it earlier:** the builtin census in the table above is a
  STATIC scan of the term. `programmableLogicGlobal` references `unValueData`
  and `valueData` but never EXECUTES them on the paths its four golden contexts
  take, so its budgets agreed with the ledger regardless. The post-#112 seize
  goldens are the first that run them. This is a good argument for keeping the
  ExBudget cross-check on every golden rather than on a sample.

## 8. Reproduce

```
# 1. regenerate the goldens from wsc-poc main (see WSC/goldens/MANIFEST.md)
cabal --project-dir=<wsc-poc-worktree> build golden-dump --extra-lib-dirs=/usr/local/lib
<worktree>/dist-newstyle/.../golden-dump generated/scripts/unapplied/prod \
    <CLAB>/WSC/goldens <CLAB>/WSC/goldens/applied

# 2. K
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-n2
sed 's|/home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens/applied|<CLAB>/WSC/goldens/applied|g' \
    <CLAB>/WSC/goldens/KMeasure.lean.disabled > <SCRATCH>/pcb-n2/KMeasureN2.lean
cd <SCRATCH>/pcb-n2 && lake env lean KMeasureN2.lean

# 3. applied-flat fidelity
sed '…same path rewrite…' <CLAB>/WSC/goldens/KVerify.lean.disabled > <SCRATCH>/pcb-n2/KVerifyN2.lean
cd <SCRATCH>/pcb-n2 && lake env lean KVerifyN2.lean > kverify.log
python3 <CLAB>/WSC/goldens/verify-applied.py kverify.log <CLAB>/WSC/goldens

# 4. the builtin census behind §7 (scratch driver in the wsc-poc worktree)
cabal --project-dir=<worktree> build builtin-scan --extra-lib-dirs=/usr/local/lib
<worktree>/dist-newstyle/.../builtin-scan generated/scripts/unapplied/prod
```

---
---

# ⛔ EVERYTHING BELOW IS SUPERSEDED (pre-PR-#112, wsc-poc `f918ec6`)

The document that follows was current for the goldens dumped from wsc-poc
`f918ec6`. It is kept verbatim because the deltas in §3 above are only
meaningful against it, and because its §4-§5 prep-cost analysis (symbolic
`#prep_uplc` cost as a function of budget) is about Blaster, not about wsc-poc,
and is therefore **still valid** — only the K numbers it quantifies over moved.
Its section numbers are its own and do not continue the numbering above.

**Do not quote a K from below.** Use §2/§3.

---

# K-MEASUREMENTS — true CEK step counts of the 13 WSC golden runs (task X1)

Answers SPIKE-FINDINGS open issue 2 ("the minimum non-vacuous seize budget is
unknown — measure actual CEK steps of a concrete accepting run before choosing
K") and supplies the numbers ARCHITECTURE.md's `LR-BUDGET` axiom quantifies over.

**Headline. The four production validators halt in 208 - 5,079 CEK steps on real
golden transactions — four orders of magnitude below the ceiling we allowed for,
and the measurement itself costs 3 ms per golden. So the numbers are small and
cheap to get; the bad news is on the other side of the ledger. Symbolic
`#prep_uplc` cost is driven by the BUDGET, and it grows exponentially with a
measured marginal doubling every ~113 budget steps — then hits a cliff
(seize: 19 s at budget 900, never completes at 2,000). Consequently:
base is proved and comfortable (K = 208, prep 600 = 11 s); minting has a genuinely
affordable non-vacuous budget (K_novac = 784, prep ≈ 20 s) and should be attacked
next; global's cheapest accept (1,554) is affordable at 26–36 min of prep — and
that accept is the covering-node scenario, i.e. exactly P5's subject, so P5 at
UPLC is newly within reach; while seize (3,002) and the containment-carrying
global transfers (3,262 / 3,726) are out of reach by 3 to 9 orders of magnitude,
so P2 and P1 cannot be done this way. The blocker was never the
validators' step counts — it is symbolic-prep cost as a function of budget.**

---

> ## ⛔ CORRECTION NOTICE (task A1, 2026-07-25) — read before quoting ANY prep cost
>
> **AMENDED BY TASK C3, 2026-07-25 — §3's step counts were NOT all unaffected.**
> The sentence that stood here ("§3's CEK step counts are correct and unaffected")
> was true when written of the vectors then on disk, and is FALSE of the vectors on
> disk now: the wsc-poc builder fix (positive fee, ledger-ordered withdrawals,
> min-ada on every output) re-dumped every golden and every applied flat, and
> **4 of the 13 rows moved**. §3 is corrected in place from a fresh run of
> `KMeasure.lean` against the current `WSC/goldens/applied/*.flat` (Appendix A′);
> the superseded run is retained verbatim as Appendix A. The moved rows are
> `seize-1-input` 2,570 → **3,002**, `seize-2-inputs-partial-with-noise`
> 4,647 → **5,079**, `seize-1-input-missing-residual-output-REJECT`
> 1,938 → **2,261**, `transfer-containment-violation-REJECT` 2,970 → **2,737**
> (the only one that went DOWN). The other 9 rows reproduce to the unit.
>
> The audit's finding **F13** flagged the two ACCEPTING seize rows; it did not
> flag the two REJECTING rows, which this re-measurement adds.
>
> **The cross-check still holds, and it is the reason to trust the new numbers:**
> PCB's own metered budget equals the ledger's `ExBudget` in the golden JSON
> exactly, for all 9 accepting goldens, on the CURRENT vectors — including
> `60,231,630 / 163,820` and `105,501,594 / 274,735` for the two seize rows.
>
> **§5.1's PREP-COST table is wrong by 6–58×, and so is every prep-cost figure in
> the headline paragraph above** ("prep 600 = 11 s", "prep ≈ 20 s", "26–36 min",
> "3 to 9 orders of magnitude"). The measurements were taken with `lake env lean`
> **without `--load-dynlib`**, so Blaster and PlutusCoreBlaster ran interpreted
> rather than native. The authoritative, re-measured table is **§5.1a**: base 600 =
> **1.35 s**, minting 900 = **1.53 s**, global 1600 = **37.8 s** (published as
> 2,143 s = 35.7 min). The U3 audit recorded this as finding **F5**, having seen it
> cause a task to skip half the library's build.
>
> §5.2 and §5.3's per-validator VERDICTS and every extrapolation in §5 are anchored
> on the superseded figures. Their structural conclusions stand; their costs do not.
> **Measure with `lake build` before concluding that anything is unaffordable.**
>
> Also note what has made the whole question less load-bearing: task A1 restated
> `WSC/Honest.lean`'s four `LR_BUDGET_*` axioms against `Runs.XRun K`
> (`WSC/Runs.lean`), which needs no `#prep_uplc` at all, so the ledger-side bridges
> now exist at 2500 / 3300 / 3800 / 4400 — budgets §5 correctly reported as beyond
> any affordable unshaped prep. The prep wall still binds the SHAPED preps the
> P-theorems are stated over.

---

## 1. Method

Measured on the FULLY APPLIED goldens `WSC/goldens/applied/*.flat` — the
production unapplied script with all script parameters AND the golden
`ScriptContext` baked in as `Data` constants (Plutarch `applyArguments`), i.e.
CLOSED, zero-argument programs. This is therefore **concrete** CEK evaluation,
not symbolic execution.

* Runner: `WSC/goldens/KMeasure.lean.disabled` (the `.disabled` suffix keeps
  `lake` out of it; it is NOT part of any `lean_lib` here).
* Workspace: `<SCRATCH>/pcb-kmeasure`, a `cp -a` of
  `/home/gumbo/iohk/PlutusCoreBlaster` at branch `cip153-value-builtins`
  @ `9f9ca8c` (warm `.lake`; `lake build PlutusCore` replayed 284 jobs in 2.9s),
  with `<SCRATCH>` =
  `/tmp/claude-1000/-home-gumbo-iohk-wsc-poc/7ad8fab7-3c95-4aef-a618-398aa216c728/scratchpad`.
  A copy is used only to avoid `.lake` lock contention with the agent that owns
  this repo's build.
* Command: `cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean`
  → **all 13 measurements in 3.2 s wall** (each `count_ms` ≤ 3 ms). No
  bisection was necessary and nothing came close to the 10-minute per-run
  ceiling the task allowed for.

`countSteps` iterates the real `PlutusCore.UPLC.CekMachine.step` — the very
function `runSteps` / `cekExecuteProgram` / `#prep_uplc` consume — to the
terminal state, counting applications. Because `runSteps`
(`PlutusCore/UPLC/CekMachine.lean:229-241`) returns a terminal state as-is and
turns fuel-0 into `State.Error` only in a NON-terminal state, that count is
exactly the minimal `runSteps`/`#prep_uplc` budget at which the run's outcome
appears.

**Budget starvation vs. genuine evaluation `Error` (the trap the task flags).**
Three independent guards:
1. `countSteps` reaches `.error` only by APPLYING `step` while fuel remains;
   running out of fuel is a distinct `.fuelOut` outcome — which never fired
   (ceiling 50,000,000 steps, i.e. ≥ 10,000× every measured K).
2. For every golden, `runSteps @ K` and `runSteps @ K-1` were executed:
   accepting goldens give `Halt` / `Error`, rejecting goldens `Error` / `Error`.
3. Every rejecting golden was re-run at `10 × K` and still gives `Error` —
   the "same Error at 10× the budget" test the task asks for.

---

## 2. Fidelity evidence (why these numbers describe the real chain)

1. **Byte-exact arguments.** `WSC/goldens/KVerify.lean.disabled` walks each
   applied program's `Apply` spine, checks every argument is a `Const (Data …)`,
   and re-serialises it with PCB's CBOR encoder (`PlutusCore.Cbor.encodeData`,
   the `serialiseData` builtin). `WSC/goldens/verify-applied.py` diffs those
   hexes against the golden JSONs → **ALL-MATCH for all 13**: after the script's
   own top-level `Force`/let application (spine arg 0, part of the compiled
   script, not a user argument) the arguments are exactly
   `paramsHex… ++ [scriptContextHex]`, in the documented application order, with
   the expected arity (base/minting 2 params + ctx; seize/global 1 param + ctx).
   Spine heads are `Lam`, and no applied program is a bare top-level lambda
   awaiting arguments.
2. **Byte-exact cost.** PCB's own budget-metered run of the same applied program
   (`cekExecuteProgramWithBudget … .plutusV3 .postConway`) reproduces the ledger
   `ExBudget` recorded in the golden JSONs **exactly — all 9 accepting goldens,
   CPU and memory, to the unit** (see table). Those JSON figures came from
   Haskell `PlutusLedgerApi.V3.evaluateScriptCounting` at PV11. Two independent
   evaluators (Lean CEK + PCB cost model vs. plutus-ledger-api 1.63) agreeing to
   the unit on 9 programs is strong evidence that (a) the flat decode is faithful,
   (b) the baked-in ctx is the golden ctx, and (c) PCB's CEK is step- and
   cost-exact against the reference machine on this code.
3. **The measured K is the same unit as a `#prep_uplc` budget, applied to the
   same term shape.** `#prep_uplc … n` elaborates to
   `cekExecuteProgram prog (inputsFn args) n` with `n` a raw `Nat`
   (`PlutusCore/UPLC/PreProcess.lean:143-153`), and `cekExecuteProgram` is
   `runSteps ∘ initialState ∘ applyParams` — the same counter this task
   measures. Crucially the ARGUMENT SHAPE also matches: CLAB's
   `spendingInputs`/`mintingInputs`/`rewardingInputs` return exactly
   `[toTerm ctx]` (`CardanoLedgerApi/V3/Contexts.lean:676-691`) and
   `toTerm x = Term.Const (Const.Data (toData x))`
   (`CardanoLedgerApi/IsData/Class.lean:56`) — a SINGLE `Const` node, exactly as
   in the applied flats, with only the `Data` payload symbolic. So a symbolic
   prep does not pay extra steps to *build* the context, and the path
   corresponding to one of these goldens consumes exactly K steps inside it.
   That is what makes the verdict in §5 a valid comparison rather than an
   analogy.
4. **Uniform CPU-per-step.** 18,132–21,759 CPU units per CEK step and
   54.1–56.3 memory units per step across all four validators and all nine
   accepting goldens — the ratio does not drift, so K is a genuine measure of the
   same machine the ledger meters.

---

## 3. The 13 goldens

`K` = minimal CEK step budget at which the outcome appears (= exact step count of
the run). ExBudget columns are the ledger's, from the golden JSONs (testing cost
model, see MANIFEST.md); `PCB budget` is PCB's own metered run of the applied
program.

| golden | accepts | outcome @K | **K (CEK steps)** | ExBudget CPU | ExBudget mem | PCB budget = ledger? | CPU/step | mem/step |
|---|---|---|---|---|---|---|---|---|
| programmableLogicBase.base-spend-transfer-tx | yes | Halt | **208** | 4,525,794 | 11,715 | **exact** | 21,759 | 56.3 |
| programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT | no | Error | 286 | — | — | n/a | — | — |
| programmableTokenMinting.mint-burnonly | yes | Halt | **784** | 14,215,312 | 43,421 | **exact** | 18,132 | 55.4 |
| programmableTokenMinting.mint-delegate-transfer-topup | yes | Halt | **1,257** | 26,455,938 | 69,372 | **exact** | 21,047 | 55.2 |
| programmableTokenMinting.mint-local-registered-by-ref | yes | Halt | **1,681** | 34,116,362 | 92,870 | **exact** | 20,295 | 55.2 |
| programmableTokenMinting.mint-local-empty-withdrawals-REJECT | no | Error | 1,627 | — | — | n/a | — | — |
| programmableSeize.seize-1-input | yes | Halt | **3,002** | 60,231,630 | 163,820 | **exact** | 20,064 | 54.6 |
| programmableSeize.seize-2-inputs-partial-with-noise | yes | Halt | **5,079** | 105,501,594 | 274,735 | **exact** | 20,772 | 54.1 |
| programmableSeize.seize-1-input-missing-residual-output-REJECT | no | Error | 2,261 | — | — | n/a | — | — |
| programmableLogicGlobal.transfer-nonmember-covering-node | yes | Halt | **1,554** | 29,160,036 | 86,035 | **exact** | 18,765 | 55.4 |
| programmableLogicGlobal.transfer-member-single-policy | yes | Halt | **3,262** | 62,665,145 | 177,810 | **exact** | 19,211 | 54.5 |
| programmableLogicGlobal.transfer-mixed-many-policies | yes | Halt | **3,726** | 78,031,424 | 204,737 | **exact** | 20,942 | 54.9 |
| programmableLogicGlobal.transfer-containment-violation-REJECT | no | Error | 2,737 | — | — | n/a | — | — |

Halt values are `VCon`s (the `PUnit` result); applied-program node counts are 145
(base), 1,285 (minting), 1,976 (seize), 3,448 (global) — identical within a
validator family because each whole `Data` argument is a single `Const` node.

Rejecting goldens error at 286 / 1,627 / 2,261 / 2,737 steps, i.e. BEFORE their
accepting siblings finish — as expected for early-exit condition failures — and
they stay `Error` at 10× budget.

---

## 4. Per-validator K for `LR-BUDGET`

Two DIFFERENT numbers, with different jobs. Conflating them is the single
easiest way to publish a vacuous theorem:

* **K_novac (non-vacuity floor)** = MIN over accepting goldens. A prep at budget
  ≥ K_novac provably admits an accepting run (we have the concrete witness), so
  the mandatory vacuity probe will be Falsified. Below it, every `accept → …`
  theorem is vacuous.
* **K_cover (coverage ceiling)** = MAX over accepting goldens × margin. This is
  what `LR-BUDGET_v` must quantify over if the bounded-transaction theorem is to
  cover the transaction shapes the goldens represent.

| validator | K_novac (witness) | K_max (accepting goldens) | K_cover ×1.5 | K_cover ×2 | prep budget in use today |
|---|---|---|---|---|---|
| programmableLogicBase | **208** (base-spend-transfer-tx) | 208 | 312 | 416 | **600 — covers it (2.9× K_max); P3 PROVED, non-vacuous** |
| programmableTokenMinting | **784** (mint-burnonly) | 1,681 | 2,522 | 3,362 | 600 — no accepting witness within it (600 < K_novac = 784) |
| programmableSeize | **3,002** (seize-1-input) | 5,079 | 7,619 | 10,158 | 600/1,000 — VACUOUS, measured (spike vacuity probes returned Valid) |
| programmableLogicGlobal | **1,554** (transfer-nonmember-covering-node) | 3,726 | 5,589 | 7,452 | 600 — VACUOUS, measured (`Prep/Global.lean`'s own probe) |

Caveat, stated precisely: K_novac is an UPPER bound on the true minimum
accepting budget of each validator (a hand-minimised accepting ctx could halt in
fewer steps; e.g. base's bootstrap witness in Props/P3_Base.lean accepts inside
600 and the golden needs only 208). It is exactly what a non-vacuity claim needs
— a witness — not a lower bound on the threshold. K_cover, conversely, covers
only transactions no bigger than these goldens: seize/global cost scales with
input/output/policy counts (seize 1→2 inputs: 3,002→5,079; global 1→5 policies:
3,262→3,726), so a K_cover chosen for a 2-input seize says NOTHING about a
10-input seize. ARCHITECTURE.md's per-shape/bounded-transaction stance is
therefore mandatory, and any published K must name the shape it covers.

---

### 4.1 Consequences for `Honest.lean`'s LR-BUDGET axioms (actionable, not mine to edit)

`WSC/Honest.lean:354-372` currently states the three axioms as
`∃ K : Nat, 0 < K ∧ ∀ …, OnChain ctx → txSize ctx ≤ K → (NodeAccepts… ↔ isSuccessful …)`.
Two mismatches with ADDENDUM E1 ("K is per-validator and must be computed and
published, empirically calibrated with concrete accepting ctxs run through
`cekExecuteProgram`") that these measurements now let you fix:

1. **The bound is on the wrong quantity.** E1's bound is on CEK STEPS; `txSize`
   is a proxy whose relation to step count is unproven. The measurements give the
   step counts directly — state the hypothesis as `cekSteps ctx ≤ K` (or keep
   `txSize` only if a `txSize → steps` bound is separately established; the
   observed 18.1k–21.8k CPU/step gives the ExBudget side of that bridge, not the
   size side).
2. **`∃ K` should be a published constant.** An existential K makes the axiom
   unusable for auditing (nothing pins which transactions are covered) — and it
   is precisely the sort of clause a reviewer will read as "any K, including a
   vacuous one". Replace with the concrete numbers in §4:
   `K_base = 416`, `K_minting = 3362`, `K_seize = 9294`, `K_global = 7452`
   (max accepting golden × 2), each annotated with the shape it was calibrated on
   and the non-vacuity witness that keeps it honest.
3. The docstrings at `Honest.lean:360` and `:367` say "budget 2000" / "budget
   9000" for minting / seize, but `WSC/Prep/Minting.lean` and
   `WSC/Prep/Seize.lean` both prep at 600. Whatever budgets end up being used,
   those comments must be regenerated from the prep modules, and per §5 the 2000
   / 9000 figures are not achievable with fully symbolic contexts anyway.

---

## 5. THE VERDICT — can a NON-VACUOUS symbolic `#prep_uplc` be reached?

### 5.1 The measured prep-cost wall

> ## ⛔ THE TABLE IMMEDIATELY BELOW IS **SUPERSEDED**. SEE §5.1a.
>
> Every figure in the "ORIGINAL (task X1)" table is **6–58× too large** on the
> current substrate, and the error is not uniform, so no scaling factor rescues it.
> It is retained ONLY as the historical record of how the wall was first found.
>
> **CAUSE** (two components, neither of them a property of `#prep_uplc`):
> 1. the measurements were taken with **`lake env lean` on a prep-only file,
>    WITHOUT `--load-dynlib`**, so the Blaster / PlutusCoreBlaster compiled code
>    ran in the Lean **interpreter** instead of as native code. `lake build`
>    supplies the dynlibs; `lake env lean` does not. This is the dominant term.
> 2. a substrate bump since X1 (`Blaster` `beta-lambda-cache-optimization`, plus
>    the CIP-153 `Value` builtins in the pinned PlutusCoreBlaster).
>
> **THIS COST REAL WORK, which is why the warning is this loud.** Task U2 declined
> to build `WSC/Props/P1_Transfer.lean`, `WSC/Props/P5_NonMember.lean` and the
> ENTIRE shaped layer, citing "a 35.7-min `#prep_uplc`" from the row below, and
> shipped edits validated against a partial build. The U3 audit recorded this as
> finding **F5 (MEDIUM)**. The real figure for that module is **37.8 s**.
>
> **RULE: never conclude that a budget is unaffordable from this table. Measure it
> with `lake build` first.** The one conclusion of §5.1–§5.3 that the re-measurement
> does NOT overturn is the SHAPE of the curve (exponential in the budget, with a
> cliff) and the non-completions, which were real timeouts.

#### ORIGINAL (task X1) — SUPERSEDED, DO NOT QUOTE

Symbolic `#prep_uplc` cost is driven by the BUDGET (the symbolic unrolling
depth), and it grows explosively. Nine fresh measurements were taken for this
task, on the same box that produced SPIKE-FINDINGS (32 cores, 61 GB, Lean 4.24.0,
Z3 4.15.2, `maxHeartbeats 0`, `lake env lean` on a prep-only file, warm `.lake`;
in a `cp -a` of this repo at `<SCRATCH>/clab-prep` with the PlutusCore dep
repointed at `<SCRATCH>/pcb-kmeasure`; probe sources in
`WSC/goldens/prep-probes/`):

| validator | budget | prep wall (SUPERSEDED) | source |
|---|---|---|---|
| programmableTokenMinting | 600 | **11.1 s** | this task (`prep-probes/Mint600`) |
| programmableTokenMinting | 900 | **27.6 s** | this task |
| programmableTokenMinting | 1,200 | **131.6 s** | this task |
| programmableTokenMinting | 1,700 | **never completed — killed at 48.6 min** | this task |
| programmableLogicGlobal | 600 | **11.8 s** | this task (CIP-153 builtins) |
| programmableLogicGlobal | 900 | **24.3 s** | this task |
| programmableLogicGlobal | 1,600 | **2,143 s = 35.7 min** (completed; max RSS 1.55 GB) | this task |
| programmableSeize | 600 | **12.7 s** | this task (11.1 s in SPIKE-FINDINGS) |
| programmableSeize | 900 | **19.4 s** | this task |
| programmableSeize | 2,000 | never completed (>29 m, then >77 m) | SPIKE-FINDINGS |
| programmableSeize | 9,000 | never completed (>62 m) | SPIKE-FINDINGS |
| governance (repo precedent) | 9,000 | never completed (>29 m) | SPIKE-FINDINGS |

### 5.1a RE-MEASURED (task A1, 2026-07-25) — **THIS is the authoritative table**

Method, so it is reproducible in one loop. In a `cp -a` of the repo at
`<SCRATCH>/clab-A1` (branch `wsc-containment-proofs`), for each prep module:

```
rm -f .lake/build/lib/lean/WSC/Prep/<M>.olean .lake/build/lib/lean/WSC/Prep/<M>.ilean \
      .lake/build/lib/lean/WSC/Prep/<M>.trace .lake/build/lib/lean/WSC/Prep/<M>.*.hash
/usr/bin/time -f '%e %M' lake build WSC.Prep.<M>
```

Each row is therefore a **cold re-elaboration of exactly one module** (confirmed
per row by lake's `Built WSC.Prep.<M> (Ns)` line and by the
`Successfully decoded double CBOR hex …` message reappearing), with dependency
oleans warm, `--load-dynlib` supplied by `lake`, and nothing else competing.
Wall time includes ≈0.4 s of `lake` overhead. Same box, Lean 4.24.0,
Z3 4.15.2, `maxHeartbeats 0`.

| module | validator | budget | prep wall | max RSS | ORIGINAL figure | overstated by |
|---|---|---|---|---|---|---|
| `WSC.Prep.Base` | programmableLogicBase | 600 | **1.35 s** | 1.20 GB | "≈11 s class" | ≈8× |
| `WSC.Prep.Minting` | programmableTokenMinting | 600 | **1.15 s** | 1.21 GB | 11.1 s | 9.7× |
| `WSC.Prep.Minting800` | programmableTokenMinting | 800 | **1.34 s** | 1.21 GB | (≈20 s, extrapolated) | ≈15× |
| `WSC.Prep.Minting900` | programmableTokenMinting | 900 | **1.53 s** | 1.21 GB | 27.6 s | 18× |
| `WSC.Prep.Minting1300` | programmableTokenMinting | 1,300 | **5.31 s** | 1.28 GB | 131.6 s @1,200 | ≈25× |
| `WSC.Prep.Seize` | programmableSeize | 600 | **1.25 s** | 1.21 GB | 12.7 s | 10× |
| `WSC.Prep.Global` | programmableLogicGlobal | 600 | **2.00 s** | 1.25 GB | 11.8 s | 5.9× |
| `WSC.Prep.Global1600` | programmableLogicGlobal | 1,600 | **37.8 s** (36.6 s in a second run) | 1.66 GB | **2,143 s = 35.7 min** | **57×** |

Independent cross-check: the U3 clean-room rebuild of all 63 WSC modules measured
`WSC.Prep.Global1600` at **44 s**, higher than the 37.8 s here because that build
was running 30+ other modules in parallel. Both falsify 2,143 s.

WHAT THE RE-MEASUREMENT DOES **NOT** CHANGE:

* the CURVE is still exponential in the budget with a cliff — 600 → 1,600 is
  1.15 s → 37.8 s for minting/global-class scripts, i.e. ×2 per ≈150 budget steps
  in this range;
* every **non-completion** in the original table was a real timeout and is not
  re-measured here (minting @1,700 killed at 48.6 min; seize @2,000 >77 min;
  seize @9,000 >62 min). They are 1.5–2× further up an exponential from a point
  that now costs 5–38 s, so they may well be affordable today — **that is an
  untested hypothesis, deliberately not asserted.** Nobody should conclude a
  budget is reachable from this table either;
* §5.2/§5.3's per-validator verdicts and the extrapolations below are anchored on
  the SUPERSEDED numbers and are therefore ALSO unreliable as costs. Their
  structural conclusions (base is trivial, minting's cheap end is in hand, global
  splits, seize's fully-symbolic route is the hardest) are unaffected.
* **most important: none of this matters for the campaign's ledger bridges any
  more.** Task A1 restated `WSC/Honest.lean`'s four `LR_BUDGET_*` axioms against
  `Runs.XRun K` (`WSC/Runs.lean`) — the imported flat under a `K`-step meter, a
  plain Lean definition with NO `#prep_uplc` and hence NO prep cost at ANY budget.
  The budgets this table said were out of reach (2500, 3300, 3800, 4400) now carry
  published `K` constants with PROVED non-vacuity theorems. The prep wall still
  binds the SHAPED `#prep_uplc`s the P-theorems are stated over — which is why
  shaping exists (shaped prep is essentially budget-independent, ≈1 s at 4400,
  SHAPING-RESULTS §2.5).

Three facts fall out of the ORIGINAL table (the ratios below are computed from the
superseded figures; the qualitative claims survive, the absolute costs do not):

* **Prep cost is driven by the budget, NOT by script size.** At 600: minting
  11.1 s, global 11.8 s, seize 12.7 s. At 900: seize 19.4 s, global 24.3 s,
  minting 27.6 s. Those scripts are 1,285 / 3,448 / 1,976 nodes and global
  additionally carries the CIP-153 `Value` builtins, yet the spread at a fixed
  budget is under 1.5×. Budget is the control variable; the four validators are
  interchangeable to within a small factor.
* **There is a fixed ≈8 s floor plus an exponential term.** Fitting the three
  minting points to `t = c₀ + A·e^{s·b}` gives an exact solution
  c₀ = 7.96 s, ratio ×6.29 per +300 steps, **s = 0.00613 /step — the marginal
  cost doubles every 113 budget steps**. (600→900 and 900→1,200 in raw terms:
  ×2.5 then ×4.8.)
* **The slope STEEPENS, so every fit is optimistic.** Global's slope goes from
  0.00482 /step (600→900) to **0.00696 /step (900→1,600) — doubling every 100
  steps**. Minting @1,700 was predicted at 39–44 min by its own 600–1,200 fit and
  did not finish in **48.6 min**. Seize is the extreme case: its 600→900 slope
  (0.00294) predicts @2,000 ≈ 5 min, but the measured @2,000 never completed in
  77 minutes — ≥ 15× the fit. Somewhere between 900 and 2,000 the symbolic
  execution crosses into path-explosion on symbolic `Data` (SPIKE-FINDINGS:
  fixing list spines does not help, because redeemer/datum/mint fields stay
  symbolic). **Treat every extrapolation below as a LOWER BOUND on cost**, and
  note the practical ceiling observed here: budgets of 1,600–1,700 cost 36–>49
  minutes, and nothing above ~2,000 has ever completed for any WSC validator.

Extrapolation used in the verdict, each validator anchored on its own STEEPEST
measured slope (`t = 8 + A·e^{s·b}`; minting s = 0.00614, global s = 0.00696,
seize taken as global's since seize's own 600→900 slope is empirically refuted by
its @2,000 non-completion):

| target budget | why | smooth-fit cost (lower bound) | measured reality nearby |
|---|---|---|---|
| ~800 | minting K_novac = 784 | **≈ 20 s** | bracketed by 600 = 11 s and 900 = 28 s — **affordable** |
| 1,554 | global K_novac | ≈ 26 min | **bracketed by the measured 1,600 = 35.7 min** |
| 1,681 | minting K_max | ≥ 45 min | **1,700 measured: did NOT finish in 48.6 min** |
| 2,522 | minting K_cover ×1.5 | ≥ 4.8 days | — |
| 2,570 | seize K_novac (**now 3,002** — C3) | ≥ 15 days | seize @2,000 already >77 min, never completed |
| 3,262 / 3,726 | global K_max (P1's real shapes) | ≈ 7 y / 182 y | — |
| 6,971 | seize K_cover ×1.5 (2-input seize) | astronomical | — |

### 5.2 Per-validator verdict

**programmableLogicBase — (a) ALREADY DEMONSTRATED.** K_novac = K_max = 208; the
prep in use is 600, i.e. 2.9× the golden's whole run, and P3 is proved
non-vacuously there (`WSC/Props/P3_Base.lean`, prep 11 s class). Nothing to fix.
Headroom exists for a bigger base prep if some future property needs it
(600 → 900 costs ~28 s).

**programmableTokenMinting — (b) PLAUSIBLY REACHABLE, and the cheap end is
essentially in hand.** A non-vacuous prep needs only ≥ 784 (mint-burnonly), which
sits between the measured 600 (11.1 s) and 900 (27.6 s) → **~20 s: affordable
today**. That budget yields a genuinely non-vacuous P4-class theorem, but one
whose scope is "burn-only-sized minting transactions". Covering all three minting
goldens needs 1,681 (smooth-fit ≈ 39 min; the measured 1,700 run did not finish in
48.6 min — CI-hostile
even in the good case, and only tolerable because `WSC/Prep/*` caches each prep in
its own module), and `K_cover ×1.5 = 2,522` is ≥ 4.7 days — out of reach. **Recommendation:
raise `Prep/Minting.lean` from 600 to ~800–900 and prove P4 there, with the
scope stated as "minting runs halting within 900 steps" and mint-burnonly as the
non-vacuity witness.**

**programmableLogicGlobal — SPLIT VERDICT: (b) REACHABLE for the covering-node
(P5) shape, at 26–36 min of prep; (c) OUT OF REACH for the containment (P1)
shapes by 5–9 orders of magnitude.** K_novac = 1,554 — and that cheapest accept is
`transfer-nonmember-covering-node`, i.e. exactly the scenario ADDENDUM E3 makes
P5's subject ("P5's postcondition is the covering-node witness"). Global prep at
1,600 was MEASURED at 35.7 min / 1.55 GB and completed, so a non-vacuous global
prep covering that shape is genuinely available today as a one-off cached
elaboration — **this is the one new "yes" this measurement unlocks beyond base.**
What it does NOT cover is P1: the containment-carrying member accepts cost 3,262
and 3,726 steps, extrapolating (on global's own steepest measured slope) to ≈ 7
years and ≈ 182 years of prep. **P1 at UPLC over a fully symbolic ctx is dead.**
The CIP-153 `valueContains` route does not rescue it: prep cost is budget-driven,
and the builtin only lowers the ON-CHAIN step count (already counted in §3), not
the symbolic unrolling of the rest of the validator.

**programmableSeize — (c) OUT OF REACH BY ORDERS OF MAGNITUDE.** The smallest
accepting seize run is **3,002** steps (2,570 on the pre-fix vectors this
section's fit was written against; the conclusion moves further out, not in). Symbolic prep at 2,000 already never
completed in 77 minutes (≥ 15× above the smooth fit for seize, which is how we
know about the cliff); 3,002 is ≥ 15 days on global's measured slope and realistically
unbounded, and the ×1.5 coverage budget 7,619 is astronomical. Every "seize accept ⟹ …" theorem at any prep budget we
can afford (≤ ~1,000) is provably vacuous — which is exactly what the spike's
vacuity probes at 600/1,000 reported. **P2 over a fully symbolic ScriptContext is
dead at UPLC level**; it needs either shaped contexts with concrete
redeemer/spines (and the spike showed shaped-at-9,000 also never completed, so
shaping must be aggressive: concrete indices AND concrete `Data` scalars), or the
source-model (B3) route.

### 5.3 What this means for the remaining plan

1. **P3 (base) stays the keystone**, and its architectural weight increases: it
   is what forces global/seize to run at all, and it is the only property provable
   over a fully symbolic context at trivial cost.
2. **Move minting up the queue.** Non-vacuous at ~800 for ~20 s of prep — the
   cheapest new UPLC result available. Do it before any further seize/global
   attempt.
3. **Take the one global win that is affordable: P5 at budget ~1,600
   (35.7 min, measured, cached).** The covering-node accept (1,554 steps) is both
   the non-vacuity witness and P5's own subject shape, so P5-at-UPLC is
   reachable — the single most valuable newly-unlocked target. Budget CI for a
   ~40-minute prep in its own module, and do NOT attempt to widen that prep
   toward the member-transfer accepts (3,262+) in the same file.
4. **Stop spending time on fully-symbolic seize preps and on any global prep
   above ~1,700.** The wall is
   exponential-plus-cliff and we are 1.6–2.7× in budget away from the
   non-vacuity floor — which at ~113 steps per doubling is 10–16 doublings, i.e.
   3–5 orders of magnitude in time. Redirect to (i) shaped/partially-concrete
   contexts with measured per-shape K — the numbers in §3 are exactly the
   per-shape budgets to use (3,002 for 1-input seize, 3,262 for single-policy
   transfer, …) — and/or (ii) the source-model route for P1/P2 with a separately
   argued compilation-fidelity bridge.
5. **The LR-BUDGET axiom is now quantitative.** For each validator, state
   `LR-BUDGET_v` as "a real node run of v on a transaction of shape S halts in
   ≤ K_v(S) CEK steps", with K_v(S) taken from §3 × margin, and record that the
   ledger's own ExBudget for those runs is 4.5M–105.5M CPU (≈ 20k CPU/step) —
   i.e. all of the goldens sit far inside the 10^10 CPU per-tx mainnet limit, so
   the axiom is not a hidden restriction on realistic transactions of that shape.
   A prep-side speedup (memoized/opaque recursive-CEK abstraction in Blaster,
   SPIKE-FINDINGS verdict (c)) is the only thing that would change the verdict
   for seize/P1; the required improvement is ≈3 orders of magnitude for seize
   non-vacuity (15 days → 40 min) and 6–9 orders for P1's member-transfer accepts.

---

## 6. Reproduction

Probe files as committed: `prep-probes/{Mint600,Mint900,Mint1200,Mint1700,Global600,Global900,Global1600,Seize600,Seize900}.lean.disabled`
(each is `WSC/Prep/<V>.lean` with a renamed namespace/defs, `set_option
maxHeartbeats 0`, and the prep budget changed; the Global ones drop the trailing
vacuity probe so only the prep is timed). Drop them into a `PrepProbe/`
directory of the CLAB copy, without the `.disabled` suffix.

```
# K measurement + minimality/genuine-Error confirmation (3.2 s)
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure   # git log -1 == 9f9ca8c
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# applied-flat argument fidelity (byte-exact vs the golden JSONs)
cp WSC/goldens/KVerify.lean.disabled <SCRATCH>/pcb-kmeasure/KVerify.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KVerify.lean > /tmp/kverify.log
python3 WSC/goldens/verify-applied.py /tmp/kverify.log      # → ALL-MATCH

# prep-cost wall — §5.1's SUPERSEDED method.  DO NOT USE: `lake env lean` gets no
# --load-dynlib, so Blaster/PCB run interpreted and every figure is 6-58x too high.
cp -a <this repo> <SCRATCH>/clab-prep
#   in <SCRATCH>/clab-prep/lakefile.lean: repoint `require PlutusCore from` to
#   <SCRATCH>/pcb-kmeasure ; probes are WSC/goldens/prep-probes/*.lean.disabled
cd <SCRATCH>/clab-prep && /usr/bin/time -f "WALL=%e" timeout 3000 \
    lake env lean PrepProbe/Mint900.lean

# prep-cost wall — §5.1a's CORRECT method (task A1).  No probe files needed: time a
# cold re-elaboration of the real prep module with `lake build`, which supplies the
# dynlibs.  Confirm each row really re-elaborated by looking for lake's
# `Built WSC.Prep.<M> (Ns)` line, not `Replayed`.
cd <SCRATCH>/clab-A1
for m in Base Minting Minting800 Minting900 Minting1300 Seize Global Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.olean .lake/build/lib/lean/WSC/Prep/$m.ilean \
        .lake/build/lib/lean/WSC/Prep/$m.trace .lake/build/lib/lean/WSC/Prep/$m.*.hash
  /usr/bin/time -f "$m %e s %M KB" lake build WSC.Prep.$m > /dev/null
done
```

## 7. Open issues

1. Both `#eval!`-based files run under the Lean INTERPRETER (PCB has no
   `precompileModules`), so the wall times in §1 are worst-case; a native build
   would be faster still. Irrelevant at these K, relevant if someone measures a
   10^7-step program.
2. PCB's `runStepsWithBudget` carries a `sorry` in its `decreasing_by`
   (`PlutusCore/UPLC/CekMachine.lean:299`), hence `#eval!` rather than `#eval`
   for the budget cross-check. The step-count measurement itself does not touch
   it.
3. The exact ExBudget agreement (§2.2) is against the plutus-ledger-api 1.63
   **testing** cost model (MANIFEST.md). It proves machine/decoder fidelity, not
   that mainnet PV11 publishes those params.
4. Per-shape scaling of K is only sampled (2 points for seize, 3 for global).
   Before publishing per-shape K_cover values for the shaped-prep route, measure
   K on a small grid of shapes (inputs × policies × outputs) — the applied-flat
   pipeline makes this cheap (3 ms per measurement).
5. The prep-cost extrapolations are 2–3-point fits per validator with a
   STEEPENING slope, and both deep probes overshot their own fit (global 1,600:
   36 min vs 18 min predicted; minting 1,700: >48.6 min vs 39–44 min predicted).
   Treat every extrapolated column as a lower bound on cost, not a
   promise.

---

## Appendix A — verbatim output of `lake env lean KMeasure.lean` (task X1, **SUPERSEDED**)

**SUPERSEDED by Appendix A′ (task C3).** This run measured the PRE-BUILDER-FIX
applied flats. It is retained verbatim because four of its rows are quoted
throughout the repository and a reader must be able to see exactly what was
measured and when. Do not quote it: quote Appendix A′.

(`Successfully decoded double CBOR hex '<file>'` lines from the importer omitted;
one per golden, all 13 successful. Total wall 3.209 s.)

```
programmableLogicBase.base-spend-transfer-tx: K=208 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=145 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=4525794,mem=11715] | count_ms=0 confirm_ms=0 budget_ms=1
programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: K=286 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=145 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=0 confirm_ms=0 budget_ms=1
programmableTokenMinting.mint-local-registered-by-ref: K=1681 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=34116362,mem=92870] | count_ms=2 confirm_ms=0 budget_ms=4
programmableTokenMinting.mint-burnonly: K=784 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=14215312,mem=43421] | count_ms=1 confirm_ms=0 budget_ms=3
programmableTokenMinting.mint-delegate-transfer-topup: K=1257 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=26455938,mem=69372] | count_ms=0 confirm_ms=0 budget_ms=4
programmableTokenMinting.mint-local-empty-withdrawals-REJECT: K=1627 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1285 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=1 confirm_ms=0 budget_ms=2
programmableSeize.seize-1-input: K=2570 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=51571527,mem=140357] | count_ms=2 confirm_ms=0 budget_ms=7
programmableSeize.seize-2-inputs-partial-with-noise: K=4647 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=96841491,mem=251272] | count_ms=3 confirm_ms=0 budget_ms=13
programmableSeize.seize-1-input-missing-residual-output-REJECT: K=1938 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1976 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=2 confirm_ms=0 budget_ms=2
programmableLogicGlobal.transfer-member-single-policy: K=3262 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=62665145,mem=177810] | count_ms=2 confirm_ms=0 budget_ms=10
programmableLogicGlobal.transfer-nonmember-covering-node: K=1554 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=29160036,mem=86035] | count_ms=1 confirm_ms=0 budget_ms=5
programmableLogicGlobal.transfer-mixed-many-policies: K=3726 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=78031424,mem=204737] | count_ms=2 confirm_ms=0 budget_ms=11
programmableLogicGlobal.transfer-containment-violation-REJECT: K=2970 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=3448 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=2 confirm_ms=0 budget_ms=4
```

## Appendix A′ — re-measurement on the CURRENT applied flats (task C3, 2026-07-25)

**This is the authoritative run.** Same `KMeasure.lean`, same method, same PCB
(`/home/gumbo/iohk/PlutusCoreBlaster`, branch `cip153-value-builtins`, commit
`9f9ca8c76baf3b5efdb63c33ca0091efa606b474`, working tree clean), against
`WSC/goldens/applied/*.flat` as they stand at this revision.

Four rows differ from Appendix A, all four traceable to the wsc-poc builder fix
that re-dumped every vector:

| golden | Appendix A (pre-fix) | **Appendix A′ (current)** | Δ |
|---|---|---|---|
| `programmableSeize.seize-1-input` | 2,570 | **3,002** | +432 |
| `programmableSeize.seize-2-inputs-partial-with-noise` | 4,647 | **5,079** | +432 |
| `programmableSeize.seize-1-input-missing-residual-output-REJECT` | 1,938 | **2,261** | +323 |
| `programmableLogicGlobal.transfer-containment-violation-REJECT` | 2,970 | **2,737** | **−233** |

The other 9 reproduce to the unit. The three seize rows move together and in the
same direction, consistent with a common cause (the residual seized-token output
gained a lovelace entry under `ensureMinAda`, so every value walk over it costs
more); the global rejecting row moves DOWN, i.e. it now fails EARLIER, which is
also consistent — its tamper is detected before the extra work is reached.

**Cross-check, and the reason these numbers are trustworthy:** for all 9
accepting goldens PCB's own metered `pcbBudget[cpu=…,mem=…]` below equals the
`exBudgetCpu`/`exBudgetMem` recorded in the golden JSON **exactly**, so the
"`PCB budget = ledger?` **exact**" column of §3 is re-earned on the current
vectors rather than inherited.

```
programmableLogicBase.base-spend-transfer-tx: K=208 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=145 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=4525794,mem=11715] | count_ms=0 confirm_ms=0 budget_ms=1
programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: K=286 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=145 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=1 confirm_ms=0 budget_ms=0
programmableTokenMinting.mint-local-registered-by-ref: K=1681 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=34116362,mem=92870] | count_ms=1 confirm_ms=0 budget_ms=4
programmableTokenMinting.mint-burnonly: K=784 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=14215312,mem=43421] | count_ms=1 confirm_ms=0 budget_ms=2
programmableTokenMinting.mint-delegate-transfer-topup: K=1257 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=26455938,mem=69372] | count_ms=1 confirm_ms=0 budget_ms=3
programmableTokenMinting.mint-local-empty-withdrawals-REJECT: K=1627 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1285 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=1 confirm_ms=0 budget_ms=2
programmableSeize.seize-1-input: K=3002 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=60231630,mem=163820] | count_ms=2 confirm_ms=0 budget_ms=8
programmableSeize.seize-2-inputs-partial-with-noise: K=5079 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=105501594,mem=274735] | count_ms=3 confirm_ms=0 budget_ms=13
programmableSeize.seize-1-input-missing-residual-output-REJECT: K=2261 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1976 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=1 confirm_ms=0 budget_ms=3
programmableLogicGlobal.transfer-member-single-policy: K=3262 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=62665145,mem=177810] | count_ms=2 confirm_ms=0 budget_ms=8
programmableLogicGlobal.transfer-nonmember-covering-node: K=1554 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=29160036,mem=86035] | count_ms=1 confirm_ms=0 budget_ms=4
programmableLogicGlobal.transfer-mixed-many-policies: K=3726 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=78031424,mem=204737] | count_ms=3 confirm_ms=0 budget_ms=11
programmableLogicGlobal.transfer-containment-violation-REJECT: K=2737 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=3448 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=2 confirm_ms=0 budget_ms=4
```

## Appendix B — verbatim prep-probe output

```
$ /usr/bin/time -f "BUDGET=%s ..." timeout … lake env lean PrepProbe/MintB.lean
BUDGET=600  EXIT=0   WALL=11.086
BUDGET=900  EXIT=0   WALL=27.61   CPU=27.33
BUDGET=1200 EXIT=0   WALL=131.57  CPU=131.31
BUDGET=1700 EXIT=124 WALL=2918.66            <- timeout-killed, NEVER COMPLETED
GLOBAL BUDGET=600  EXIT=0 WALL=11.84   CPU=11.76   MAXRSS_KB=1188528
GLOBAL BUDGET=1600 EXIT=0 WALL=2143.40 CPU=2141.09 MAXRSS_KB=1588268
PROBE='Global900' EXIT=0 WALL=24.30 CPU=23.86
PROBE='Seize600'  EXIT=0 WALL=12.71 CPU=12.19
PROBE='Seize900'  EXIT=0 WALL=19.38 CPU=18.62
```

## Appendix C — verbatim applied-flat verification

```
$ lake env lean KVerify.lean > /tmp/kverify.log && python3 verify-applied.py /tmp/kverify.log
OK programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicBase.base-spend-transfer-tx: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-containment-violation-REJECT: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-member-single-policy: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-mixed-many-policies: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-nonmember-covering-node: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-1-input-missing-residual-output-REJECT: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-1-input: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-2-inputs-partial-with-noise: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-burnonly: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-delegate-transfer-topup: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-local-empty-withdrawals-REJECT: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-local-registered-by-ref: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
ALL-MATCH
```
