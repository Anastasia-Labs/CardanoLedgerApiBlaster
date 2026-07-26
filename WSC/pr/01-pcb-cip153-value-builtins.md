# SUBMISSION 1 — PlutusCoreBlaster: the CIP-153 `Value` builtins

**Repo** `input-output-hk/PlutusCoreBlaster` · **branch** `cip153-value-builtins`
(`9f9ca8c76baf3b5efdb63c33ca0091efa606b474`) · **base** `a04042c4b7b19c66e7e6fa5bbcc3b1c985894ed0`,
which **is** today's `origin/main` — no rebase needed at the time of writing
· **2 commits, 17 files, +2832/−6**

Part 1 is the PR description as it should be submitted. Part 2 is the readiness
assessment: what a maintainer will ask about, and what to do before opening it.

---
---

# PART 1 — PR DESCRIPTION (submit this)

## Summary

Adds the six CIP-153 `MaryEraValue` builtins to the UPLC substrate — enum entries,
arities, flat tags 94–99, CEK denotations matching `plutus`'s `Value.hs`, cost arms in
all five semantics variants, and ~45 unit tests — plus `PlutusCore/Value/Algebra.lean`,
an equational theory over them for use by proof automation.

The motivating consequence: **a real production PlutusV3 script that uses these
builtins previously failed to decode at all.** Against `main` the same flat blob returns
`Could not decode program!`; with this branch it decodes, and the decoded body runs on
the CEK machine end to end. That negative control is committed as part of the test
suite.

| builtin | flat tag | arity | plutus signature |
|---|---:|---:|---|
| `insertCoin` | 94 | 4 | `ByteString → ByteString → Integer → Value → BuiltinResult Value` |
| `lookupCoin` | 95 | 3 | `ByteString → ByteString → Value → Integer` |
| `unionValue` | 96 | 2 | `Value → Value → BuiltinResult Value` |
| `valueContains` | 97 | 2 | `Value → Value → BuiltinResult Bool` |
| `valueData` | 98 | 1 | `Value → Data` |
| `unValueData` | 99 | 1 | `Data → BuiltinResult Value` |

## `830819b` — the builtins

* **`PlutusCore/UPLC/Term/Basic.lean`** — `BuiltinFun` entries `InsertCoin`…`UnValueData`
  after `DropList`; `Const.Value : List (ByteString × List (ByteString × Integer))`;
  `AtomicType.TypeValue`.
* **`PlutusCore/UPLC/Builtins.lean`** — arities, all monomorphic.
* **`PlutusCore/UPLC/FlatEncoding/Basic.lean`** — builtin tags 94–99; uni tag 13 →
  `TypeValue` in `decodeConstType`; a value-constant decoder following flat's
  Map-as-list encoding, with `K`/`Quantity` validation and `packValue` normalisation.
* **`PlutusCore/Value/Basic.lean`** (new, 256 lines) — a pure model of `Value.hs`:
  `ValueRep`, `insertCoin`, `deleteCoin`, `lookupCoin`, `unionValue`, `valueContains`,
  `valueData`, `unValueData`, `packValue`. All total (`termination_by` on list lengths);
  `Option.none` encodes `BuiltinResult` failure.
* **`PlutusCore/UPLC/BuiltinFunctions/Value.lean`** (new) — `CekValue` wrappers, args
  reversed per this repo's convention, dispatched from `Evaluate.lean` (6 new arms).
* **`PlutusCore/UPLC/CostModels.lean`** (+239) — helpers `argValueTotalSize`,
  `argValueMaxDepth`, `dataNodeCount`/`argDataNodeCount`; `constSize (.Value v) =
  totalSize v`; six cost arms in each of the five variants A–E.
* **`Term/Instances.lean`**, **`Term/ToExpr.lean`**, **`TextEncoding/Basic.lean`** —
  `Repr`/`ToExpr`/`BEq`/type-name-parse coverage for the new constructors.
* **`PlutusCore/Value/Tests.lean`** (new, 331 lines) — ~45 `native_decide` unit tests,
  registered in `Tests/Basic.lean`.

## `9f9ca8c` — blaster-friendly denotations + `Value/Algebra.lean`

Every `Value` denotation walk is restated as an explicit first-order pattern-match
recursion — no `List.all`/`any`/`find?`, no `foldl` with a lambda, no projection
lambdas. **Motivation is downstream**: an SMT-based proof automation consumer cannot
digest the stdlib combinators (3 of 4 containment lemmas came back `Undetermined`, one
was a hard translation error), while the hand-rolled recursions close in seconds.

**Public names, signatures and semantics are unchanged, and that is a theorem, not a
claim:** `Basic.lean` carries an `*_eq_*` lemma proving each restatement equal to its
original stdlib-combinator formulation. All unit tests, the decode gate and the CEK
dispatch tests pass unchanged.

`PlutusCore/Value/Algebra.lean` (new, 1400 lines) is the equational theory, in plain
Lean, `sorry`-free — four lemma groups:

* `lookupCoin_insertCoin_hit` / `_miss`, including the `amt = 0` delete arm;
* `lookupCoin_unionValue`, plus `unionValue_none` (the overflow side) and
  `unionValue_sorted`;
* `valueContains_iff` and `valueContains_none_iff` (both negative-error arms);
* the sortedness/normalisation invariants the above need.

## Fidelity evidence

Every number and every semantic decision below was read out of `plutus` source, cited
to file and line:

* **flat builtin tags** — `plutus-core/src/PlutusCore/Default/Builtins.hs:2171-2176`
  (encode `InsertCoin -> 94` … `UnValueData -> 99`), decode `go 94`…`go 99` at
  `:2275-2280`.
* **arities and signatures** — `Builtins.hs:1979-2027`.
* **uni tag** — `Universe.hs:896` `encodeUni DefaultUniValue = [13]`, decode at `:920`.
* **semantics** — `Value.hs`, read in full (564 lines): `maxKeyLen = 32` (`:70`);
  `Quantity` bounds ±2¹²⁷ (its `Bounded` instance); `insertCoin` with `amount = 0`
  delegates to `deleteCoin` with an unchecked `UnsafeK` (**no key validation** — a real
  corner, and it is tested); replace-not-add via
  `insertLookupWithKey (\_ _ _ -> qty)`; `unionValue` fails on overflow and drops zeros
  and empty inner maps; `valueContains` fails on negatives in **either** argument (v1
  checked first) and is `isSubmapOfBy (isSubmapOfBy (<=))`; `valueData` emits `Map`/`B`/`I`
  in ascending order; `unValueData` rejects non-`Map`, non-`B` keys, oversized keys,
  non-ascending order at **both** levels, empty inner maps, and zero or out-of-bounds
  `I` (an empty outer map is valid).
* **flat instance** — `pack <$> decode` with Map-as-list encoding
  (`flat/src/PlutusCore/Flat/Instances/Containers.hs:73`) and validating `K`/`Quantity`
  instances.
* **cost numbers** — `cost-model/data/builtinCostModel{A,B,C}.json`; formulas from
  `CostingFun/Core.hs:527-550` (`with_interaction`, `c00+c10x+c01y+c11xy`) and
  `:702-709` (`const_above_diagonal`); size measures from `ExMemoryUsage.hs:391-446`
  (`DataNodeCount` = node count, `ValueTotalSize`, `ValueMaxDepth` = ⌊log₂m⌋+1 +
  ⌊log₂k⌋+1) and `:405-407` (generic `ExMemoryUsage Value = totalSize`, mirrored in
  `constSize`).

## Verification

```
lake build          →  Build completed successfully (284 jobs).   exit 0
lake build Tests    →  Build completed successfully (292 jobs).   exit 0
```

Re-run in a clean `cp -a` workspace at `9f9ca8c` immediately before writing this.

**The decode gate.** `PlutusCore/Value/Tests.lean` contains
`#import_uplc … PlutusV3 double_cbor_hex ".../TestsFlat/programmableLogicGlobal.flat"`
under a `#guard_msgs` expecting `Successfully decoded double CBOR hex '…'`. It is
non-vacuous by construction: six `usesBuiltin` checks prove the decoded program really
contains `InsertCoin`, `UnionValue`, `ValueContains`, `ValueData`, `UnValueData` and
`DropList`. An evaluation smoke test then applies the decoded body to two dummy
`Data (I 0)` arguments and runs `runStepsWithBudget` with a 10¹⁰/10¹⁰ budget, reaching a
terminal `EvaluationError` — i.e. the real bytecode runs on the CEK machine with no
decode failure, no budget exhaustion and no stuck state.

Unit tests rather than conformance vectors: there is no `.plutus-conformance`
directory in this repository (checked).

## Deviations from `Value.hs`, and why each is safe

All six are documented in-code at the point of deviation.

1. `valueContains`'s `totalSize v1 < totalSize v2 → False` **shortcut** is omitted from
   the semantics — provably equivalent for normalised non-negative values. It is kept in
   the cost arm's diagonal, where it is observable.
2. `unionValue`'s empty short-circuit and size-based argument swap are omitted —
   identity and commutativity make them semantically transparent.
3. Error-check **order** within a builtin (e.g. currency-vs-token-vs-quantity in
   `insertCoin`) collapses to a single `none`. Order is preserved anyway where cheap.
4. **Cost variants D and E reuse the A/B/C numbers** — see the caveat below.
5. `negativeAmounts` is recomputed by scan rather than cached — this model has no
   caching; observationally identical.
6. The flat value-constant decoder models `Map.fromList` last-wins on duplicate keys
   plus `pack` normalisation (`packValue`), and is tested. Compiled scripts are unlikely
   ever to carry value constants, but decoding is now faithful if they do.

## Caveats, stated up front

* **Cost variants D and E carry the A/B/C numbers.** The `plutus` checkout used here has
  `builtinCostModel{D,E}.json` predating CIP-153, so there is nothing to transcribe.
  Every one of the six D and six E arms carries the disclosure in a comment. They are
  **not load-bearing for the consumer that motivated this work**, which budgets by CEK
  step count rather than `ExBudget`. If you would rather these arms fail loudly than
  return a plausible-but-unsourced number, say so and I will change them — I chose a
  documented wrong number over a crash in an unexercised path, and that is a judgement
  call you may reverse.
* **`ScaleValue` is not included.** It is the seventh CIP-153 builtin; its flat tag is
  above the 94–99 range this branch enables. No consumer needs it and I did not verify
  its tag or its costing against `plutus`, so it is left out rather than guessed at.
  Happy to add it as a follow-up.
* **Textual `(con value …)` constant syntax is not parsed.** It fails the same way
  `bls12_381_MlResult` does. Type *names* parse (`"value"`); constant *literals* do not.
  No current gate needs them.
* **The `sorry` in the build is not mine.** The single `declaration uses 'sorry'`
  warning is `PlutusCore/UPLC/CekMachine.lean:299:4` (`runStepsWithBudget`'s
  `decreasing_by`), which predates this branch and is untouched here. Its one practical
  effect on this work is that ad-hoc budget runs must use `#eval!` rather than `#eval`;
  the `native_decide` tests are unaffected.
* **The test fixture is an application's production script.**
  `ScriptEncoding/TestsFlat/programmableLogicGlobal.flat` is the *unapplied* production
  global validator exported from `input-output-hk/wsc-poc` (regenerated there by commit
  `7ae0024`; 6,880 hex chars, `590d6d590d6a0101…`, double-CBOR, UPLC 1.1.0). It is the
  only real-world script I have that exercises tags 94–99, which is why it is here. If
  you would prefer a synthetic minimal fixture, that is a reasonable ask and I will
  build one; note the trade — a hand-built fixture cannot catch a decoder bug that only
  a compiler-emitted program triggers, which is exactly the class of bug this fixture
  found.

---
---

# PART 2 — READINESS ASSESSMENT (do not submit this part)

## Is it PR-ready as-is?

**Nearly. One measured blocker, three disclosures, one logistics item.**

### 4.1 BLOCKER — 48 lint warnings in the branch's own new files

Measured in this task from a clean-room `cp -a` build at `9f9ca8c`:

| file | sites |
|---|---:|
| `PlutusCore/Value/Algebra.lean` | **45** |
| `PlutusCore/Value/Basic.lean` | **3** |
| **total** | **48** |

All are `This simp argument is unused`, i.e. a `simp only [...]` list carrying a name
simp never fired on. By unused-argument name:

| unused argument | sites |
|---|---:|
| `hbe` | 17 |
| `hbe'` | 12 |
| `hngt` | 6 |
| `hz` | 6 |
| `if_neg` | 2 |
| `h` | 2 |
| `ite_true` | 2 |
| `ite_false` | 1 |

(They appear **96** times in a full log because each is emitted once per build target —
library and `Tests`. 48 is the number of source sites.)

**Why this is a blocker rather than a nit.** `main` builds with exactly one warning (the
pre-existing `sorry`). This branch takes that to 49. A maintainer's first impression of
a 1,400-line new proof file is the warning wall above it, and the fix is deletion of
dead names — the lowest-risk edit in Lean. Removing an argument the linter has already
proved unused cannot change a proof; one rebuild confirms all 48 at once.

**Regenerate the exact list with:**
```bash
lake build 2>&1 | grep -A1 'This simp argument is unused'
```

### 4.2 Commit structure — keep the two commits

`830819b` (the builtins) and `9f9ca8c` (the restatement + `Algebra.lean`) are two
genuinely separate changes and should stay separate: the first is a substrate feature a
maintainer can review against `plutus` source; the second is a refactor whose
*motivation* is external and whose *safety* is internal (the `*_eq_*` lemmas). Squashing
them would hide that the refactor is provably semantics-preserving. **Do not squash.**

Base is `a04042c` = today's `origin/main`, so **no rebase is needed** — re-check at
submission time, since that is the kind of fact that expires.

### 4.3 The pre-existing `CekMachine.lean:299` `sorry` — do not touch it

It is `runStepsWithBudget`'s `decreasing_by` (the `sorry` term is at `:314`; the warning
is reported at the declaration, `:299:4`). It is not in this branch's diff and fixing it
is a separate piece of work with its own review surface (the measure is
`budget.exBudgetCPU.unExCPU + budget.exBudgetMemory.unExMemory`, and the decrease needs
`stepWithBudget`'s `canAfford` guard to imply a strict drop, which is true but not
one-line). **Disclose it in the body — done above — and leave it alone.** Offering to
fix it in the same PR would be scope creep on a file nobody in this change owns.

### 4.4 The D/E cost variants — the one thing likely to draw pushback

Verified in this task: all five variants carry **byte-identical** cost expressions for
the six builtins (e.g. `InsertCoin` is `⟨⟨356924 + 18413 * u⟩, ⟨45 + 21 * u⟩⟩` at
`CostModels.lean:452, 750, 1041, 1294, 1550`), and each of the five blocks carries the
same four-line disclosure comment. So the disclosure is already in-code, in all five
places — good.

What is **missing**: nothing distinguishes D and E from A/B/C to a grepper. There is one
`TODO` in the whole file and it is unrelated (`:80`). Recommended pre-submission edit:
add a `-- TODO(CIP-153): D/E numbers are A/B/C's; refresh from
cost-model/data/builtinCostModel{D,E}.json once those carry tags 94-99` to the D and E
blocks **only**, so a maintainer grepping `TODO` finds them and a future contributor
does not have to re-derive why they are identical.

Three ways this can go, in the order I would defend them:

1. **ship as-is + the TODO markers** (recommended) — the numbers are unsourced but
   unexercised by the consumer, and a documented wrong number is safer than a crash in
   a path nobody runs;
2. make the six D/E arms `panic!`/`none` — guarantees no wrong number is ever consumed,
   but converts an inert inaccuracy into a live failure mode;
3. drop D/E from the PR — leaves the enum non-exhaustive in two variants, which will
   not compile.

Only 1 and 2 are real options. **Say in the body which one you picked and why** — that
is the whole point, and the body above does.

### 4.5 `ScaleValue` — disclose, offer, do not guess

The omission is deliberate and correctly reasoned (no consumer, outside the tag range
enabled). But note honestly: the internal report describes it as "tag 100 region", and
**this task did not verify `ScaleValue`'s actual flat tag or costing against `plutus`.**
The body therefore says "above the 94–99 range" and does not name a tag. Do not tighten
that sentence without checking `Builtins.hs`.

### 4.6 LOGISTICS — the local checkout is a **shallow clone**

`.git/shallow` grafts at `a04042c`; `git rev-list --count HEAD` is **3**. Two
consequences:

* A whole-history `git bundle` made from it is unusable even though `git bundle verify`
  calls it complete — this was measured previously and is why the offline artifact in
  the downstream repository is an *incremental* bundle.
* **Before pushing, confirm the push from a shallow clone succeeds** (`git push -u
  origin cip153-value-builtins --dry-run`). If it does not, the fix is to clone
  `origin/main` fully into a fresh directory and apply the two commits with
  `git am`/`cherry-pick` from the existing checkout. Budget ten minutes for this.

### 4.7 What a maintainer will want that is *not* in the diff

* **A short `PlutusCore/Value/README.md`** — three paragraphs: what the six builtins
  are, where the `plutus` sources are, and the A/B/C-vs-D/E cost situation. The internal
  report `WSC/CIP153-BUILTINS-REPORT.md` is the raw material; it must **not** be shipped
  as-is (its first line is an absolute local path plus "not pushed").
* **A sentence about who is waiting on this**, without citing paths in a repository the
  maintainer cannot open. One sentence, in the Summary — already drafted above.

### 4.8 What is NOT owed to PCB — it belongs to Blaster

The `#import_uplc` command registers its identifier in the **root** namespace rather
than the enclosing one. That is Blaster's elaborator behaviour, not PCB's, and it is a
usage note for consumers rather than a defect in this PR. Leave it out of the body.

### 4.9 Checklist before opening

- [ ] delete the 48 unused `simp` arguments; rebuild; confirm warnings drop to **1**
- [ ] add `TODO(CIP-153)` markers to the D and E cost blocks only
- [ ] optional: `PlutusCore/Value/README.md`
- [ ] `git fetch origin && git log --oneline origin/main -1` — confirm base is still `a04042c`
- [ ] `git push --dry-run` from the shallow clone; fall back to a full clone if it fails
- [ ] re-run `lake build` and `lake build Tests` in a fresh `cp -a`; expect 284 / 292 jobs, exit 0
- [ ] open the PR with Part 1 as the body
