# REPRODUCE — building and re-checking the WSC containment campaign elsewhere

This is the third-party recipe. It assumes nothing about the machine the campaign
was developed on. Every expected number below was measured by task E5 on
2026-07-25 at branch `wsc-containment-proofs`; where a number is a range, the range
is two independent runs, because a single wall-clock figure that does not reproduce
is exactly the sort of claim this campaign's audit exists to catch.

**Read `WSC/AUDIT.md` §0 before you read any number here.** Reproducing the build
does not reproduce the *claim* — it reproduces a set of solver verdicts and axiom
lists. What those establish is `WSC/README.md`'s subject.

---

## 0. Environment

| | value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.24.0` (`lean-toolchain`, elan will fetch it) |
| Z3 | 4.15.2, 64-bit, on `PATH` |
| CPU | 32 cores on the reference box; the build peaks around 420–460 % CPU |
| RAM | peak RSS **1.50 GB** — 4 GB is comfortable |
| `maxHeartbeats` | `0` (set per-module in the sources; do not override) |

Two dependencies:

| package | how | pinned to |
|---|---|---|
| `Blaster` | git require, public | `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce` on `https://github.com/input-output-hk/Lean-blaster`, branch `beta-lambda-cache-optimization` |
| `PlutusCore` (PlutusCoreBlaster) | **absolute local path** | `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`, branch `cip153-value-builtins` — **not on the public remote** |

The Blaster pin is a real, verified `rev` in `lake-manifest.json`. Branch names
move; the manifest rev is what is checked.

---

## 1. Reconstruct the substrate

The `PlutusCore` dependency is the one thing that does not resolve by itself. Its
branch is not published, so this repository carries it as an offline artifact.

Full instructions, checksums and the reason the bundle is *incremental* rather
than whole-history: **`WSC/substrate/README.md`**. In short:

```bash
git clone https://github.com/input-output-hk/PlutusCoreBlaster /some/path/PlutusCoreBlaster
cd /some/path/PlutusCoreBlaster
git rev-parse HEAD         # a04042c4b7b19c66e7e6fa5bbcc3b1c985894ed0  (the public base)

git bundle verify  <CLAB>/WSC/substrate/pcb-cip153-value-builtins.bundle
git fetch          <CLAB>/WSC/substrate/pcb-cip153-value-builtins.bundle \
    'refs/heads/cip153-value-builtins:refs/heads/cip153-value-builtins'
git checkout cip153-value-builtins

git rev-parse HEAD         # 9f9ca8c76baf3b5efdb63c33ca0091efa606b474
git rev-parse HEAD^{tree}  # e75862b26b5055e8cc36ea8cf393054e2417ca62
```

If those last two hashes do not match, **stop** — nothing below means anything,
because the CIP-153 `Value` builtins on that branch are what let the production
`programmableLogicGlobal` flat decode at all.

---

## 2. Repoint the path dependency — BOTH files

This is the one edit every third party must make, and the one place people get it
wrong. The substrate path appears **twice**:

1. `lakefile.lean` — `require PlutusCore from "/home/gumbo/iohk/PlutusCoreBlaster"`
2. `lake-manifest.json` — the `PlutusCore` entry's `"dir"` field

Editing only one leaves lake resolving the manifest's stale `dir`, usually with a
confusing error far from the cause.

Then build the substrate once:

```bash
cd /some/path/PlutusCoreBlaster && lake build
```

---

## 3. The clean-room rebuild

Delete every `WSC` olean; **keep** the dependency oleans. A full `lake clean` is
not needed and only costs time: no WSC solver verdict is computed in a dependency
module — every `#import_uplc`, `#prep_uplc` and `#blaster` lives under `WSC/` — so
deleting the WSC oleans forces all of them to run for real.

```bash
cd <CLAB>
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.olean \
       .lake/build/lib/lean/WSC.ilean .lake/build/lib/lean/WSC.olean.hash \
       .lake/build/lib/lean/WSC.ilean.hash .lake/build/lib/lean/WSC.trace
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log
```

### Expected

> **This table was stale and is corrected here.** It carried E5's `7039cdb`
> figures and was never updated at G3 (`f4486ca`), where the library moved to 432
> jobs / 94 modules / 162 verdicts. It is now stated at the **current** revision,
> i.e. after the H2 dead-file cleanup (`AUDIT.md` §12): the jobs and module counts
> happen to return to 431/93, but the **verdict count is 162, not 159** — the E5
> value in this table was wrong for two revisions.

| measurement | expected |
|---|---|
| exit status | `0` — `Build completed successfully (431 jobs)` |
| wall clock | **1:49 – 2:36** (measured across three runs on a box under concurrent agent load; do not quote a point value) |
| user + sys CPU | 478–585 s + 58–84 s |
| max RSS | **1.50–1.66 GB — load-dependent, NOT an instrument** (`AUDIT.md` §1.2) |
| WSC modules re-elaborated | **93** |
| solver verdicts | **162 — 103 `✅ Valid` + 59 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` | **0 / 0** (hard requirement) |
| `error:` lines | **0** (hard requirement) |
| `declaration uses 'sorry'` | **20** — 19 `WSC/ShapeBridge.lean`, 1 `PlutusCore/UPLC/CekMachine.lean:299`. **NOT a census — see §5.** |
| `unused variable` | **5**, all at `WSC/Composition.lean:2442-2446` |

---

## 4. Censuses

```bash
# markers
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c    # 102 Valid, 57 Expected Falsified
grep -cE '⚠️|❌' build.log                             # 0
grep -c 'error:'  build.log                            # 0
grep -c 'unused variable' build.log                    # 5

# axiom declarations
grep -rn '^axiom ' --include='*.lean' WSC/ | wc -l                                  # 51
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0  ← the shaped layer adds no assumption
grep -rl 'set_option warn.sorry false' --include='*.lean' WSC/ | wc -l              # 38
```

### Source reconciliation — the check that rules out a skipped stanza

Over the 93 built modules, **with block comments and docstrings stripped first**:

* **57** column-0 `#blaster … (solve-result: 1)` stanzas → 57 `✅ Expected Falsified`
* **2** column-0 `#blaster … (solve-result: 0)` stanzas → 2 `✅ Valid` (these are the
  deliberate vacuity probes: `WSC/Prep/Global.lean:83`, `WSC/Props/P4_Minting.lean:386`)
* **100** `blaster` tactic invocations in theorem position → 100 `✅ Valid`

`57 + 2 + 100 = 159`, matching the log exactly.

> **Two traps.** (a) Strip block comments first, or prose inside docstrings inflates
> the count. (b) **5** of the tactic invocations are written `:= by` with `blaster`
> on the *next* line — `WSC/Props/P3_BaseRun.lean:93,112,141`,
> `WSC/Goldens/Witnesses.lean:152`, `WSC/Props/P3_Base.lean:210`. A naive one-line
> grep finds 95 and lands on 154 instead of 159.

### Axiom census — the numbers that actually matter

`#print axioms` output **wraps across log lines**. Parse for `'NAME' depends on
axioms: [` … `]` across newlines; a line-oriented grep undercounts `sorryAx` badly
(17 instead of 37).

```
172 `#print axioms` results;  37 carry sorryAx;  70 use native_decide;
122 carry zero project axioms.
(At HEAD f4486ca, before the H2 dead-file cleanup: 174 / 37 / 72 / 124.
 The two removed results were builtins-only, so no project-axiom figure moved.)
```

The four to check by name:

| theorem | project axioms |
|---|---|
| `Composition.containment_on_contained_class` | **26** |
| `RealizableLeaves.containment_on_realizable_class` | **28** = the 26 + `LR_BUDGET_global` + `TS3` |
| `RealizableLeaves.containment_on_seize_class` | **28** = the 26 + `LR_BUDGET_seize` + `nodeStepsSeize` |
| `RealizableLeaves.realizable_inhabitant` / `_NS` / `_S1R` | **0**, and no `sorryAx` |

---

## 5. Things that will mislead you if you skip them

1. **The `sorry` warning count is not a census.** 38 modules `set_option
   warn.sorry false`, so ~100 further `admit`-closed theorems emit no warning at
   all. The authoritative instrument is `#print axioms` → `sorryAx`. Every one of
   the 100 `by blaster` theorems is admit-closed, and **every top-level theorem
   carries `sorryAx`**.
2. **Always time with `lake build`, never `lake env lean`.** The latter omits
   `--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. A whole audit
   finding (F5) exists because someone quoted a `lake env lean` figure.
3. **`✅ Valid` is a Z3 verdict recorded in the log, not a kernel check.** Rebuilding
   from cached oleans replays the log line without re-running the solver. Only the
   clean-room delete in §3 re-runs them.
4. **A `✅ Valid` can be vacuous.** The library's own worst moment is preserved at
   `WSC/Shaped/Probe/G6Vacuous2500.lean`: a `✅ Valid` over an accept-UNSAT class.
   That is why every accept-hypothesis theorem is paired with a probe at its **own**
   term and its **own** shape.

---

## 6. Re-verify the bytecode provenance (independent of Lean)

The four `.flat` files must be byte-identical to the `cborHex` of the named
unapplied production scripts at wsc-poc commit `7ae0024`:

```bash
for n in programmableLogicBase programmableLogicGlobal programmableSeize programmableTokenMinting; do
  git -C <wsc-poc> show 7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/$n.json \
    | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | tr -d '\n' | sha256sum
  sha256sum <CLAB>/WSC/flats/$n.flat
done
```

Expected, 4/4 identical:

```
1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3  programmableLogicBase
ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2  programmableLogicGlobal
289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1  programmableSeize
7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048  programmableTokenMinting
```

---

## 7. Optional: prep-cost re-measurement

```bash
for m in Base Minting900 Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.{olean,ilean,trace}
  /usr/bin/time -f "$m %e s" lake build WSC.Prep.$m > /dev/null
done          # expect ~ 1.6 / 1.5 / 36-46 s
```

Do **not** trust the figures in `WSC/goldens/K-MEASUREMENTS.md` §5.1; they were
taken with `lake env lean` and are the subject of audit finding F5.

---

## 8. Residual non-portability, stated plainly

After §1 and §2 this repository builds on another machine. It is still true that:

* the substrate branch is **not published**, so the bundle in `WSC/substrate/` is
  the only copy travelling with the repo — custody is the trust anchor;
* the `require` is still an **absolute path**, so §2 is a mandatory manual edit;
* `lake` does not verify the `"rev"` recorded for a path dependency, and `lake
  update` would drop it.

The one-line fix that retires all three is to push the PCB branch and restore a git
pin (`WSC/substrate/README.md` §5).
