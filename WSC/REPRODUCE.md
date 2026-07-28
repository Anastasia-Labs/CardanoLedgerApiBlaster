# REPRODUCE — building and re-checking the WSC containment campaign elsewhere

> # ⚠️ POST-#112 (task N6, 2026-07-28) — READ `WSC/AUDIT.md`'s BANNER FIRST
>
> This file was written against the PRE-#112 wsc-poc bytecode. wsc-poc PR #112
> (`main` @ **2306678**) changed three of the four validators SEMANTICALLY; the
> minting policy is byte-identical. Tasks N1–N6 re-based everything.
>
> **The current measurements are: 440 jobs, 0 errors, `170` solver verdicts
> (`108 ✅ Valid` + `62 ✅ Expected Falsified`), 0 `⚠️`/`❌`, 20 `sorry`,
> 5 unused-variable, 102 WSC modules, two clean-room runs, wall ≈ 9.5 min,
> peak RSS ≈ 4.35 GB.** Both composed results survive with **28** project axioms
> each and **1 of 4** leaves discharged by the bytecode on each side — unchanged
> — but `top_claim` now carries one NEW hypothesis, `WdrlPairShaped Shape`.
>
> Everything that changed, with measurements: `WSC/AUDIT.md` (top banner) and
> `WSC/status-fragments/N6-compose-and-reaudit.md`. Numbers in the body below
> that disagree with the ones above are the pre-#112 record.

---


## 0-N6. WHAT CHANGED FOR A THIRD PARTY AFTER wsc-poc PR #112

Three things, and two of them make reproduction HARDER.

1. **Machine requirements moved.** The clean-room rebuild now takes **≈ 9.5
   minutes** (was 1:46–2:10) and peaks at **≈ 4.35 GB RSS** (was 1.65 GB). Plan
   for **5 GB of free RAM**. `WSC.Prep.Global1600` alone accounts for **516 s** of
   the wall — 89 % of it. It is the `#prep_uplc` of the post-#112
   `programmableLogicGlobal`, whose flat got smaller (6880 → 5624 hex chars) but
   whose term got much harder because #112 moved the mint merge and the per-pair
   value delta onto CIP-153 `Value` builtins.
2. **The PlutusCoreBlaster pin is now needed by TWO validators, not one, and it
   needs a SEVENTH builtin.** Pre-#112 only `programmableLogicGlobal` failed to
   decode against stock PCB. Post-#112 **`programmableSeize` fails too**, and it
   uses `ScaleValue` — plutus-core flat tag **100** — which was NOT among the six
   the branch originally carried (tags 94–99). The required PCB revision is
   `cip153-value-builtins` @ **3fdd3fb** (task N5); anything earlier gives
   `Could not decode program!` on `WSC/flats/programmableSeize.flat`, and any
   attempt to guess the tag is unsafe (89–91 are present-but-commented in
   plutus-core, so "next free number" is wrong).
   The same commit also fixes a **cost-table bug** only seize could expose:
   `unValueData` and `valueData` carried plutus **1.57** coefficients in an
   otherwise-1.63 table. With it, PCB's metered budget reproduces the ledger
   `ExBudget` **exactly on all nine accepting goldens** (was 7 of 9).
3. **Blaster is now a local path pin too.** `require Blaster from
   "/home/gumbo/iohk/Lean-blaster-wsc"`, branch `wsc-d6-dite-branch-retype` @
   **4d320dd** = public `59db213` + ONE commit. Without that commit the seize
   shaped prep and `WSC/Prep/Global1600` both die with a KERNEL
   `application type mismatch` on `Blaster.dite'` (defects D6/D8): the condition
   and the branch lambdas are optimized independently, so a normalisation that
   rewrites `¬c` without rewriting `c` emits a term the kernel rejects. Two such
   normalisations fire on #112 bytecode. Verdict-neutrality was controlled: the
   eight `WSC/Props/Shaped/P4*` modules give byte-identical counts (42 V + 23 F)
   with and without the patch.

**Net:** reproducing this library off this machine now requires **three**
unpublished branches (PCB `cip153-value-builtins` @ 3fdd3fb, Blaster
`wsc-d6-dite-branch-retype` @ 4d320dd, and CLAB `wsc-containment-proofs` itself),
where before it required one. The offline `git bundle` under `WSC/substrate/`
carries only the PCB branch **at 9f9ca8c** and is therefore STALE — it predates
`ScaleValue` and will not decode the post-#112 seize flat.

---


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
| `Blaster` | **absolute local path** (was: git require, public) | `4d320dd5f70ac953945b5126f5cfd45128da8131`, branch `wsc-d6-dite-branch-retype`, tree `9550c96b0dff95096d07d29825a19d885fe7c6cd` — = public `59db213` **+ one commit** (the D6 fix) — **not on the public remote** |
| `PlutusCore` (PlutusCoreBlaster) | **absolute local path** | `3fdd3fb5cb259f039b60cc584cd954de18c819dc`, branch `cip153-value-builtins`, tree `1c9d80221bd59fdd21ab132d1fcec086c7bbf3b9` — **not on the public remote** |

**⚠️ BOTH PINS MOVED, AND BOTH ARE NOW UNPUBLISHED LOCAL PATHS.** This table used
to say Blaster was a real, verified `rev` in `lake-manifest.json` fetched from a
public remote — *"branch names move; the manifest rev is what is checked"*. That
is **no longer true of either dependency**: `lake` does not verify the `rev` key
on a `"type": "path"` entry, so neither pin is machine-enforced. The revisions
above are the ones actually used to produce every number in this library, read
straight off the two working repositories; treat them as documentation, not as a
lock file.

Both changes are consequences of wsc-poc PR #112:

* PCB `9f9ca8c` → **`3fdd3fb`** — adds the CIP-153 **`ScaleValue`** builtin at flat
  tag **100**, without which the post-#112 `programmableSeize` script does not
  decode AT ALL, and fixes `unValueData`/`valueData` costs that were still on
  plutus 1.57 coefficients in an otherwise-1.63 table (task N5).
* Blaster `59db213` → **`4d320dd`** — the defect **D6** fix, without which the
  global prep at budget 1600 and the seize shaped prep both die in the kernel
  (tasks N5/N4).

Neither is optional and there is no fallback: at the earlier revisions three of
the six properties are not merely unproved, they are **unstatable**.

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

# …then the SECOND, incremental bundle (task N5) that adds ScaleValue:
git bundle verify  <CLAB>/WSC/substrate/pcb-scalevalue-3fdd3fb.bundle
git fetch          <CLAB>/WSC/substrate/pcb-scalevalue-3fdd3fb.bundle \
    'refs/heads/cip153-value-builtins:refs/heads/cip153-value-builtins'
git checkout cip153-value-builtins
git rev-parse HEAD         # 3fdd3fb5cb259f039b60cc584cd954de18c819dc
git rev-parse HEAD^{tree}  # 1c9d80221bd59fdd21ab132d1fcec086c7bbf3b9
```

### 1b. Blaster — NEW at task N6, and previously missing entirely

`Blaster` is no longer a public git require: it carries the D6 fix as one commit
on top of the public base. Until task N6 the repository shipped **no offline
artifact for it at all**, so `WSC/substrate/` did not in fact reconstruct the
substrate. It now does:

```bash
git clone https://github.com/input-output-hk/Lean-blaster /some/path/Lean-blaster-wsc
cd /some/path/Lean-blaster-wsc
git checkout 59db213ca6396269d2606b7dd9ac2bc26ae7c4ce   # the public base

git bundle verify  <CLAB>/WSC/substrate/blaster-d6-dite-4d320dd.bundle
git fetch          <CLAB>/WSC/substrate/blaster-d6-dite-4d320dd.bundle \
    'refs/heads/wsc-d6-dite-branch-retype:refs/heads/wsc-d6-dite-branch-retype'
git checkout wsc-d6-dite-branch-retype

git rev-parse HEAD         # 4d320dd5f70ac953945b5126f5cfd45128da8131
git rev-parse HEAD^{tree}  # 9550c96b0dff95096d07d29825a19d885fe7c6cd
```

Equivalently, `WSC/substrate/patches/0003-Optimize-DITE-re-type-branch-binders-D6.patch`
is the same commit as a `git am`-able patch (6,073 bytes).

Then point `lakefile.lean`'s `require Blaster from "…"` at that path.

**Caveat, stated because it is the kind of thing this document exists to catch:**
both bundles are INCREMENTAL and were verified with `git bundle verify` **against
the local working repositories**, which is the only check available offline. They
have NOT been verified against a fresh clone of either public remote, because
that needs network access this machine did not use. The prerequisite commits
(`9f9ca8c` for PCB's second bundle, `59db213` for Blaster's) are public, so the
fetch should succeed — but it is untested.

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
unapplied production scripts on `wsc-poc` `main` at commit
`f918ec6dcef4398952febe11e84fda089c064374` — the squash-merge of PR #110. Run
this exactly; every ref in it is fetchable from a plain clone:

```bash
git clone https://github.com/input-output-hk/wsc-poc /tmp/wsc-poc
W=/tmp/wsc-poc
REF=f918ec6dcef4398952febe11e84fda089c064374

for n in programmableLogicBase programmableLogicGlobal programmableSeize programmableTokenMinting; do
  git -C $W show $REF:generated/scripts/unapplied/prod/$n.json \
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

### 6.1 If you find `7ae0024` in the audit trail — why it is not the ref to use

The flats were **exported** at wsc-poc commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f`, on the PR #110 branch
`feat/van-rossem-bump`, and that is the SHA `WSC/AUDIT.md` §6.1 and
`WSC/flats/PROVENANCE.md` record, because it is what was measured at the time.
The **identical** bytes are on `main` at `f918ec6`, which is why the command
above uses `f918ec6` and why nothing here needs `7ae0024`.

PR #110 was squash-merged — the merge creates a new commit on top of the old
`main` tip, the branch's own commits never enter `main`'s history — and
`feat/van-rossem-bump` was deleted afterwards. So in your clone:

```bash
git -C /tmp/wsc-poc for-each-ref --contains 7ae0024b185cf16f17e38c20c9ee97ae1410c51f
# EMPTY — no branch, no tag. It is not in `git log main` and never will be.
```

You can still *ask GitHub* for it by name (both worked on 2026-07-26), because
GitHub retains pull-request refs and serves objects no branch points to:

```bash
git -C /tmp/wsc-poc fetch origin refs/pull/110/head              # FETCH_HEAD == 7ae0024
git -C /tmp/wsc-poc fetch origin 7ae0024b185cf16f17e38c20c9ee97ae1410c51f   # also works
```

Treat that as a convenience with no guarantee — PR refs and unreachable objects
can be pruned or repacked away, and the SHA does not exist at all in a mirror or
an archive tarball. **Do not build a verification procedure on it**; use
`f918ec6`, which is reachable from `main`.

The squash preserved the whole tree, not just these four files: `7ae0024` and
`f918ec6` share the tree `d86b6aa15e89fa989018d08b4e4bcd08ecc66e5f`
(`git diff 7ae0024 f918ec6` is empty). So the `file:line` source citations in
`WSC/Redeemer.lean`, `WSC/Shaped/MintingLocalShapedRIdx.lean` and the model
docstrings land on the same bytes at `f918ec6` as they did at `7ae0024`.

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
