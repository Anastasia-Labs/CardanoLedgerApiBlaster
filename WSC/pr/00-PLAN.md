# PR SUBMISSION PLAN — the WSC containment campaign, unbundled

**Written at task H2 (2026-07-26), against CardanoLedgerApiBlaster branch
`wsc-containment-proofs` HEAD `4b49706` (verified), PlutusCoreBlaster branch
`cip153-value-builtins` HEAD `9f9ca8c` (verified), wsc-poc worktree branch
`fix/benchmark-arity-and-ctx-builder` HEAD `c18c525` (verified).**

Everything asserted below was measured in this task or is cited to a file and line
that was read in this task. Where a claim is inherited from a document rather than
re-measured, it says so. Nothing here has been pushed to any remote and no PR has
been opened or edited.

---

## 0. The one-paragraph answer

The work spans three repositories and decomposes into **four upstream submissions plus
one placement decision**. Two of the four are clean, self-contained, independently
valuable, and can be submitted essentially now: the **CIP-153 Value builtins** to
PlutusCoreBlaster and the **two ledger-API bug fixes** to CardanoLedgerApiBlaster.
One is a **defect report against Blaster**, not a PR. One is a **bug-fix PR to
wsc-poc**, the user's own repository, which is ready as measured (67/18/2 test suites
pass at `c18c525` — re-run in this task). The **137-module WSC proof library** is the
hard case: it is an application-specific artifact currently living inside a
general-purpose ledger-API library, it cannot build without an unpublished branch, and
where it should live is a decision for the user, not for this plan. Section 3 gives
four options with costs and a recommendation.

---

## 1. SUMMARY TABLE

| # | Deliverable | Repo | Branch → base | Scope | Blockers | Order |
|---|---|---|---|---|---|---|
| **1** | CIP-153 `Value` builtins (6 of 7), flat tags 94–99, CEK denotations, cost arms, ~45 unit tests, `Value/Algebra.lean` | `input-output-hk/PlutusCoreBlaster` | `cip153-value-builtins` → `main` (`a04042c`, **is** today's `origin/main`) | 17 files, **+2832/−6**, 2 commits | **48 `simp` lint warnings in the branch's own new files** (§4.1); D/E cost variants carry A/B/C numbers; local checkout is a **shallow clone** | **1st** (or in parallel with 2) |
| **2** | Two ledger-API bug fixes: script-purpose / credential **ordering**, and the Conway **exact-redeemer** rule (`MissingRedeemers`/`ExtraRedeemers`) | `input-output-hk/CardanoLedgerApiBlaster` | new branch cut from `main` (`5dab3c4`) — **do not use `wsc-containment-proofs`** | 3 files under `CardanoLedgerApi/`, ~**+720/−20**, from commits `d853256` + `755d75e` + the CLAB half of `9e5d417` | **No self-contained tests exist** — all empirical evidence lives in `WSC/` (§4.3). One new `Tests/` module must be written. | **1st** (independent of 1) |
| **3** | Defect report **D6** — kernel-ill-typed `Blaster.dite'` on symbolic CIP-153 `Value` results | `input-output-hk/Lean-blaster` | **an issue, not a PR** | 2 named reproductions already in-tree | none — file any time | any time; **gates future WSC work only** |
| **4** | Benchmark arity fix (4 cases, 2 validators) + 3 ledger-invariant fixes in the `ScriptContext` builder | `input-output-hk/wsc-poc` | `fix/benchmark-arity-and-ctx-builder` → `main` (`f918ec6` = merged #110) | 1 commit `c18c525`; **plus 1 unrelated commit `97160f8`** (nix) that must be split out | **verified green in this task**: `cabal build all` OK, **67/67 + 18/18 + 2/2** | any time — **independent of all Lean work** |
| **5** | The **WSC proof library** (137 Lean modules, 234 files, ~300 KB of reviewer docs) | **decision required** — see §3 | n/a | the rest of `wsc-containment-proofs` | needs **1** merged (won't decode without it) **and** **2** merged (consumes both fixes); needs the absolute-path `require` retired | **last** |

### Merge order, stated as a sequence

```
   ┌─ 1  PCB: CIP-153 Value builtins ─────────┐
   │                                          │
   ├─ 2  CLAB: two ledger-API bug fixes ──────┤──►  5  WSC proof library (venue TBD)
   │                                          │
   ├─ 3  Blaster issue: D6  (no PR) ──────────┘        (needs 1 merged for a git pin;
   │                                                     needs 2 merged to consume the fixes)
   └─ 4  wsc-poc: benchmark + builder fixes   (fully independent — merge whenever)
```

1, 2, 3 and 4 have **no dependency on each other**. 5 depends on 1 and 2.

---

## 2. THE FOUR SUBMISSIONS — one file each

| file | what it is |
|---|---|
| `01-pcb-cip153-value-builtins.md` | PR description + a maintainer-readiness assessment (the four things a PCB maintainer will ask about, answered) |
| `02-blaster-issue-d6-dite-motive.md` | issue text for `input-output-hk/Lean-blaster`, with both reproductions and the diagnosed root cause |
| `03-clab-ledger-api-fixes.md` | PR description for the two bug fixes, with the ledger citations, plus the test work that must be written first |
| `04-wsc-proof-library-placement.md` | the four venue options with costs, a recommendation, and the PR description for whichever venue is chosen |
| `05-wsc-poc-benchmark-arity-and-ctx-builder.md` | PR description, with this task's re-verification |
| `06-wsc-poc-nix-haskell-nix-bump.md` | PR description for the commit that must be split out of 05 |

---

## 3. DOES THE WSC PROOF LIBRARY BELONG IN CardanoLedgerApiBlaster?

**Short answer: no, and this is the user's decision, not mine.** Reasoning and the
cost of each alternative are in `04-wsc-proof-library-placement.md`; the summary:

| option | one-time cost | recurring cost | reviewability |
|---|---|---|---|
| **A. status quo** — `WSC/` stays a subdirectory of CLAB | zero | every CLAB contributor inherits a **1:46–2:10** build needing **Z3 4.15.2** and an unpublished PCB branch; 51 axioms and 101 `admit`-closed theorems land in a general-purpose library | **nil** — no maintainer will review 137 modules as one PR |
| **B. own repository** (recommended) | new lakefile + 2 git `require`s, move 234 files, fix ~30 cross-references, new CI | its own; CLAB stays clean | each repo reviewable on its own terms |
| **C. subdirectory of wsc-poc** | add a Lean + Z3 toolchain to a Haskell/Nix repo; a self-referential bytecode pin | wsc-poc CI grows a Lean job | good for the WSC team, poor for anyone else |
| **D. private handoff only** (interim) | zero | nothing is externally reviewable | nil, by design |

**Recommendation: B, with D as the interim until PCB submission 1 merges.** The
decisive facts are (i) the campaign's own `AUDIT.md` §11.1 says the durable asset is a
*reduction* plus a *negative result about the technique* — a research artifact with its
own audience, not a feature of a ledger-API library; (ii) CLAB's non-WSC diff on this
branch is ~1,090 lines against WSC's 137 modules, so the guest is roughly 30× the
host; (iii) WSC hard-requires an unpublished PCB branch by absolute path, so folding it
into CLAB makes **CLAB** unbuildable for anyone without that substrate; and (iv) B is
the only option under which submission 2 — two small, genuinely valuable bug fixes —
can merge *now* instead of waiting behind a 137-module review.

---

## 4. WHAT MUST NOT SHIP, OR MUST BE RELABELLED

Complete `git grep` over tracked files in all three repositories. **PlutusCoreBlaster
is clean: zero hits for `/home/gumbo` and zero for `/tmp/claude`.** wsc-poc has hits in
exactly one file, and that file is already on `origin/main`. CLAB has **53 matching
lines across 17 files** for `/home/gumbo` and **3 lines in 3 files** for `/tmp/claude`.

### 4.0 Hard blockers — a PR cannot contain these

| # | hit | recommendation per PR variant |
|---|---|---|
| B1 | `lakefile.lean:70` — `require PlutusCore from "/home/gumbo/iohk/PlutusCoreBlaster"` | **submission 2 (CLAB fixes): do not touch `lakefile.lean` at all** — branch from `main`, whose line 8 already reads `require PlutusCore from git "…/PlutusCoreBlaster" @ "main"`. **Submission 5 (WSC): must become** `require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "<sha on main after submission 1 merges>"`. |
| B2 | `lake-manifest.json:23` — `"dir": "/home/gumbo/iohk/PlutusCoreBlaster"` on a `"type": "path"` entry | same split. For 5, regenerate with `lake update PlutusCore` **after** B1, then commit the regenerated manifest; do not hand-edit. The `"rev"`/`"inputRev"` keys E3 added to the path entry become redundant once the entry is a git entry — drop them. |
| B3 | `lakefile.lean:9-66` — the 58-line `SUBSTRATE PIN` comment block, which names the absolute path twice (`:21`, and again in the "restore a real git pin" instruction) | **delete the whole block** in the same commit as B1/B2, replacing it with 3–4 lines: the PCB rev, what depends on it (the global validator does not decode without tags 94–99), and the negative control. Everything else in that block exists only to describe the unpublished-branch workaround and dies with it. |

### 4.1 Absolute local paths in Lean docstrings and `.disabled` sources

| # | file:line | current | must become |
|---|---|---|---|
| P1 | `WSC/Model/GlobalModel.lean:17` | `/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d/src/…/ProgrammableLogicBase.hs` | `input-output-hk/wsc-poc @ 7ae0024 — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs` |
| P2 | `WSC/Model/SeizeModel.lean:19` | same worktree prefix | same treatment |
| P3 | `WSC/Honest.lean:359` | `/home/gumbo/playground/cardano-ledger @ cd8b7fab8` | `IntersectMBO/cardano-ledger @ cd8b7fab8` |
| P4 | `WSC/goldens/KMeasure.lean.disabled:152-164` | **13** `#import_uplc … "/home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens/applied/*.flat"` | `<REPO>/WSC/goldens/applied/…` with a one-line `sed` recipe in the module header. (Blaster's `#import_uplc` path handling was not tested for relative paths in this task — **verify before assuming a relative path works.**) |
| P5 | `WSC/goldens/KVerify.lean.disabled:58-70` | **13** more of the same | same |
| P6 | `WSC/goldens/KMeasure.lean.disabled:9-10` | `<SCRATCH> = /tmp/claude-1000/-home-gumbo-…/scratchpad` and an absolute CLAB inputs path | `<SCRATCH>` placeholder, unexpanded |
| P7 | `WSC/goldens/verify-applied.py:8` | `gdir = "/home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens"` | `gdir = os.path.dirname(os.path.abspath(__file__))` — **one line, mechanical, patch written and tested in this task but deliberately not committed; see §6** |

### 4.2 Absolute local paths in markdown

All of the following are provenance records whose *content* is correct and worth
keeping. The fix is uniformly: **replace the absolute path with `<org>/<repo> @ <sha>`
or with a `<SCRATCH>` / `<REPO>` placeholder.** None should be deleted.

| # | file:line(s) | what it names |
|---|---|---|
| M1 | `WSC/ARCHITECTURE.md:589, 612` | the PCB local path + the `require` line |
| M2 | `WSC/AUDIT.md:122` | `cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-E5` → `cp -a <REPO> <SCRATCH>/clab-audit` |
| M3 | `WSC/AUDIT.md:1042` | the cardano-ledger checkout path |
| M4 | `WSC/REPRODUCE.md:70` | the `require` line a third party must edit — **this one disappears entirely** once B1 lands |
| M5 | `WSC/substrate/README.md:122` | the PCB path — **this whole directory goes away**, see §4.4 |
| M6 | `WSC/flats/PROVENANCE.md:5, 32, 84, 91` | the wsc-poc worktree (×2) and the PCB path (×2). The worktree hits should become `wsc-poc @ 7ae0024`, which is what the provenance actually depends on. |
| M7 | `WSC/goldens/K-MEASUREMENTS.md:81, 499, 582` | the PCB path ×3 |
| M8 | `WSC/goldens/K-MEASUREMENTS.md:84` | a literal `/tmp/claude-1000/…/scratchpad` → `<SCRATCH>` |
| M9 | `WSC/goldens/MANIFEST.md:45, 73, 190` | the wsc-poc worktree, the CLAB goldens dir, the PCB path |
| M10 | `WSC/SPIKE-FINDINGS.md:5` | a literal `/tmp/claude-1000/…` **from a different session id** — and see §4.4, this file is a drop candidate anyway |
| M11 | `WSC/CIP153-BUILTINS-REPORT.md:3` | the PCB path + "not pushed" — and see §4.4 |

### 4.3 wsc-poc

One file, and it is not a docstring: **`doc/plutarch-van-rossem-backport.patch`** has
**12 matching lines** for `/tmp/claude-1000/…/scratchpad/plutarch-163/…` in its `diff -ru`
headers and `+++` lines. This file is **already on `origin/main`** (it shipped with
merged PR #110), so it is not a blocker for submission 4 and is out of that PR's scope.
**Recommendation: a separate one-line-per-header cleanup PR**, regenerating the patch
with `git diff` inside a checkout instead of `diff -ru` across two directories, so the
headers read `a/Plutarch/…` / `b/Plutarch/…`. Flagged rather than fixed here: it is not
this task's file and rewriting a shipped patch file risks invalidating the reference.

### 4.4 Internal campaign process artifacts — do not ship in a public PR

| # | path | size | disposition |
|---|---|---|---|
| I1 | `WSC/status-fragments/` (7 files: `U1`, `U2`, `V1-P1-shaped`, `V3`, `V4`, `z6-p2shaped`, `C1-global-realizable`) | 81 KB | **drop from a public tree.** They are per-task fragments explicitly superseded by `STATUS.md` ("kept as the per-task record"), they are named by internal task codename, and where they disagree with the sealed documents the sealed documents win (`AUDIT.md` §7, §8). Keep them in `git log` and in any private handoff. |
| I2 | `WSC/CIP153-BUILTINS-REPORT.md` | 7.8 KB | **do not ship as-is.** It is a per-task report about *PlutusCoreBlaster* work, sitting in CLAB, whose first line is an absolute path plus "not pushed". Its durable content is the basis of `01-pcb-cip153-value-builtins.md` and should travel there, in the PR body and optionally as a short `PlutusCore/Value/README.md` in PCB. |
| I3 | `WSC/SPIKE-FINDINGS.md` | 14 KB | **relabel or drop.** It is a spike report at a superseded substrate (CLAB `main` @ `5dab3c4`, PCB `main` @ `4ef4860`) describing 34 experiment files under `Tests/Spike/` that **are not in the tree**, and it names a scratch workspace from an unrelated session. But it is **cited 10 times from shipped Lean and markdown** (`P3_Base.lean:50,102`, `P1Shaped.lean:177`, `P4LocalShaped.lean:167`, `P6ShapedR.lean:45`, `Goldens/Witnesses.lean:44`, `ShapeBridge.lean:1611,1642`, `SHAPING-RESULTS.md:339`, `K-MEASUREMENTS.md:3`), so **dropping it dangles ten references.** Recommendation: keep it, add a three-line header saying it is a historical spike at a superseded substrate and that `Tests/Spike/` was never committed, and fix M10. |
| I4 | `WSC/substrate/` (bundle 39,068 B + `patches/` + `README.md`) | 45 KB | **do not ship in a public PR.** The audit itself calls this appropriate for a private handoff (§6.2), and it exists for exactly one reason: PCB's branch is unpublished. **Delete it in the same commit that lands B1/B2** and say so in the PR body — that deletion *is* the closure of defect D5. Until submission 1 merges it is the trust anchor and must travel with any private handoff. |
| I5 | `WSC/goldens/pre-fix/` (14 files) | — | **keep, but add a `README`.** These are the deliberately-invalid pre-fix golden vectors, and they are load-bearing: `RealizableShapes.all_old_witnesses_fail_c3_coverage` is a shipped theorem about them. Without one paragraph of explanation a reviewer will read them as stale duplicates of `WSC/goldens/*.json`. |
| I6 | `WSC/Shaped/Probe/` (43 modules, of which **3 deliberately do not build**: `T3PrepFAILS`, `T4PrepFAILS`, `BridgeProbe2FAILS`) + `WSC/goldens/prep-probes/` (9 `.lean.disabled`) + `WSC/goldens/ctx-audit/*.py` | — | **keep, add `WSC/Shaped/Probe/README.md`.** Several are load-bearing as *records*: `G6Vacuous2500.lean` is the vacuity cautionary tale `AUDIT.md` §4 opens with, `T3PrepFAILS`/`T4PrepFAILS` are the D6 reproductions submission 3 cites, `L2RProbe.lean` is the record of L2R's `⚠️ Undetermined`. But a reviewer's first `lake build` of a `*FAILS*` module looks like a broken repository unless the README says which three are expected to fail and that **none of the 43 is imported by `WSC.lean`** except `Probe.S1K` (`WSC.lean:127`). |
| I7 | `.gitignore` `+.wsc-build.log` / `+.wsc-build.sh` | 4 lines | harmless; **keep in submission 5, drop from submission 2.** Names a local-only helper that is not in the tree. |
| I8 | `WSC/flats/*.flat` (4) and `WSC/goldens/applied/*.flat` (13) | 13 KB + | **keep.** Production bytecode, byte-identical to the deployed scripts (sha256 4/4, `AUDIT.md` §6.1), and it is the campaign's strongest single fact. Not secret — it is on chain and in wsc-poc's `generated/`. Note, though, that shipping 17 compiled application scripts into a general-purpose ledger-API library is another argument for §3's option B. |

---

## 5. WHAT EACH PR MUST SAY ABOUT ITS UNMERGED DEPENDENCIES

* **Submission 1 (PCB)** — it has none. One sentence is still owed the maintainer:
  *"a downstream Lean verification effort needs flat tags 94–99 to decode a production
  PlutusV3 script; that consumer is not part of this PR and is not required to review
  it."* Do **not** cite `WSC/` paths — they do not exist in PCB.
* **Submission 2 (CLAB fixes)** — must say the two defects were found by a downstream
  formalization that is **not in this PR**, and that the differential evidence (13/13
  goldens, both directions) lives there. Must therefore carry **its own** tests
  (§4.3 of `03-…md`) and must not reference any `WSC/` path. Must not touch
  `lakefile.lean`, `lake-manifest.json`, `.gitignore` or `WSC.lean`.
* **Submission 3 (Blaster issue)** — must state that the two reproductions live in an
  unpublished repository and **inline the failing terms and the diagnosis** so the
  issue stands alone. Cite Blaster's own files (`Optimize/Rewriting/OptimizePropNot.lean:53`,
  `Optimize/Decidable.lean:36,43`) which the maintainer can read.
* **Submission 4 (wsc-poc)** — `c18c525`'s message currently cites
  *"CardanoLedgerApiBlaster WSC/LR-CTX-AUDIT.md"*, a path in a repository the reviewer
  cannot open. **Reword to name the finding, not the path** (or keep the path and add
  "private formalization repo, not yet public"). Otherwise fully independent.
* **Submission 5 (WSC)** — must say, in the first paragraph, that it **does not build**
  until 1 and 2 are merged; must carry the two resulting git pins; and must state that
  `WSC/substrate/` was deleted because submission 1 retired the need for it.

---

## 6. WHAT THIS TASK ACTUALLY CHANGED

Committed: **the six plan files in `WSC/pr/`** (this file + five) and nothing else. The
task's commit scope was `WSC/pr/*` and that scope is honoured literally.

**One patch prepared, tested, and deliberately NOT committed** — P7, the only
`/home/gumbo` hit in the whole tree that is fixable without touching Lean or a sealed
document. It is out of the stated commit scope, so it is left here as a turnkey patch
rather than landed. `WSC/goldens/verify-applied.py` is a standalone script that no Lean
module imports and no build target reaches, so applying it cannot disturb the seal.

```diff
--- a/WSC/goldens/verify-applied.py
+++ b/WSC/goldens/verify-applied.py
@@ -5,7 +5,9 @@
 import json, sys, os, collections
 
 log = sys.argv[1]
-gdir = "/home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens"
+# The golden JSONs live next to this script; derive the directory rather than
+# hard-coding it, so the script is portable (task H2).
+gdir = os.path.dirname(os.path.abspath(__file__))
 
 args = collections.defaultdict(dict)
 for line in open(log):
```

Tested: `ast.parse` clean, and a smoke run against `/dev/null` enumerates all 13 golden
JSONs from the derived directory (reporting `MISSING` for each, which is the correct
answer for an empty log). `import os` is already present at line 5 — no new import needed.

Deliberately **not** done, with reasons:

* **No Lean file was edited, moved or deleted** — a parallel agent owns removals, and
  every candidate in §4.1 P1–P6 is inside a Lean docstring where an edit forces a
  module re-elaboration and therefore a rebuild to re-verify. They are named to the
  line instead.
* **No markdown relabelling (§4.2)** — M1–M11 span the four sealed reviewer documents
  (`AUDIT.md`, `STATUS.md`, `ARCHITECTURE.md`, `REPRODUCE.md`). Editing sealed
  documents is not mechanical preparation; the seal is the invariant this task was told
  not to disturb. They are named to the line instead.
* **`WSC/substrate/` and `WSC/status-fragments/` were not deleted** — removals belong
  to the parallel agent, and I4 must not be deleted before submission 1 merges anyway.
* **The 48 `simp` lint sites in PCB were not fixed** — they are in a different
  repository and my commit scope is `WSC/pr/*`. The exact tally is in
  `01-…md` §4.1 and is reproducible from one `lake build`.
* **Nothing was pushed and no PR was opened, viewed for editing, or modified.**
  `gh pr view` was used read-only on merged PRs #108–#110 to establish house style.

## 7. MEASUREMENTS TAKEN IN THIS TASK

| what | result |
|---|---|
| CLAB HEAD | `4b497062d0aa30ef5a994fd8208c9a19446105b2`, branch `wsc-containment-proofs`, tree clean |
| CLAB `origin/main` | `5dab3c4` — the branch's merge-base; the entire branch is unpushed |
| PCB HEAD | `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`, branch `cip153-value-builtins`, base `a04042c` **= today's `origin/main`** (no rebase needed) |
| PCB clean-room build (scratch `cp -a`) | `lake build` → **284 jobs**, exit 0; `lake build Tests` → **292 jobs**, exit 0 |
| PCB warnings | **1** `declaration uses 'sorry'` (`CekMachine.lean:299:4`, pre-existing) + **48** `This simp argument is unused` in the branch's own new files (45 in `Value/Algebra.lean`, 3 in `Value/Basic.lean`) |
| wsc-poc branch | `c18c525`, **2** commits ahead of `origin/main` (`f918ec6` = merged #110): `c18c525` (the fix) and `97160f8` (nix) |
| wsc-poc build | `cabal build all --extra-lib-dirs=/usr/local/lib` → exit 0 |
| wsc-poc tests | `programmable-tokens-test` **67/67 PASS**, `regulated-stablecoin-test` **18/18 PASS**, `aiken-example-test` **2/2 PASS** |
| `git grep '/home/gumbo'` (matching lines / files) | CLAB **53 / 17**; PCB **0 / 0**; wsc-poc **0 / 0** |
| `git grep '/tmp/claude'` (matching lines / files) | CLAB **3 / 3**; PCB **0 / 0**; wsc-poc **12 / 1** — `doc/plutarch-van-rossem-backport.patch`, confirmed already on `origin/main` at `f918ec6` |

The sealed WSC build was **not** re-run in this task, and did not need to be: **no
tracked file outside `WSC/pr/` was modified, added or deleted**, so the 432-job /
162-verdict invariant is untouched by construction rather than by measurement.
