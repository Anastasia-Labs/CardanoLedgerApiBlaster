# SUBMISSION 5 — the WSC proof library: WHERE SHOULD IT LIVE?

**This is the user's decision. Nothing below should be actioned without it.**

The question the task asked: *does the 137-module WSC proof library belong in
CardanoLedgerApiBlaster at all?* Part 1 answers it. Part 2 is the PR description for
whichever venue is chosen, written so it works for B, C or D with one paragraph swapped.

---
---

# PART 1 — THE PLACEMENT QUESTION

## 1.1 The facts, measured

| | value |
|---|---|
| WSC files tracked in CLAB | **228**, of which **131** are `.lean` (was 234/137; the H2 dead-file cleanup deleted 6 modules — `AUDIT.md` §12) |
| CLAB's *own* diff on this branch (everything not under `WSC/`) | **1,090 insertions** across 7 files, and 308 of those are `WSC.lean` — so the genuinely-CLAB part is **~780 lines** |
| reviewer-facing markdown under `WSC/` | ~**300 KB** across 12 top-level documents (`AUDIT.md` alone is 117 KB / 1,697 lines — it grew by §12, the H2 dead-file decision table) |
| build cost | **431 jobs, 1:49–2:00 wall, 1.50–1.66 GB RSS**, 93 WSC modules re-elaborated (432/94 before the H2 cleanup; the **162 verdicts are unchanged**) |
| hard external requirements | **Z3 4.15.2**, Blaster at a pinned rev, and PlutusCoreBlaster on an **unpublished** branch reached by **absolute local path** |
| trust surface it introduces | **51** `axiom` declarations, **101** `admit`-closed theorems, `sorryAx` under every top-level result |
| compiled third-party artifacts it ships | **17** `.flat` files (4 unapplied production validators + 13 applied golden programs) |
| CLAB's history | **3** merged PRs |

**The guest is roughly 30× the host, and it makes the host unbuildable for anyone who
does not already have the substrate.** That is the whole argument in one line.

## 1.2 What CLAB is, and what WSC is

CLAB is a general-purpose Lean model of the Cardano ledger API — `V1`/`V2`/`V3`
`TxInfo`, credentials, contexts, script purposes, the validity predicates. Its audience
is anyone verifying a Plutus script.

WSC is a verification *campaign* about one protocol's four validators. Its central
artifacts are (i) a machine-checked reduction of one English sentence to four leaf
obligations plus 28 named axioms, (ii) six bounded properties of specific compiled
bytecode, and (iii) — the audit's own view of the most valuable output — a
**machine-checked negative result about the technique**: `WSC/Coverage.lean` proves the
shape families do *not* cover real traffic, and the arithmetic says closing that gap by
enumeration costs ≈971 CPU-years for one property.

The two have a genuine relationship — WSC found and motivated CLAB's two bug fixes, and
CLAB is WSC's ledger vocabulary — but it is the relationship of a *consumer* to a
*library*, not of a module to its package. Nothing in WSC is reusable by another Plutus
project; everything in CLAB is.

## 1.3 The four options, with costs

### A. Status quo — `WSC/` stays a subdirectory of CLAB

**One-time cost:** zero.

**Recurring cost:** every CLAB contributor inherits a 2-minute build that needs Z3 and
an unpublished branch; CLAB's CI cannot run it, so either CI skips `WSC` (in which case
the library rots silently) or CI is impossible. CLAB's `#print axioms` surface acquires
51 axioms belonging to someone else's protocol. `git log` for a ledger-API library fills
with `WSC C4:` / `WSC F18:` commits.

**Reviewability: nil.** No maintainer will review 137 modules as one PR, and there is no
smaller unit — the library only builds as a whole.

**When A is right:** if CLAB is understood as an internal IOG scratchpad rather than a
library, and nobody outside this effort will ever consume it.

### B. Its own repository — e.g. `input-output-hk/wsc-containment-proofs` *(recommended)*

**One-time cost, itemised** — and it is smaller than it looks:

| step | cost |
|---|---|
| new `lakefile.lean` with two git `require`s (CLAB, PCB) + `lean-toolchain` | 30 min |
| move 234 files, `WSC/` → repository root or `WSC/` kept as-is | mechanical |
| fix cross-references: the ~30 `/home/gumbo` and `/tmp/claude` hits in `00-PLAN.md` §4.1–4.2 have to be fixed **for any option**, so this is not new cost | see §4 of the plan |
| CI: one job, `lake build WSC WSC.ShapeBridge`, needs Z3 in the image | 1–2 h |
| a `README.md` at root — `WSC/EXEC-SUMMARY.md` already **is** that document | 0 |
| delete `WSC/substrate/` and restore a git PCB pin | 15 min, and it closes defect D5 |

**Recurring cost:** its own CI minutes. Nothing else.

**Reviewability:** each repository is reviewable on its own terms. CLAB's two bug fixes
merge on their own merits in a day. The campaign's twelve reviewer documents become the
*point* of a repository rather than a 300 KB appendix to a library.

**Blocked on:** submission 1 merging (for the PCB git pin) and submission 2 merging (for
the CLAB git pin). Both are the same blockers option A has; B just makes them visible.

### C. A subdirectory of wsc-poc — e.g. `formal/`

**One-time cost:** add a Lean + Z3 toolchain to a Haskell/Nix repository — a real flake
and CI change, and the one thing wsc-poc's build currently does not have. Plus a
**self-referential pin**: the proofs are about bytecode exported from wsc-poc at commit
`f918ec6` on `main`, so the proofs would live in the repository whose later commits invalidate
their own fixtures. That is manageable (pin the sha in `PROVENANCE.md`, which is already
done) but it is a new maintenance obligation on the wsc-poc team every time a validator
changes.

**Genuine benefit, and it is not small:** the proofs sit next to the validators they are
about, the provenance chain becomes an in-repo path, and **the team that will actually
cite this artifact owns it**. If the deliverable's purpose is "the WSC team can point an
auditor at a formal-verification result", C is the option that makes that easiest.

**Reviewability:** good for the wsc-poc team, poor for anyone else — a Lean directory in
a Haskell repository is not where a formal-methods reviewer looks.

### D. Not shipped — private handoff only *(recommended as the interim)*

Ship submissions 1, 2, 3 and 4 upstream. Hand the proof library over as a tarball or a
git bundle, with `WSC/substrate/` included (that is exactly what it is for) and
`WSC/status-fragments/` included (a private handoff is the one place they belong).

**Cost:** nothing external is reviewable, and the audit's "reproducible by a third party"
claim stays theoretical — the substrate bundle's *custody* remains the trust anchor,
which the audit already flags (`AUDIT.md` §6.2, D5 MEDIUM/PARTIALLY REPAIRED).

**When D is right:** now. It is right *now* regardless of which of A/B/C is chosen later,
because B and C are both blocked on submission 1 merging and D is not blocked on
anything.

## 1.4 Recommendation

**B, with D as the interim.** Four reasons, in order of weight:

1. **The audit's own §11.1 says the durable asset is the reduction plus a negative result
   about the technique.** That is a research artifact with its own audience. It has a
   `README`, an `AUDIT.md`, a `COVERAGE.md` and a "what a reviewer should not believe"
   register — it is *already shaped like a repository*, and it is not shaped like a
   feature of a ledger-API library.
2. **B is the only option under which submission 2 merges soon.** Two small, genuinely
   valuable, independently verified bug fixes should not queue behind a 137-module
   review, and under option A they necessarily do.
3. **WSC hard-requires an unpublished branch by absolute path.** Under A, that makes
   *CLAB* — a library other people are supposed to use — unbuildable. Under B the
   non-portability is confined to the repository that owns it, and disappears entirely
   once submission 1 merges.
4. **The migration is cheap relative to the campaign** and most of its cost (the
   `/home/gumbo` scrub) has to be paid under every option anyway.

**Second choice: C**, and it becomes first choice if the answer to "who will cite this in
two years?" is "the WSC team, to an auditor". The deciding question is about audience,
not engineering, which is exactly why this is the user's call.

**Against A**, on the record: option A is the only one under which the library's
existence makes a *different* deliverable worse.

## 1.5 What must happen under every option

Independent of the venue:

* the `/home/gumbo` and `/tmp/claude` scrub — `00-PLAN.md` §4.1, §4.2 (**53 lines / 17
  files**);
* the absolute-path `require` retired — §4.0 B1/B2/B3;
* `WSC/status-fragments/` and `WSC/CIP153-BUILTINS-REPORT.md` dropped from any public
  tree — §4.4 I1, I2;
* `WSC/substrate/` deleted once submission 1 merges — §4.4 I4;
* three small `README`s written — `WSC/Shaped/Probe/` (which three modules deliberately
  fail), `WSC/goldens/pre-fix/` (why deliberately-invalid vectors are retained), and
  `WSC/SPIKE-FINDINGS.md`'s header (superseded substrate, `Tests/Spike/` never
  committed) — §4.4 I3, I5, I6.

---
---

# PART 2 — PR / REPOSITORY DESCRIPTION (use once the venue is chosen)

> **Swap the first paragraph** for the venue: "This PR adds…" (A), "This is the initial
> import of…" (B), "This PR adds `formal/`…" (C). Everything else is venue-independent.

## Summary

A machine-checked verification campaign over the **real compiled production bytecode** of
four programmable-token validators. It does **not** prove the target claim. What it
establishes, precisely, is three things — and a fourth that is a negative result about
its own method.

The target sentence is: *in an honest deployment, programmable tokens cannot exist
outside the mini-ledger.*

1. **The sentence is reduced, by machine, to four leaf obligations plus 28 named
   assumptions** (`Composition.top_claim`; 26 for the weakest form). The reduction is the
   durable asset: anyone who later discharges the four leaves over an unrestricted class
   gets the sentence. **The 28 are a floor, not a ceiling** — they are what today's proof
   term consumes.
2. **Six safety properties (P1–P6) of the four production validators are proved against
   the real compiled bytecode**, whose byte-identity to the deployment is verified
   cryptographically (sha256, 4/4, re-verified at four separate audits).
3. **All four leaf obligations are discharged with no remaining hypothesis over two
   node-realizable classes** — one transfer, one seize. **On each side exactly one of the
   four leaves is carried by the bytecode; the other three hold because the class is too
   narrow for them to arise.** One quarter code, three quarters narrowness. **Quote the
   ratio, never "zero remaining obligations" alone.**
4. **The classes provably do not cover real traffic.** `WSC/Coverage.lean` states coverage
   in Lean and **refutes** it at the smallest bound the family itself covers, exhibiting
   three ledger-valid, Conway-redeemer-exact transactions that the production bytecode
   accepts in **exactly the certified witness's 2,603 CEK steps** and that lie outside all
   the re-cut shapes. Two differ from a covered transaction only by a **list length**; one
   only by a **constructor tag**. Enumerating the gap costs ≈**971 CPU-years** for one
   property at the measured 3.3 s/shape. **0 project axioms, no `sorryAx`.**

Item 4 is, in the campaign's own assessment, the most valuable output: it is a negative
result the project produced about itself, and it is the reason the standing recommendation
is **not** to start a shape-coverage programme.

## Build state

```
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
lake build WSC WSC.ShapeBridge
```

| measurement | value |
|---|---|
| exit status | 0 — **431 jobs** (432 before the H2 cleanup) |
| wall clock | **1:49–2:00** over two runs post-H2 (1:46–2:10 at `f4486ca`) — quote the range, never a point |
| solver verdicts | **162** = **103 `✅ Valid`** + **59 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` | **0** |
| `error:` lines | **0** |
| `declaration uses 'sorry'` | **20** — *not a census*, see caveats |
| `unused variable` | **5**, all at `Composition.lean:2442-2446` — Lean's own confirmation that one `LeafSet`'s acceptance hypotheses are unused |
| WSC modules re-elaborated | **93** (94 before the H2 cleanup) |
| max RSS | **1.50–1.66 GB, load-dependent** — explicitly *not* an instrument |

Every one of the 13 re-cut shapes meets a four-point bar: the theorem reports
`✅ Valid`; a vacuity probe at **its own** prep term **and its own** shape builder reports
`✅ Expected Falsified`; a concrete accepting CEK witness exists with the exact step count
`K` pinned **two-sided** (halts at `K`, budget-errors at `K−1`); and a shape-realizability
theorem exists.

## Requires

* **Z3 4.15.2**, Lean **4.24.0**;
* Blaster at rev `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`;
* PlutusCoreBlaster **with the CIP-153 `Value` builtins** — without flat tags 94–99 the
  global validator's bytecode **does not decode at all** (`Could not decode program!`,
  committed as a negative control). *[If submissions 1/2 are not yet merged: this
  library does not build until they are; the pins are `<sha>` and `<sha>`.]*

## Caveats — read these before quoting anything

Taken verbatim from the campaign's own audit, which is the authoritative document
(`WSC/AUDIT.md` §9, §11.2). They are stated here rather than buried:

* **"Machine-checked" does not mean kernel-checked.** **101** theorem-position results are
  closed by the solver's `admit`; **every** top-level theorem carries `sorryAx`. What
  certifies them is a `✅ Valid` line in a build log. This is a defensible engineering
  trade — it is what makes analysing real compiled bytecode affordable — but it is not a
  kernel proof. **The build's own 20 `sorry` warnings badly understate it: 38 modules set
  `warn.sorry false`.** The instrument is `#print axioms`, parsed **across newlines** *and*
  for **both** of its output forms.
* **The theorems and the executions are not about the same term.** Shaped theorems are
  stated on `.prop` (the optimizer's output); every witness and every measured `K` is on
  `.exec`. Their equality is **unproved** and deliberately not axiomatized, and it binds
  **both** composed results.
* **`OnChain` and `Deployed` are opaque axioms.** No term here proves any context is
  genuinely on-chain or any hash genuinely deployed. Fees, witness-set agreement and the
  UTxO set are unmodelled.
* **Every bytecode result is bounded twice** — by a CEK step budget *and* by a frozen
  `Data` skeleton. Quote both bounds or neither. One load-bearing theorem provably does
  not generalise.
* **The redeemer-coverage predicate is the all-Plutus specialisation of Conway's rule, not
  the rule.** It is conservative where used positively; six emptiness results are strictly
  weaker than they read and now carry an explicit non-native side condition **in their
  types**.
* **The shapes were not chosen neutrally.** `SizeBound`'s five dimensions are a modelling
  decision. If an overclaim is hiding anywhere, it is there.
* **One theorem must not be quoted:** `P4_local_noEscape_shapedIdx` (SHAPE L2) ranges over
  a class **proved empty**. Cite `P4_local_noEscape_RIdx` (SHAPE L2R) instead — and carry
  its two riders: the headline is derived from a `✅ Valid` *negative control* rather than
  a direct verdict, and one conjunct at that shape is `⚠️ Undetermined` and is **not**
  asserted.

## Known defects, open

| id | severity | summary |
|---|---|---|
| coverage | **CRITICAL** | not merely absent — **proved false** at the smallest bound the family covers. The binding constraint on the whole deliverable. |
| the ratio | **CRITICAL** | 1 of 4 leaves is the bytecode, 3 are the shape, on each side. For the general class nothing is proved. |
| upstream `dite'` | **HIGH** | the optimizer emits a kernel-ill-typed term on symbolic CIP-153 `Value` results, blocking two shape families and two of three containment code paths. Filed upstream — see `02-blaster-PR-d6-dite-motive.md`. |
| `.prop` vs `.exec` | MEDIUM | unproved, binds both composed results |
| `"sorry"-free` | MEDIUM | false by nature, quantified above |
| substrate custody | MEDIUM | *closes when submission 1 merges* |

## Reproduction

`WSC/REPRODUCE.md` is the third-party recipe. `WSC/AUDIT.md` §10 is the census recipe,
including the two `#print axioms` parsing traps that cost previous audits time (parse
across newlines; handle the bracket-free "does not depend on any axioms" form) and the
`:= by`-newline trap in the verdict count (**six** tactic sites are written with `blaster`
on the following line, one of them with an argument, so no single grep finds all 162).

## Document map

| file | what it is |
|---|---|
| `WSC/AUDIT.md` | **authoritative** — clean-room rebuild, five censuses, provenance, per-unit verification, ranked findings, "what a reviewer should not believe" |
| `WSC/STATUS.md` | the per-property table; read after `AUDIT.md` |
| `WSC/README.md` | reviewer-facing summary |
| `WSC/EXEC-SUMMARY.md` | one page, plain English, no formal-methods vocabulary |
| `WSC/COVERAGE.md` | the coverage question and its answer |
| `WSC/ARCHITECTURE.md` | binding design record (ADDENDUM v3 overrides the base text) |
| `WSC/REPRODUCE.md`, `WSC/flats/PROVENANCE.md`, `WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md` | reproduction and provenance |
| `WSC/SHAPE-BRIDGE.md`, `WSC/SHAPING-RESULTS.md`, `WSC/LR-CTX-AUDIT.md` | technique records |
