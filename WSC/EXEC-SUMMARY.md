# Programmable-token containment: formal verification — executive summary

> # ⚠️ POST-#112 (task N6, 2026-07-28) — READ `WSC/AUDIT.md`'s BANNER FIRST
>
> This file was written against the PRE-#112 wsc-poc bytecode. wsc-poc PR #112
> (`main` @ **2306678**) changed three of the four validators SEMANTICALLY; the
> minting policy is byte-identical. Tasks N1–N6 re-based everything.
>
> **The current measurements are (task H2, 2026-07-28): 444 jobs, 0 errors,
> `175` solver verdicts (`110 ✅ Valid` + `65 ✅ Expected Falsified`),
> 0 `⚠️`/`❌`, 20 `sorry`, 5 unused-variable, 106 WSC modules, two clean-room
> runs, wall 10:25 / 10:35, peak RSS ≈ 4.35 GB.**
> The delta over the N6 census (440 / 170 / 102) is tasks H1 (SHAPE T8R's
> certified inhabitant — no new solver verdicts) and H2 (SHAPES T3R/T4R:
> +3 modules, +2 `✅ Valid`, +3 `✅ Expected Falsified`). Both composed results survive with **28** project axioms
> each and **1 of 4** leaves discharged by the bytecode on each side — unchanged
> — but `top_claim` now carries one NEW hypothesis, `WdrlPairShaped Shape`.
>
> Everything that changed, with measurements: `WSC/AUDIT.md` (top banner) and
> `WSC/status-fragments/N6-compose-and-reaudit.md`. Numbers in the body below
> that disagree with the ones above are the pre-#112 record.

---


*One page, plain English, no formal-methods vocabulary and no code names. The full,
technical and deliberately self-critical account is in `WSC/AUDIT.md`, which is
authoritative; `WSC/README.md` is the reviewer-facing version; `WSC/STATUS.md` is the
per-property table.*

---

## What changed when the code changed (July 2026)

The developers merged a substantial optimisation of three of the four programs
(wsc-poc PR #112). The verification was re-run from scratch against the new code.
**It still holds, and the honest summary above still holds**, with five changes a
reader should know:

* **Nothing silently carried over.** Every program was re-fetched and re-hashed;
  three of the four are genuinely different code and one — the minting policy — is
  byte-for-byte unchanged. All the proofs about the three changed programs were
  redone, not re-labelled.
* **One earlier result turned out to be FALSE of the new code, and that is the
  system behaving as intended.** The optimisation deliberately allows a seizure
  transaction to *add* ordinary Ada to the account it touches. The old statement
  said "nothing but the seized asset may change, Ada included", and that is now
  wrong. The new statement allows the addition and proves separately that Ada can
  only ever be **added, never removed**. A second, older result — a hand-written
  model of the seizure program used for one unbounded conclusion — was likewise
  shown to disagree with the real code, and **that unbounded conclusion is
  withdrawn**. It is a real loss and it is reported as one.
  **UPDATE (task R1, 2026-07-28): the two "assumed-equivalent" bridges between
  the hand-written models and the real programs have now been DELETED outright,
  not merely flagged.** Both were shown false by running the real programs — the
  transfer one in two independent ways — so every conclusion that went through
  them has been removed rather than relabelled. Nothing else changed: the same
  175 machine-checked results, the same assumptions under the top-level claims.
  A library that keeps an assumption it knows to be false is worth nothing;
  removing them makes the remaining claims strictly stronger.
* **The keystone result got harder to prove and had to be narrowed.** The rule
  that ties the scheme together — *spending from the mini-ledger forces the
  transfer or seizure program to run* — used to hold for every conceivable
  transaction. The optimisation replaced a search with a direct lookup by index,
  and the automated prover can no longer handle the general case. It now holds
  for transactions whose *withdrawal list has exactly two entries*, which both
  verified transaction families have. That restriction is now visible in the
  statement of the main result and cannot be forgotten. Measured: lists of one
  and two entries work, three does not.
* **The count of assumptions did not move** (28 for each of the two strongest
  results), and neither did the one-quarter-code / three-quarters-narrowness
  ratio.
* **Reproducing the work got harder.** Two of the four programs now cannot even
  be *read* by the verification tool without an unpublished extension to it, and
  a second tool needs an unpublished one-line-idea fix as well. Until three
  branches are published, this work can only be re-run on one machine.

---

## What was attempted

The system is a regulated-stablecoin design in which "programmable tokens" are
supposed to be confined to a controlled area — a mini-ledger — so that transfer rules
and law-enforcement seizure can be enforced. The target sentence was:

> **In an honest deployment, programmable tokens cannot exist outside the
> mini-ledger.**

The work verifies the **actual compiled on-chain programs** — not a re-implementation,
not a paraphrase, not a specification document. The four programs analysed are
byte-for-byte identical to what is deployed, and that identity is checked
cryptographically. This check has been re-run at four separate reviews and passes on
all four programs every time.

## What was established

**The target sentence is not proved.** Three weaker things are:

1. **The problem was reduced, rigorously, to four sub-obligations plus a list of
   clearly named assumptions** — 26 for the weakest form of the result, 28 for each of
   the two strongest. This reduction is checked by machine. It is the durable part of
   the work: anyone who later discharges the four sub-obligations gets the full
   result. The count is a **floor, not a ceiling**: it is what today's proof consumes,
   and a stronger result will consume more.
2. **Six specific safety properties of the four production programs were proved** —
   about transfers, seizure, minting, directory registration, and the rule that ties
   the whole scheme together. Each was proved by exhaustively checking the real
   compiled code, with controls (described below) designed to catch results that look
   good but say nothing.
3. **All four sub-obligations were discharged for two specific families of
   transactions** — one for transfers, one for seizures. In each family, however,
   **only one of the four obligations is actually carried by the program code; the
   other three are true because the family is narrow enough that they cannot come
   up.** That ratio — one quarter code, three quarters narrowness — is the honest
   summary of how much has been shown, and it did not improve in the final round even
   though the last remaining assumption was eliminated.

## The three most important limitations

**1. The results are about specific transaction *layouts*, and those layouts provably
do not cover real traffic.** Every proof about the compiled code fixes the *shape* of
the transaction — how many inputs, how many outputs, which fields are present — and
then checks all possible values within that shape. The obvious question is whether
those shapes cover the transactions a real wallet would build. In this round that
question was, for the first time, asked precisely and answered: **no.** There are
transactions the real deployed code accepts, that a node would consider valid, that
consume exactly the same amount of computation as the certified example, and that fall
outside every shape examined. Two of them differ from a covered transaction only by
the *length of a list*; one only by *which variant of a date range* it uses. Closing
this gap by brute force is not an option: the smallest realistic transaction size
already contains about nine billion distinct layouts, which at the measured rate would
take roughly a thousand processor-years to check for a single property. **This is the
binding limitation on the whole exercise, and it is now a measured fact rather than an
open worry.**

**2. Nothing here is checked end-to-end by the most trustworthy component.** The
proofs are completed by an automated solver, and the results are recorded as verdicts
in a build log rather than re-verified by the underlying proof checker. There are
about a hundred such results, and every top-level conclusion depends on at least one
of them. A related and separate gap: the statements the solver proves and the
executions the concrete examples run are, strictly speaking, about two different
forms of the same program, and their equality is not proved. Both top-level results
inherit that gap. This is a normal and defensible engineering trade — the solver is what makes
analysing real compiled code affordable at all — but "machine-checked" here means
"checked by the solver, with the verdict on the record", not "checked by the kernel".
A related trap is documented so it cannot recur: the build's own warning counts
understate this, and were once quoted as if they were a complete tally.

**3. The results rest on 28 named assumptions, and the deployment is not yet
independently reproducible.** The assumptions are enumerated rather than buried, and
they cover things the analysis does not model: transaction fees, the ledger's own
bookkeeping, and — importantly — the assumption that a given transaction really is on
the chain. Separately, the build depends on a private, unpublished version of one
supporting library. This round shipped a verified offline copy of it, together with a
step-by-step recipe, and confirmed by reconstruction that the copy is exact. That
reduces the risk substantially but does not remove it: until that library is published,
anyone reproducing this work is trusting the copy that travels with it.

## Why the work should nonetheless be believed on its own terms

The strongest evidence is not any single result — it is that **the project repeatedly
found and published its own critical defects rather than waiting for a reviewer to.**

The clearest example: partway through, the team discovered that *every* transaction
layout it had been using was impossible for a real node to produce, because of a rule
about how transactions must be witnessed. Six already-"proved" properties were, at that
moment, true statements about the empty set. The team found this itself, published it
before anyone else could, measured its cost, repaired eleven of the twelve layouts,
and verified the repair from both directions. A second example: an ordering defect in
the supporting ledger library had silently made an entire class of results
meaningless — every programmable-token mint was being rejected before the interesting
question was even asked. It was caught by comparing against real transactions, was at
first blamed on the wrong component, and the misattribution was then corrected and the
two causes separated by machine rather than by argument. A third: in the final round,
one work unit delivered nothing and another left a completed fix sitting outside the
repository, so a known weakness stayed open despite having been solved — none of the
project's own health metrics could detect this, because all of them measure work that
exists. That blind spot is now written down, and the response was a change of
procedure rather than a new metric: the following round's first action was to check,
finding by finding, that the claimed work was actually in the repository and said what
it was reported to say, **before** measuring anything. It was, in all three cases.
The same round also found that the project's own rule about redeemer witnessing was
stronger than the real ledger rule, which made six of its "this case is impossible"
results weaker than they read; those six were relabelled, in the code, with the extra
condition they actually need.

Alongside this, the analysis forced two corrections to the system's own written
specification: one stated inequality was simply wrong for token burns, and one
well-formedness condition was missing a clause.

## What changed in the final round

Three loose ends left open by the previous round were closed and independently
verified: the last transaction family without a worked concrete example got one; the
one family whose theorem covered an impossible case was replaced with a real one; and
the over-strong witnessing rule described above was bounded and every use of it
audited one by one. The verified build grew by one module and three solver results,
and every one of those was traced to the exact line of source that produced it. No
assumption was added anywhere in the layer that is supposed to add none.

## Bottom line

This is a genuine, unusually careful analysis of real deployed code, and it is candid
about the distance still to travel. It does **not** establish that programmable tokens
cannot escape the mini-ledger. It establishes a precise reduction of that question, six
real properties of the deployed programs, and — most valuably for anyone planning the
next step — a measured demonstration of exactly which gap remains and why the obvious
way of closing it is unaffordable. The recommended next step is therefore *not* to
attempt that closure, but to remove the tooling defects that currently force the
narrow-layout approach in the first place; the one property already proved without any
layout restriction shows that this route works.
