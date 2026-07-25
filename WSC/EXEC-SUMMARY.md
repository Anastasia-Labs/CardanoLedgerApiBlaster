# Programmable-token containment: formal verification — executive summary

*One page, plain English, no formal-methods vocabulary and no code names. The full,
technical and deliberately self-critical account is in `WSC/AUDIT.md`, which is
authoritative; `WSC/README.md` is the reviewer-facing version; `WSC/STATUS.md` is the
per-property table.*

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
   26 clearly named assumptions.** This reduction is checked by machine. It is the
   durable part of the work: anyone who later discharges the four sub-obligations gets
   the full result.
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
of them. This is a normal and defensible engineering trade — the solver is what makes
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
project's own health metrics could detect this, and that blind spot is now written
down.

Alongside this, the analysis forced two corrections to the system's own written
specification: one stated inequality was simply wrong for token burns, and one
well-formedness condition was missing a clause.

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
