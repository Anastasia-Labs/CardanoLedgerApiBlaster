# Programmable-token containment: formal verification — executive summary

*One page, plain English, no formal-methods vocabulary and no code names. The full,
precise version is `WSC/README.md`; the audit behind it is `WSC/AUDIT.md`, which is
authoritative wherever the two differ; the per-property status table is
`WSC/STATUS.md`. Every number here was re-measured on 2026-07-25.*

## The property under study

The programmable-token system is designed so that a regulated token can only ever sit
inside a controlled area of the ledger — the "mini-ledger" — where the issuer's rules
(transfer restrictions, freezes, seizures) are enforced. The property everything else
rests on is:

> **In a correctly deployed system, a programmable token cannot exist outside the
> mini-ledger.**

If it can, issuer control is a fiction: a holder moves the token to an ordinary
address and freeze and seize no longer reach it.

## What was verified, and in what sense

We took the **actual compiled on-chain programs** — and we have machine-checked
evidence that they are exactly the programs the production build produces, byte for
byte, at a recorded commit — and checked six safety properties of them.

The method is exhaustive symbolic execution. For a described family of transactions,
a solver checks *every* member of that family at once, not a sample, and reports
whether the property can be broken. All 158 checks in this build return a verdict,
with no failures, no timeouts and no errors.

The results are genuine statements about the real programs, and they carry two bounds
that must always be quoted with them:

* **a work bound** — each program is checked only up to a fixed number of execution
  steps, chosen with headroom over what real transactions cost;
* **a shape bound** — each check covers one described family of transaction layouts,
  not all layouts.

## What changed in this round

The previous round's audit found something serious and self-inflicted: **every
transaction family the proofs quantified over was, in fact, impossible to build.**
For tractability each family carried a single entry in the table that authorises the
programs a transaction runs, while simultaneously requiring two programs to run. A
real node rejects that outright. The proofs were true statements about an empty set.

That is now fixed for **11 of the 12 families**. Each was re-cut to carry exactly the
authorisation entries the ledger rule demands, and all six properties were re-proved
over the corrected families. Three independent checks back this up:

1. the ledger rule was transcribed from the node's own source and then verified
   against all 13 recorded real transactions — the predicted number and kind of
   entries matches exactly, in every case;
2. each corrected family is certified by a concrete example transaction that
   satisfies the rule in both directions (nothing missing, nothing extra) and that
   the real compiled program accepts;
3. the same check applied to the old families **fails**, on every one of them — so
   the repair is confirmed in both directions, not merely asserted.

The repair cost **nothing in execution time**: every measured step count is identical
to before, because the programs never read the authorisation table (with one
exception, which was re-measured).

The second change follows from the first. Because a corrected family is no longer
empty, it became possible for the first time to plug a result about the compiled code
into the end-to-end argument. One of the four obligations the overall claim reduces to
is now discharged **by the compiled transfer program itself**, with its acceptance
genuinely used — something that was not true of any previous step in the argument.

## What to trust it for

* **Trust that the checked programs are the deployed ones.** That link is verified,
  not asserted.
* **Trust the individual property results within their two stated bounds.** Each has
  a negative control, a tightness check, and a mandatory emptiness probe. That probe
  is not ceremony: it previously caught a property reported as proved that was
  actually about no transaction at all, and the same discipline is what surfaced the
  impossible-transaction problem above.
* **Trust the counterexamples and corrections this work produced.** A specification
  error in the containment inequality that made it false for token burns; two
  machine-checked counterexamples to an assumed helper function; an arity bug in the
  benchmark harness; and the impossible-transaction finding itself, which the campaign
  found in its own work and published before anyone else could.
* **Do not trust it as a proof of the headline property.** It is not one.

## The three most important limitations

**1. There is still no argument that the checked families cover the transactions the
claim is about.** This is the binding constraint and the largest single gap. Every
result holds over a described layout; nothing establishes that a real transaction must
have one of those layouts. This matters concretely: one of the six properties is
provable over its family precisely *because* that family gives every transaction a
single token type, and the same statement is **false in general**, with two
machine-checked counterexamples on record. Repairing the impossibility problem did not
touch this.

**2. The end-to-end claim is a reduction, not a proof, and rests on assumptions.** It
is derived from four obligations plus 28 assumptions about ledger behaviour — that
transactions balance, that inputs come from the current state, that the deployment's
published parameters are genuine, and so on. Each is documented against the node's
source, but each is assumed. Of the four obligations: one is now discharged from the
compiled code, two are discharged by the narrowness of the family (it describes pure
transfers, which mint nothing and register nothing), and one is assumed outright. The
strongest honest sentence is: *one of four obligations is now closed by the real code,
over one non-empty family, assuming a second.*

**3. The proofs are certified by a solver, not by the proof assistant's kernel, and
the build is not currently reproducible elsewhere.** Most results rest on a recorded
solver verdict rather than a fully kernel-checked proof; the claim that these are
kernel-verified theorems is false and is corrected in the audit. Separately: the build
depends on an unpublished local branch of a supporting library, with no revision
recorded anywhere, so **the results cannot presently be reproduced on another
machine.** That is the highest operational risk in the work and should be fixed before
anything here is relied upon.

## State of the work

Zero errors, zero unresolved checks; the build reproduces in about a minute and a half. The
audit is a separate document that re-derives every number here and disagrees with
earlier reports where they were wrong. Of the previous round's two critical findings,
one is now repaired and the other is unchanged and is limitation 1 above.

The honest summary: this is a strong, well-controlled body of evidence about the
deployed code, and a reduction of the headline property to a small, explicitly listed
set of gaps — not a proof of that property. The evidence is now about transactions a
node could actually build, which it was not before. Closing the remaining distance
requires a coverage argument, and that work has not been started.
