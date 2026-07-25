# Programmable-token containment: formal verification — executive summary

*One page, plain English, no formal-methods vocabulary and no code names. The full,
precise version is `WSC/README.md`; the audit behind it is `WSC/AUDIT.md`; the
per-property status table is `WSC/STATUS.md`.*

## The property under study

The programmable-token system is designed so that a regulated token can only ever sit
inside a controlled area of the ledger — the "mini-ledger" — where the issuer's rules
(transfer restrictions, freezes, seizures) are enforced. The property we set out to
verify is the one everything else rests on:

> **In a correctly deployed system, a programmable token cannot exist outside the
> mini-ledger.**

## What was verified, and in what sense

We took the **actual compiled on-chain programs** — and we now have machine-checked
evidence that they are exactly the programs the production build produces, byte for
byte, from the recorded source commit. We reasoned about them mechanically inside a
proof assistant, using an execution engine that reproduces the Cardano ledger's own
cost accounting for these programs **exactly, to the unit**, on nine real transactions.

Six safety properties of the four programs were verified this way, covering every route
a token could take: the transfer path conserves tokens inside the mini-ledger; a
seizure moves only the seized asset and it stays inside; a mini-ledger holding cannot
be spent without the transfer or seize program running; every mint either drives tokens
into the mini-ledger or is a genuine burn; an exemption from the rules cannot be claimed
for a token that is actually registered; and claiming "registered" can only *increase*
what must remain inside. Each result is checked against the real compiled program with
no hand-written model in between, and each carries machine-checked evidence that it is
not empty or circular — including a control that exhibits a legal-but-cheating
transaction and shows the real program rejecting it.

We then wrote the argument that lifts those six properties to the top-level property
over the whole history of the ledger. **That argument is complete and machine-checked,
and it now runs end to end without any unproved input — but only for a restricted
family of transactions: those that visibly send no regulated token outside the
mini-ledger and register no new token type.** For that family the top-level property is
established outright. The family deliberately excludes every transaction for which
containment depends on the *programs* rather than on the shape of the transaction, so
what this demonstrates is that the lifting argument is sound and complete, not that the
code is safe. For the general case the top-level property remains a verified
**reduction**: it follows from four precisely named remaining obligations plus 26
explicitly stated assumptions, each labelled with what would discharge it.

## What to trust it for

* **The four programs do what their specifications say, on the transaction patterns
  tested, against the real deployed code.** These are not model-based results; they are
  results about the compiled programs, and the identity of those programs is now
  independently verified rather than asserted.
* **The assumption list is complete and explicit.** Every remaining assumption is
  named, glossed, and traceable to either "trust the Cardano ledger", "trust the
  one-time deployment audit", or one specific unfinished piece of work. Nothing is
  hidden. Automated censuses reproduce the list in one command.
* **The specification itself was corrected by the exercise.** Two written requirements
  turned out to be wrong and the code turned out to be right: the transfer-conservation
  rule had been specified in a form that a legitimate *burn* refutes, and the
  registry-integrity assumption was missing a clause without which the exemption check
  does not actually rule out registered tokens. Both are now fixed and machine-checked.
* **The work found real defects elsewhere.** Most consequential: four benchmark cases
  were passing the wrong number of arguments to two programs, so they reported success
  **without running a single check** and their published cost was the cost of doing
  nothing — one of them under-reporting CPU by a factor of 54. Separately, the benchmark
  harness had been building transactions no real ledger would accept, which had been
  *under-counting* the cost of seizures by up to 17% (the largest seizure scenario is now
  at 83.5% of the on-chain memory budget, not 76.6%). A verification-library bug that had
  made the precondition for every minting-related proof **impossible to satisfy** — and
  therefore every such proof empty — was also found and fixed.

## The three most important limitations

1. **For the transactions the property is actually about, it is reduced, not proved.**
   The family for which the argument closes end to end is, by construction, the family
   in which nothing leaves the mini-ledger anyway. Outside it, four named obligations
   remain unfinished, so nobody should say "containment has been proved". The
   deliverable is the reduction plus the six results about the code — a strong position,
   but a different one.
2. **Every result about the compiled code is bounded twice — by a step limit and by a
   fixed transaction *shape*** (a pinned number of inputs, outputs, reference inputs and
   so on, with all the actual values left arbitrary) — and we have now *proved* that
   those shapes describe transactions **no Cardano node would accept**. Each shape
   carries one entry in a certain authorisation table while requiring several, and the
   ledger rejects that. So there is no argument that the shapes cover all transactions,
   we know of one result that is true for its shape and *false* in general, and — the
   sharpest version — no result about the code yet constrains its behaviour on a single
   transaction that could actually be submitted. The honest label for this layer is
   exhaustive checking of the real code over named bounded families of *inputs* — much
   stronger than testing, and not yet a statement about real transactions. Fixing it is
   well understood and sized: the shapes must be re-cut with realistic authorisation
   tables, using one of the real production test vectors as the template.
3. **It is not independently reproducible today.** Verifying the transfer program
   requires new machinery in a supporting library that exists only as an unpublished
   branch on one developer's machine — and the build configuration does not even record
   which version of it is being used. Until that is published and pinned, no third party
   can re-run these results. This is cheap to fix and should be fixed first.

Two further caveats worth one line each: the guarantee is about tokens staying *inside*
the mini-ledger in aggregate, not about which holder owns what inside it (that is
enforced by per-token rules outside this work); and the strongest single assumption is
the well-formedness of the on-chain registry, which is still assumed rather than proved —
the escape route it would open is the one place where finishing the remaining work
matters most for assurance.

## State of the work

The library builds clean from scratch in **98 seconds**: **101 automated proof verdicts,
all green, zero failures, zero unexplained gaps**, every verdict reconciled one-for-one
against the source so that nothing can have been silently skipped, and every number in
this summary re-measured by an independent final audit that also verified the compiled
programs' provenance end to end and corrected three published figures it found wrong (a
cost estimate off by a factor of 47, a count of suppressed warnings, and the recorded
cost of two test vectors). The ranked list of what would move the needle next is in
`WSC/STATUS.md`; the first four items are (1) re-cut the transaction shapes so they
describe transactions a node would accept, (2) finish the four remaining obligations on
top of that, (3) publish and pin the supporting-library branch, (4) verify the on-chain
registry.
