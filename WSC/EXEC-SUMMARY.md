# Programmable-token containment: formal verification — executive summary

*One page, no formal-methods vocabulary. The full, precise version is
`WSC/README.md`; the independent audit behind it is `WSC/AUDIT.md`.*

## The property under study

The programmable-token system is designed so that a regulated token can only ever
sit inside a controlled area of the ledger — the "mini-ledger" — where the
issuer's rules (transfer restrictions, freezes, seizures) are enforced. The
property we set out to verify is the one everything else rests on:

> **In a correctly deployed system, a programmable token cannot exist outside the
> mini-ledger.**

## What was verified, and in what sense

We took the **actual compiled on-chain programs** — the same bytes that are
deployed, hash-checked against the production build artefacts — and reasoned about
them mechanically, inside a proof assistant, using an independently
cross-validated execution engine (it reproduces the Cardano ledger's own cost
accounting for these programs **exactly, to the unit**, on nine real
transactions).

Six safety properties of the four validators were verified this way, covering
every route a token could take: the transfer path conserves tokens inside the
mini-ledger; a seizure moves only the seized asset and it stays inside; a
mini-ledger UTxO cannot be spent without the transfer or seize program running;
every mint either drives tokens into the mini-ledger or is a genuine burn; an
exemption from the rules cannot be claimed for a token that is actually
registered; and claiming "registered" can only *increase* what must remain inside.
Each result is checked against the real bytecode with no hand-written model in
between, and each carries machine-checked evidence that it is not empty or
circular — including a control that exhibits a legal-but-cheating transaction and
shows the real program rejecting it.

We then wrote the argument that lifts those six properties to the top-level
property over the whole history of the ledger. That argument is complete and
machine-checked **as a chain of reasoning**, but it consumes the six properties in
a slightly stronger form than the form in which they are currently proved (see
limitations). So what exists today is a verified **reduction**: the top-level
property follows from four precisely named remaining obligations plus 26 explicitly
stated assumptions, each assumption labelled with what would discharge it.

## What to trust it for

* **The four validators do what their specifications say, on the transaction
  patterns tested, against the real deployed code.** These are not model-based
  results; they are results about the bytecode.
* **The assumption list is complete and explicit.** Every remaining assumption is
  named, glossed, and traceable to either "trust the Cardano ledger", "trust the
  one-time deployment audit", or one specific unfinished piece of work. Nothing is
  hidden. Automated censuses reproduce the list in one command.
* **The specification itself was corrected by the exercise.** Two written
  requirements turned out to be wrong, and the code turned out to be right: the
  transfer-conservation rule had been specified in a form that a legitimate
  *burn* refutes, and the directory-integrity assumption was missing a clause
  without which the exemption check does not actually rule out registered tokens.
  Both are now fixed and machine-checked.
* **The work found real defects elsewhere.** Most consequential: four benchmark
  cases were passing the wrong number of arguments to two validators, so they
  reported success **without running a single check** and their published cost was
  the cost of doing nothing — one of them under-reporting CPU by a factor of 54
  (**+5,336%** once fixed). Separately, the benchmark harness had been building
  transactions no real ledger would accept, which had been *under-counting* the
  cost of seizures by up to 17% (the largest seizure scenario is now at 83.5% of
  the on-chain memory budget, not 76.6%). A verification-library bug that had made
  the precondition for every minting-related proof **impossible to satisfy** — and
  therefore every such proof empty — was also found and fixed.

## The three most important limitations

1. **The top-level property is reduced, not proved.** Four named obligations
   remain unfinished, so nobody should say "containment has been proved". The
   deliverable is the reduction plus the six leaf results — which is a strong
   position, but a different one.
   **UPDATE (task A2, 2026-07-25).** The four obligations are now discharged for one
   restricted family of transactions — those that visibly send no programmable token
   outside the mini-ledger and register no new policy — so for that family the
   top-level property is proved outright rather than reduced
   (`WSC.Composition.containment_on_contained_class`). That family deliberately
   excludes every transaction for which containment depends on the VALIDATORS, so it
   demonstrates that the lifting argument closes, not that the code is safe. A2 also
   established a harder limitation: the bounded transaction *shapes* of limitation 2
   describe transactions **no node would accept** (each bakes one redeemer-map entry
   while requiring several script witnesses), so the six bytecode results cannot be
   lifted by restricting the top-level statement to those shapes — the shapes have to
   be re-cut first. Machine-checked in
   `WSC/Props/Shaped/ShapeRealizability.lean`; see `WSC/STATUS.md` §0.0a.
2. **Every result about the bytecode is bounded twice: by a step limit and by a
   fixed transaction *shape*** (a pinned number of inputs, outputs, reference
   inputs and so on, with all the actual values left arbitrary). We have no
   argument that the shapes tested cover all transactions, and we know of one
   result that is true for its shape and *false* in general. The honest label for
   this layer is exhaustive checking of the real code over named bounded families
   of transactions — much stronger than testing, weaker than a universal proof.
3. **It is not independently reproducible today.** Verifying the transfer
   validator requires new machinery in a supporting library that currently exists
   only as an unpublished branch on one developer's machine. Until that is
   published, no third party can re-run these results. This is cheap to fix and
   should be fixed first.

Two further caveats worth one line each: the guarantee is about tokens staying
*inside* the mini-ledger in aggregate, not about which holder owns what inside it
(that is enforced by per-token rules outside this work); and the strongest single
assumption is the well-formedness of the on-chain registry directory, which is
still assumed rather than proved — the escape route it would open is the one place
where finishing the remaining work matters most for assurance.

## State of the work

The library builds clean: 98 automated proof verdicts, all green, zero failures,
zero unexplained gaps, reproduced from scratch in 94 seconds by an independent
audit that re-measured every number quoted here and found exactly one earlier
figure wrong (a cost estimate, since corrected). The ranked list of what would move
the needle next is in `WSC/STATUS.md`; the first four items are (1) connect the
proved shape bridge to the assumption set, (2) finish the four leaf obligations,
(3) publish the supporting-library branch, (4) verify the registry directory.
