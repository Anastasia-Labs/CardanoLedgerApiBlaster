# D6 — the `Blaster.dite'` motive defect: ROOT CAUSE AND FIX

Status: **FIXED.** Companion to `WSC/pr/02-blaster-issue-d6-dite-motive.md`,
which reported the defect.

**WHOSE FIX LANDED.** Tasks N4 and N5 hit this defect independently, in different
validators, and diagnosed the same root cause and the same repair. **The fix that
landed is N5's** — `optimizeDITE` rebuilding both branch binder types from the
final condition, in `Lean-blaster-wsc` @ `4d320dd`, now pinned by `lakefile.lean`
as a local path. N4's workspace patch was equivalent and has been discarded
rather than committed, so there is one fix and one pin, not two.

The convergence is worth recording as evidence: two units, two different failing
programs (the global transfer validator's mint merge; the seize validator), same
diagnosis. And N5 ran the control this note originally listed as missing —
**verdict-neutrality on the untouched minting side: 42 Valid + 23 Expected
Falsified both with and without the patch.**

What this file adds that N5's commit message does not is the REACH analysis
below: how far D6 actually extended after PR #112, and why it was the difference
between P5/P6 being provable and being unstatable.

⚠ `Lean-blaster-wsc` is a LOCAL, UNPUSHED path pin. Every global-side result in
this library is unreproducible off this machine until it is published.

## Why it mattered here

PR #112 rewrote the transfer validator's mint merge to use the CIP-153
`unionValue` builtin (`ProgrammableLogicBase.hs:1245-1268`) instead of the
hand-rolled sorted walk it used before. `unionValue` sums quantities, so its
residual carries a 128-bit range guard. That guard is a `Not`-shaped
proposition sitting in a `Blaster.dite'` binder, which is exactly D6's trigger.

Consequence, measured: after PR #112, **every shaped prep with a NONZERO MINT
FIELD stopped elaborating** — `#prep_uplc` succeeded and `addDecl` was then
rejected by the kernel. That is SHAPES G1R (P5's), G6R (P6's), T2R and T7R. P5
and P6 are inherently mint-side properties, so before this fix they were not
merely un-reproved, they were **unstatable**. D6 went from blocking two shape
families to blocking two of the three properties in this unit.

It also explains defect **D8** as reported by unit N1 (`IMPACT-PR112.md` §6.2):
D8 is not a separate defect. The unshaped `Prep/Global1600` prep and the shaped
mint-side preps fail the same way, for the same reason, in the same optimizer
pass. D8 should be closed as a duplicate of D6.

## Root cause

`Blaster.dite'` is
```lean
protected noncomputable def dite' {α : Sort u} (p : Prop) (t : p → α) (e : ¬ p → α) : α
```
The optimizer walks a `dite'` node's three interesting arguments SEPARATELY:
the condition `args[1] = p`, the then-branch `args[2] : p → α`, and the
else-branch `args[3] : ¬ p → α` (`Optimize/Basic.lean`, `optimizeExplicitArgs`).
Each branch is a lambda, and `optimizeLambda` pushed `.InitOptimizeExpr t` for
the binder TYPE — i.e. it optimized `p` and `¬ p` **independently of the `p`
already stored in the node's head**.

`optimizeNot` (`Optimize/Rewriting/OptimizePropNot.lean:57-66`) then rewrote the
else-branch binder with rules that are propositionally valid but NOT
definitional:

* `¬(¬e₁ ∧ ¬e₂) ⟹ e₁ ∨ e₂` (De Morgan, via `notLogicalSimp?`)
* `¬(true = e) ⟹ false = e`, `¬(false = e) ⟹ true = e` (via `notEqSimp?`)

so the emitted term had head `dite' p …` demanding `¬ p → α` while the branch it
was given had type `(e₁ ∨ e₂) → α`. The optimizer returned successfully and the
KERNEL rejected the result — which is why this reads at the call site as a
PlutusCoreBlaster failure (`#prep_uplc` calls `Optimize.main` and then
`addDecl`) when it is not one.

Observed error, verbatim, from the SHAPE G6R prep before the fix:
```
(kernel) application type mismatch
argument has type
  q < ((Int.ofNat 2).pow 127).neg ∨ (Int.negSucc 0).add ((Int.ofNat 2).pow 127) < q → State
but function has type
  (¬(¬q < ((Int.ofNat 2).pow 127).neg ∧ ¬(Int.negSucc 0).add ((Int.ofNat 2).pow 127) < q) →
      State) → State
```
`q` is the shape's free minted quantity, and the two bounds are `unionValue`'s
128-bit `Quantity` range guard. The De Morgan rewrite is plainly visible.

## The fix (upstream option 1, "rewrite the motive with the binder")

Make each branch's binder type track the head instead of being optimized on its
own. At the point the optimizer reaches the branches, the condition has ALREADY
been optimized, so the correct binder types are exactly `p` and `¬ p` built from
it, and they are free. Non-`dite'` lambdas keep their binder types optimized as
before, and both De Morgan rules stay available everywhere outside a `dite'`
binder.

See `Lean-blaster-wsc` @ `4d320dd` for the landed form.

## Which way does this fix cut, soundness-wise

Worth being explicit, because "I patched the prover" deserves scrutiny.

The patch REMOVES a rewrite; it adds no new reasoning. The binder type is forced
to be syntactically what `Blaster.dite'`'s own signature demands, so the emitted
term is well-typed by construction and the Lean KERNEL still typechecks it
exactly as before — `#prep_uplc` still ends in `addDecl`, and that check is
untouched. What the else-branch's hypothesis context now registers is the
un-normalised `¬ p` rather than its De Morgan form, which can only give the SMT
backend LESS to work with.

So the failure mode this fix can introduce is `Undetermined` — a goal the solver
no longer closes. Under the house rule that `Undetermined` leaves the goal open
and hard-fails the build, that is a visible failure, not a silent one. It cannot
turn a false goal into `✅ Valid`.

That argument is a reason to trust the DIRECTION of the change, not a substitute
for the regression run in "What is NOT yet re-verified" below.

## Measured effect (N4's global-side numbers)

Preps that FAILED before the fix and BUILD after it (same workspace, same flats,
wsc-poc main @ 2306678):

| module | shape | before | after |
|---|---|---|---|
| `WSC/Shaped/GlobalMemberShaped.lean` | G6 | kernel type mismatch, 7.5 s | ✔ 1.8 s |
| `WSC/Shaped/GlobalMemberShapedRPrep.lean` | G6R (P6) | blocked by the above | ✔ 2.2 s |
| `WSC/Shaped/GlobalShapedRPrep.lean` | G1R (P5) | blocked by the above | ✔ 1.8 s |
| `WSC/Shaped/GlobalShapedP1RMintPrep.lean` | T2R (P1 mint) | blocked | ✔ 2.5 s |
| `WSC/Shaped/GlobalShapedP1ROutMintPrep.lean` | T7R (P1 agg+mint) | blocked | ✔ 2.8 s |
| `WSC/Shaped/GlobalShapedP1RPrep.lean` | T1R | blocked (module coupling) | ✔ 2.1 s |
| `WSC/Shaped/GlobalShapedP1ROutPrep.lean` | T6R | blocked (module coupling) | ✔ 2.4 s |
| `WSC/Shaped/GlobalShapedP1SOwnPrep.lean` | T8R (NEW) | — | ✔ 1.7 s |

## What is NOT yet re-verified about the fix

Stated so nobody over-reads the table above. Item 2 has since been discharged by
N5 (see the status note at the top); items 1 and 3 stand.

1. **The two historically-failing probes have not been re-run.**
   `WSC/Shaped/Probe/T3PrepFAILS.lean` (`valueContains` residual) and
   `WSC/Shaped/Probe/T4PrepFAILS.lean` (two contributing inputs, the
   `unionValue` guard) are *named for their failure*. If the fix is complete they
   should now PREP, which would retire the "SHAPES T3/T4 are unreachable"
   limitation in `COVERAGE.md` and open P1's containment dispatch Paths B/C and
   the input-side aggregation axis. **This was not attempted in this unit and
   must not be claimed.** It is the single highest-value follow-up.
2. ~~**No regression run of the full library.**~~ **DISCHARGED by N5's
   verdict-neutrality control**: the eight P4/minting shaped modules give
   42 Valid + 23 Expected Falsified both with and without the patch.
3. **No upstream test-suite run.** `Lean-blaster`'s own tests were not executed.
