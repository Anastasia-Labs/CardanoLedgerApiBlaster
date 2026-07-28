# SUBMISSION 3 — Blaster defect D6: **A PULL REQUEST** (was: an issue)

**Repo** `input-output-hk/Lean-blaster` · **against rev**
`59db213ca6396269d2606b7dd9ac2bc26ae7c4ce` (branch `beta-lambda-cache-optimization`)
· **severity** HIGH for any consumer that optimizes a term containing `dite`
· **status** ⛔ **FIXED — this document is now a PR, not an issue** (task N6, 2026-07-28)

## ⚠️ WHAT CHANGED ABOUT THIS DOCUMENT

It was drafted as a defect report we owed upstream, with a Part 2 listing what was
missing before we could file. **We then fixed it ourselves.** The fix is one function
in `Blaster/Optimize/Rewriting/OptimizeITE.lean`, commit **`4d320dd`** on
`Lean-blaster-wsc` (= public `59db213` + that single commit), authored during task N5.

So the submission to make is a **pull request** carrying the fix, and this file is its
description. Part 1 below is unchanged and is the defect analysis — it becomes the PR's
"problem statement". Part 2 has been rewritten: the blockers it listed are resolved
except one, which is stated honestly rather than quietly dropped.

Root cause, reach and the post-mortem of a retracted duplicate report live in the
companion `WSC/pr/03-blaster-d6-FIX.md`.

## THE PATCH

```
 Blaster/Optimize/Rewriting/OptimizeITE.lean | 38 ++++++++++++++++++++++++++++-
 1 file changed, 37 insertions(+), 1 deletion(-)
```

`Blaster.dite' c (fun _ : c => _) (fun _ : ¬c => _)` is well typed only when the branch
binders are **syntactically** `c` and `¬c`. But the condition and the branch lambdas are
optimized INDEPENDENTLY — `OptimizeStack.DiteChoiceWaitForCond` optimizes argument 1,
and the binder types are optimized separately via `.LambdaWaitForType`. Whenever
`optimize (¬c)` is not syntactically `¬ (optimize c)`, the rebuilt `dite'` is
kernel-ill-typed.

`optimizeDITE` now rebuilds **both** binder types from the FINAL condition (`c` and
`Not c`) before reassembling the application. This is sound because `dite'` ignores the
`Decidable` instance and its branches take a computationally irrelevant PROOF argument:
when a branch lambda does not use its binder (`!body.hasLooseBVars` — true of every
branch the optimizer builds by normalisation) the binder's type is unconstrained by the
body. When the body DOES use its binder, nothing is changed. **The change can only
repair a term the kernel would have rejected; it never alters a term that already
typechecked, and it never touches a branch body.**

## EVIDENCE THE PR SHOULD CARRY

| claim | measurement |
|---|---|
| fixes reproduction 1 (`¬(true = e)`) | `WSC/Shaped/Probe/T3PrepFAILS.lean`: kernel error → **exit 0, 0 errors, 2.4 s** |
| fixes reproduction 2 (De Morgan) | `WSC/Shaped/Probe/T4PrepFAILS.lean`: kernel error → **exit 0, 0 errors, 9.4 s** |
| fixes a third, independent consumer | `WSC/Prep/Global1600`: 8 m 9 s kernel failure → **builds, 8 m 19 s** |
| and a fourth | post-#112 `programmableSeize` shaped prep at budget 3800: kernel error → **elaborates in 28 s** |
| **does not change any verdict** | the eight untouched `WSC/Props/Shaped/P4*` minting modules: **42 ✅ Valid + 23 ✅ Expected Falsified** with the patch and the **identical 42 + 23** without it, zero failures either way |

The last row is the one a maintainer should care about most: the defect's blast radius
is "term fails to typecheck", never "term typechecks and means something else", and the
control confirms the repair inherits that property.

---
---


# PART 1 — ISSUE TEXT (file this)

## Title

`Optimize.main` emits a kernel-ill-typed `Blaster.dite'` — the `Not`-normalisation
rewrites the else-branch binder type without updating the motive

## Summary

`Blaster.Optimize.main` returns a term the Lean **kernel rejects**. The optimizer's
`Not`-normalisation rewrites the *type of the else-branch binder* of a
`Blaster.dite'` node without correspondingly rewriting the `dite'` node's own
proposition argument, so the branch function's domain no longer matches the domain the
`dite'` motive demands.

The rewrite is propositionally justified — the optimizer's substitution is sound — but
the resulting `Expr` is not well-typed, so it cannot be added to the environment.
Consumers hit this as `(kernel) application type mismatch` at `addDecl`, not as a
Blaster error, which makes it hard to attribute.

## The two rewrites that trigger it

Both are in `Blaster/Optimize/Rewriting/OptimizePropNot.lean`:

| # | rule | implemented at |
|---|---|---|
| 1 | `¬ (true = e) ⇝ (false = e)` | `notEqSimp?` (`:23`), applied from `optimizeNot` (`:65`) |
| 2 | `¬ (¬ e₁ ∧ ¬ e₂) ⇝ (e₁ ∨ e₂)` | `notLogicalSimp?` (`:78`), applied from `optimizeAdvancedNot` (`:100-103`) |

`Blaster.dite'` is
```lean
protected noncomputable def dite' {α : Sort u} (p : Prop) (t : p → α) (e : ¬ p → α) : α
```
(`Blaster/Optimize/Decidable.lean:25`), i.e. the else branch has type `¬ p → α`. When
rule 1 or 2 fires **inside** the else-branch binder's type, that binder becomes
`false = e → α` (rule 1) or `(e₁ ∨ e₂) → α` (rule 2), while `p` in the `dite'`
application is left as the un-normalised proposition. `¬ p → α` and the rewritten type
are propositionally equivalent and definitionally distinct, so the kernel rejects.

`dite'` nodes are introduced by the optimizer itself — `dite_equiv`
(`Optimize/Decidable.lean:36`) and `ite_to_dite'_equiv` (`:43`) rewrite `dite`/`ite`
into `dite'` — so any input containing a conditional whose condition is a `Bool`
equation or a conjunction is a candidate.

## Reproduction 1 — rule 1, Bool polarity

Optimizing a UPLC program whose residual condition is a `Bool`-valued containment test
produces:

```
(kernel) application type mismatch
  Blaster.dite' (true = PlutusCore.Value.containedInner …) (fun x => Halt) (fun x => Error)
argument has type
  false = containedInner … → State
but function has type
  (¬true = containedInner … → State) → State
```

The residual itself is **correct** — the intended condition
`containedInner [("",[("",outAda)]),(cs,[(tn0,qOut0),(tn1,qOut1)])] cs [(tn0,qIn0),(tn1,qIn1)]`
appears exactly as expected. Only the typing is wrong.

## Reproduction 2 — rule 2, De Morgan

Optimizing a program whose residual condition is a two-sided 128-bit range guard
produces:

```
(kernel) application type mismatch
  Blaster.dite' (¬ qIn0+qIn1 < -2^127 ∧ ¬ -1+2^127 < qIn0+qIn1) …
argument has type
  (qIn0+qIn1 < -2^127 ∨ -1+2^127 < qIn0+qIn1) → State
but function has type
  (¬(¬ qIn0+qIn1 < -2^127 ∧ ¬ -1+2^127 < qIn0+qIn1) → State) → State
```

Again the residual is the intended term
(`Blaster.dite' (qOut < qIn0.add qIn1) (fun x => Error) (fun x => Halt)` is what the
program means); only the motive is stale.

## How we hit it

Through PlutusCoreBlaster's `#prep_uplc` command
(`PlutusCore/UPLC/PreProcess.lean:28`), which calls `Optimize.main app |>.run default`
at `:40` and then `liftCoreM <| addDecl propDecl` at `:60`. The optimizer **succeeds**;
`addDecl` is where the kernel rejects. So from a consumer's seat this reads as a PCB
failure, which is why it took a while to attribute correctly. PCB is not doing anything
unusual — it adds the optimizer's output as a definition, which is the only thing it can
do with it.

## Expected behaviour

`Optimize.main` should return a term that typechecks. Two shapes of fix:

1. **Rewrite the motive with the binder.** When a `Not`-normalisation rewrites the
   else-branch binder's type of a `dite'` node, rewrite the node's `p` argument to
   match. For rule 1 the `dite'` becomes `dite' (false = e) (fun _ => els) (fun _ => thn)`
   with the branches swapped and the *then* binder type rewritten instead; for rule 2 it
   becomes `dite' (e₁ ∨ e₂) …`, likewise swapped. Both are exactly the `ite'`/`dite'`
   equivalences already proved in `Optimize/Decidable.lean`.
2. **Do not descend into `dite'` binder types at all** for these two rules. Cheaper and
   strictly safe; costs whatever SMT-side benefit the normalisation buys inside a branch
   binder.

Either fix is fine from our side. We have no preference and no view on which is cheaper
for you.

## Impact on us, for prioritisation

This is the single defect that most constrains our work. The consumer is a verification
effort over compiled PlutusV3 validators, and the affected conditions are the CIP-153
`Value` builtins' own residuals — `valueContains`'s containment test and `unionValue`'s
128-bit `Quantity` range guard. `unionValue` sums the lovelace entry of the two values it
merges, so the range guard fires on **every** program that aggregates two or more values,
whatever the policies are. Consequently:

* two whole families of transaction shapes cannot be prepared at all, at any budget;
* the containment property we care about is provable on one of three code paths instead
  of three;
* the workaround is to restrict the analysed transaction shapes until the builtin
  residual does not appear — which is precisely the restriction our own audit identifies
  as the binding constraint on the deliverable.

So: an optimizer soundness-of-*typing* bug in Blaster is the reason a verification
result is narrower than it needs to be. That is the whole of our interest here.

## Environment

Lean 4.24.0 · Z3 4.15.2 · Blaster `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`
(`beta-lambda-cache-optimization`) · PlutusCoreBlaster with the CIP-153 `Value`
builtins.

---
---

# PART 2 — WHAT WAS MISSING, AND WHERE IT STANDS NOW (do not submit this part)

*Rewritten at task N6. The original Part 2 listed three blockers to filing an ISSUE.
Two are resolved by the fact that we now have a FIX; one is genuinely still open and is
the reason this PR is not yet filed.*

### 2.1 A Blaster-only reproduction — ⚠️ STILL MISSING, and it still matters

**Unchanged and not papered over.** Both reproductions still run through PCB and still
need a production script plus the CIP-153 `Value` denotations. A maintainer cannot run
them. The original sketch (a `dite` whose else-binder normalises, driven through
optimize-then-`addDecl` rather than the `#blaster` tactic, which `admit`s and so may
never add the optimized term as a definition) was **never attempted** — not at N5, which
went straight from diagnosis to fix, and not at N6, which chose the clean-room rebuild
over it.

This is now *less* costly than it was, because a PR carrying a fix is easier to evaluate
than a bug report nobody can reproduce: the maintainer can read the 37-line diff and the
soundness argument without running anything. But a regression test in Blaster's own
suite is what would make the fix stick, and **we are not supplying one.** Say so when
filing; do not imply the two PCB modules are usable as upstream tests.

### 2.2 Verify the two rewrites are really the ones firing — ✅ RESOLVED

The original text offered option (b), "soften the attribution to *the error is exactly
the shape these two rules produce*". That softening is **no longer needed**: the fix was
developed against both failing terms and both now elaborate, which confirms the
attribution operationally. The rules are as named in Part 1
(`notEqSimp?`, `notLogicalSimp?` in `OptimizePropNot.lean`).

One correction to Part 1's framing, worth carrying into the PR: the defect is **not**
really "the `Not`-normalisation rewrites the else-branch binder". It is that the
condition and the branches are optimized independently, so ANY normalisation that
treats `c` and `¬c` asymmetrically triggers it. Those two rules are the two we
measured, not an exhaustive list — which is precisely why the fix rebuilds the binders
from the final condition instead of special-casing either rule.

### 2.3 The reproductions are in an unpublished repository — ⚠️ STILL TRUE, now worse

`Lean-blaster-wsc` @ `4d320dd` is a **local, unpushed path pin**, and so is
PlutusCoreBlaster `cip153-value-builtins` @ `3fdd3fb`. Every global- and seize-side
result in the WSC library is therefore **unreproducible off this machine**. Publishing
the Blaster commit is a precondition for filing this PR at all, and publishing both is a
precondition for anyone independently checking the results the PR's evidence table
cites. See `WSC/REPRODUCE.md` and `WSC/substrate/README.md`.
