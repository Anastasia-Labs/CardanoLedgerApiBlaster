# SUBMISSION 3 — Blaster defect report D6 (an ISSUE, not a PR)

**Repo** `input-output-hk/Lean-blaster` · **against rev**
`59db213ca6396269d2606b7dd9ac2bc26ae7c4ce` (branch `beta-lambda-cache-optimization`)
· **severity** HIGH for any consumer that optimizes a term containing `dite`

This is not a pull request. It is a defect report we owe upstream, and it is against
**Blaster**, not PlutusCoreBlaster — even though both reproductions we hold are
triggered through PCB's `#prep_uplc`. Part 1 is the issue text. Part 2 is what is
missing before filing.

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

# PART 2 — WHAT IS MISSING BEFORE FILING (do not submit this part)

### 2.1 We do not have a Blaster-only reproduction, and a maintainer will want one

Both reproductions run through PCB and require a 6,880-hex-char production script plus
the CIP-153 `Value` denotations. That is a poor bug report: the maintainer cannot run it.

**What the root-cause analysis says should suffice**, and what should be attempted before
filing (30–60 minutes, Blaster only, no PCB, no UPLC):

```lean
-- sketch, UNTESTED — this is a work item, not a verified reproduction
import Blaster
example (b : Bool) (n : Nat) : Nat :=
  if h : b = true then n else 0        -- rule 1 candidate: ¬(true = b) in the else binder
example (x : Int) : Int :=
  if h : ¬ (x < -3) ∧ ¬ (5 < x) then x else 0   -- rule 2 candidate: De Morgan
```
run through whatever entry point exercises `Optimize.main` and `addDecl` on the result
(the `#blaster` tactic path calls `goal.admit` on `Valid` and so may never add the
optimized term as a *definition*; the failing path is specifically
**optimize-then-`addDecl`**, which is what `#prep_uplc` does). If a two-line
reproduction can be produced, **lead the issue with it** and demote both current
reproductions to "how we found it".

**If it cannot be reproduced in Blaster alone, say so in the issue** and offer the PCB
route with the fixture. Do not imply we have a minimal reproduction when we do not.

### 2.2 Verify the two rewrites are really the ones firing

The attribution above is a *reading* of `OptimizePropNot.lean` matched against the two
error messages, and the match is exact (rule 1's `¬ (true = e) ⇝ false = e` is literally
the T3 error; rule 2's `¬ (¬e₁ ∧ ¬e₂) ⇝ e₁ ∨ e₂` is literally the T4 error). But it was
**not** confirmed by instrumenting Blaster or by a `verbose:` trace. Before filing,
either (a) re-run one reproduction with Blaster's `verbose:` option and confirm the rule
in the trace, or (b) soften "the rewrite is in `notEqSimp?`/`notLogicalSimp?`" to "the
error is exactly the shape these two rules produce". **(b) is acceptable; overstating is
not.**

### 2.3 The reproductions are in an unpublished repository

`T3PrepFAILS.lean` and `T4PrepFAILS.lean` are in the downstream proof library, which is
not public (see `04-wsc-proof-library-placement.md`). The issue text above therefore
**inlines the failing terms and the diagnosis** and cites only Blaster's own files, so it
stands alone. Keep it that way. Do not link paths the maintainer cannot open.

### 2.4 What NOT to put in the issue

* Any `/home/gumbo/…` path, any `/tmp/claude-…` path, any internal task codename
  (`V1`, `C1`, `T3`, `T4` as *shape* names are fine as shorthand if defined in place;
  as task names they are noise).
* The campaign's own findings register (`D6`, `F12`) — those are our numbers, not theirs.
  Give the defect a plain title and let them number it.
* Any suggestion that PCB is at fault. `PreProcess.lean` does the only correct thing
  available to it.
