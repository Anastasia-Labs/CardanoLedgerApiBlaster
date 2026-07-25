# SHAPE BRIDGE — the link from `appliedXShaped.prop` to a ledger-supplied `ScriptContext`

Task **U1**. Deliverable module: `WSC/ShapeBridge.lean`.
Branch `wsc-containment-proofs`; canonical HEAD was `0e2a99d` at task start and
`92f3255` (task U2, "axiom/prep hygiene + wire the shaped leaves into the LeafSet")
when this was written — §8 is stated against `92f3255`.

> ## ⚠️ NUMBERS RECONCILED AT THE G STAGE (H1, 2026-07-25)
>
> **The authority for every campaign-level number is `WSC/AUDIT.md` §1, not this
> file.** This document is task U1's deliverable and its body is left as U1 wrote
> it; only the stale figures are corrected here, in one place, so that the body can
> still be read as the record of its own stage.
>
> | figure | as written by U1 | **current, verified** |
> |---|---|---|
> | `WSC/ShapeBridge.lean` length | 1,616 lines | **1,705 lines** |
> | whole-module cold build | 38 s | **45 s** (G3, box under concurrent load; ≈38 s on a quiet box) |
> | expected `sorry` warnings in this module | 19 | **19 — unchanged** (`AUDIT.md` §2: all 20 build-wide `sorry` warnings less the one pre-existing PCB warning) |
> | shapes bridged | 16 | **16 — unchanged** (6 Tier A + 10 Tier B). Not to be confused with the **13** re-cut shapes of `WSC/Coverage.lean`'s family, which is a different roster for a different purpose |
> | whole-library build | not stated | **432 jobs, 162 verdicts (103 ✅ Valid + 59 ✅ Expected Falsified), 0 errors**, of which this module contributes **19 V + 6 F** |
>
> **Two substantive corrections to the body**, both flagged again at their own
> sections:
>
> 1. **§10 is out of date on coverage.** It says *"No such argument is offered"*.
>    Since task E4 there IS an artifact: `WSC/Coverage.lean` states coverage in Lean
>    and proves it **FALSE** for the re-cut family. See the note at §10.
> 2. **§F22 — `bridge_GIdx` and `bridge_GNIdx` are NOT load-bearing.** Nothing in
>    the library consumes them; their non-vacuity was unwitnessed until the G stage
>    and is now supplied by `G1NonVacuity.propIdx_accepts_1600` /
>    `propNIdx_accepts_1600` through the `rfl` reduction
>    `WSC.globalShapedCtxIdx_at_0_1`. See `AUDIT.md` §8 F22.

This module discharges the obligation `WSC/Composition.lean` §9.4 names
("SHAPE BRIDGE — an obligation created by the shaped-context route", *"expected to
be true and NOT proved anywhere in the library"*) and the one
`WSC.LR_BUDGET_global`'s docstring records as `LR_BUDGET_global_shaped`'s
outstanding debt.
Substrate: PlutusCoreBlaster `cip153-value-builtins` @ `9f9ca8c` (local path pin,
ARCHITECTURE E11), Blaster `beta-lambda-cache-optimization` @ `59db213`,
Lean 4.24.0, Z3 4.15.2.

---

## 1. The problem, stated exactly

Every theorem in `WSC/Props/Shaped/*` has the form

```
∀ leaves, PRE (σ leaves) → isSuccessful (appliedXShaped.prop leaves) → POST leaves
```

`WSC/Composition.lean` and `WSC/Honest.lean`'s `LR_BUDGET_*` axioms trade against

```
isSuccessful (appliedX.prop params ctx)          -- ctx : ScriptContext, ledger-supplied
```

Nothing published before U1 connected the two. The bridge asked for is

```
isSuccessful (appliedXShaped.prop leaves) ↔ isSuccessful (appliedX.prop (shapedCtx leaves))
```

## 2. What the two terms actually are

Read from PlutusCoreBlaster `PlutusCore/UPLC/PreProcess.lean`.

`#prep_uplc name prog f K` (`:34-65`) creates **three** declarations:

| declaration | value | properties |
|---|---|---|
| `name.exec` | `fun x₁ … xₙ => cekExecuteProgram (PlutusScript.script prog) (f x₁ … xₙ) K` — built by `mkUplcApply` (`:142-153`), which η-expands `f`, re-abstracts its telescope, and applies `cekExecuteProgram` | a plain Lean function; `addAndCompile`d ⇒ `native_decide`-executable |
| `name.prop` | `(Optimize.main name.exec).run default` — `Blaster/Optimize/Basic.lean:293`, invoked at `PreProcess.lean:40` | `noncomputable` (`:59`); embeds `Classical.propDecidable`; only `blaster` can attack it |
| `name` | `⟨lang, prop, exec⟩` | `PrepUPLC.<name>` structure, `:47-57` |

Three consequences that determine everything below.

**(a) `Optimize.main` is not a Lean function of the term.** It is
`Expr → TranslateEnvT Expr`, run at elaboration time. "Congruence on
`Optimize.main`" is unavailable; two separately-elaborated preps' `prop`s are two
unrelated constants with no proved relation.

**(b) `prop` is not defeq to `exec`.** MEASURED: `@appliedBase.prop = @appliedBase.exec := rfl`
fails with the kernel error *"Not a definitional equality"*
(`WSC/Shaped/Probe/BridgeProbe2.lean`). The optimizer performs De Morgan /
Bool-polarity / `ite → Blaster.dite'` rewrites which are propositionally justified
(`Blaster/Optimize/Decidable.lean:36` `dite_equiv`, `:43` `ite_to_dite'_equiv` are
PROVED theorems) but not definitional.

**(c) The `exec` level IS a function of the inputs list.** So at that level the
bridge is ordinary congruence.

## 3. The identified "one non-trivial step" — and why it is free in this codebase

The task anticipated the crux as *"the shaped inputs fn's `Data` term equals
`toTerm (shapedCtx args)` as a `Term`"*.

**In WSC that step is definitional, because no shape was ever written as raw `Data`.**
Every `σ` in `WSC/Shaped/*` builds a Lean `ScriptContext` (e.g.
`mintShapedCtx : … → ScriptContext`, `WSC/Shaped/MintingShaped.lean:88`) and the
shaped inputs function is literally

```lean
def mintShapedInputs (ppCS) (mlh) (leaves…) : List Term :=
  toTerm ppCS :: toTerm mlh :: mintingInputs (mintShapedCtx leaves…)   -- :157-168
```

against the unshaped

```lean
def mintingPolicyInputs900 (ppCS) (mlh) (ctx) : List Term :=
  toTerm ppCS :: toTerm mlh :: mintingInputs ctx                       -- Prep/Minting900.lean:69
```

— the **same** `mintingInputs`, hence the same `IsData` encoder. So

```
mintShapedInputs ppCS mlh leaves  ≡δ  mintingPolicyInputs900 ppCS mlh (mintShapedCtx leaves)
```

This is `ShapeBridge.inputs_M1`, proved by `rfl`. `#print axioms inputs_M1` ⟹
**“does not depend on any axioms”**. The same holds for all sixteen shaped preps
(`inputs_B1 … inputs_T7`). Note the base shape additionally shapes the *parameters*
(`baseShapedInputs` wraps `gh`/`sh` as `ScriptCredential`), so the bridge maps both
the parameter vector and the context — the `inputs_B1` statement makes that explicit.

**The crux the task expected to be hard is therefore already discharged by the way
the shapes were authored.** That is a real (and lucky) property of this codebase,
not a general fact about shaped verification: had a shape been written as a `Data`
literal, this step would have required an `IsData`-roundtrip proof.

## 4. LEVEL 2 — the bridge, proved, kernel-checked, no solver

Because `cekExecuteProgram` is a function and the program constant is shared
(`mkProj PlutusScript 1`, `PreProcess.lean:148`, is what `prog.script` elaborates
to), the inputs-level equality lifts:

```lean
def mintingRun (K) (ppCS) (mlh) (ctx) :=
  cekExecuteProgram programmableTokenMinting900.script (mintingPolicyInputs900 ppCS mlh ctx) K

theorem exec_M1 (…leaves…) :
    appliedMintShaped900.exec ppCS mlh leaves… = mintingRun 900 ppCS mlh (mintShapedCtx leaves…)
  := rfl
```

**This is the shape bridge at the only level where both sides are functions, and it
is proved for all sixteen shapes by `rfl`.** `#print axioms exec_M1` /
`exec_T1` ⟹ `[propext, Classical.choice, Quot.sound]` — Lean's standard three,
**no `sorryAx`**, no WSC axiom, no solver.

Two things make this stronger than it looks:

* The right-hand side `XRun K params (σ leaves)` mentions **no optimizer at all**:
  imported production bytecode + the audited `WSC/Prep/*` inputs function +
  `cekExecuteProgram`. It is exactly "the validator running on a ledger-supplied
  `ScriptContext` under a `K`-step meter".
* It needs **no `#prep_uplc`**, hence no prep cost, hence it is available at
  *every* budget — including 2500 / 3300 / 3800 / 4400, where an unshaped prep is
  unaffordable (§6). `exec_T1` at budget 4400 is `rfl`.

## 5. LEVEL 3 — the bridge at the level the theorems live on

The shaped theorems are about `.prop`, so LEVEL 2 alone does not finish the job.
Two forms, and the difference matters.

### 5.1 Tier A — right-hand side is the UNSHAPED prep's `prop` at the same budget

Available exactly where an unshaped `#prep_uplc` exists at the shape's budget:

| shape | budget | unshaped prep | `Honest.lean` constant |
|---|---|---|---|
| `B1` | 600 | `appliedBase` | `K_base = 600` ✔ |
| `M1`, `M2` | 900 | `appliedMinting900` | `K_mint = 900` ✔ |
| `G1`, `GIdx`, `GNIdx` | 1600 | `appliedGlobal1600` | `K_global_nonmember = 1600` ✔ (U2 republished `K_global` to 4400) |

```lean
theorem bridge_M1 (…leaves…) :
    isSuccessful (appliedMintShaped900.prop ppCS mlh leaves…)
      ↔ isSuccessful (appliedMinting900.prop ppCS mlh (mintShapedCtx leaves…)) := by blaster
```

**Verdict: `✅ Valid` for all six, ≈1 s each.** These carry the same trust status as
every other WSC bytecode theorem (solver verdict + `admit`; `sorryAx` appears in
`#print axioms`, which is the campaign-wide idiom — `WSC/Props/Shaped/P4Shaped.lean:203`
etc.). **No new axiom, no residual.**

This is not a triviality. The left side is the optimizer run on a *closed skeleton*;
the right side is the optimizer run on a *symbolic context* and then instantiated at
the skeleton. `bridge_*` says **shaping commutes with the optimizer**. That the
verdict is cheap is because `blaster` re-runs `Optimize.main` on the goal and the
instantiated right-hand side collapses onto the shaped left-hand side — i.e. the
optimizer's own normalisation is what carries the content, and it is doing real work
here (it must push the substitution through the whole residual branch structure).

The Tier-A budgets are **exactly** the ones the composition publishes after U2's
hygiene repairs — `K_base = 600`, `K_mint = 900`, `K_global_nonmember = 1600` — so
`bridge_B1` / `bridge_M1` / `bridge_M2` / `bridge_G1` are directly consumable by
`LR_BUDGET_base`, `LR_BUDGET_minting` (now correctly naming `appliedMinting900.prop`)
and `LR_BUDGET_global` instantiated at `⟨appliedGlobal1600.prop, 1600⟩`. See §8.

### 5.2 Tier B — right-hand side is the raw metered run

`G6`@3300, `L1`/`L2`/`DT1`/`DS1`@2500, `S1`@3800, `T1`/`T2`/`T6`/`T7`@4400 have no
unshaped prep and cannot get one (§6). For them:

```lean
theorem bridge_T1 (…leaves…) :
    isSuccessful (appliedGlobalShapedT1.prop ppCS leaves…)
      ↔ isSuccessful (globalRun 4400 ppCS (p1ShapedCtx leaves…)) := by blaster
```

**Verdict: `✅ Valid` for all ten.**

**HEALTH WARNING — read this before quoting a Tier-B bridge.** `blaster` begins by
running the very same `Optimize.main` on the goal. Presented with
`isSuccessful X.prop ↔ isSuccessful (raw run)` it optimizes the right side into (a
term equal to) `X.prop` and the SMT query it emits is then trivial. MEASURED: the
verdict is `Valid` in ≈1 s at budget 600 (`WSC/Shaped/Probe/BridgeProbe3.lean`) and
again at budget 4400 (`BridgeProbe7.lean`) — a cost only explicable by syntactic
collapse. So the Tier-B verdicts are genuine evidence that `Optimize.main` is
**deterministic and idempotent**, which is what a Tier-B bridge needs *in practice*,
but they are **not independent evidence that it is faithful**.

### 5.3 The residual, precisely

```
PropExecFaithful X  :  X.prop = X.exec
```

stated in `WSC/ShapeBridge.lean` §RESIDUAL as a `Prop`-valued **`def`, not an
`axiom`**, with per-validator instances. Nothing in the module consumes it.

* **It is not new.** The campaign already depended on it and never named it: every
  `P*` theorem is about `.prop`, while every executable witness, every measured `K`
  and every golden replay runs `.exec` (`WSC/Props/P3_Base.lean:202` `exec_accepts`
  vs `:209` `prop_accepts`; `WSC/Goldens/Witnesses.lean:143` vs `:151`). Those pairs
  are only jointly meaningful if `PropExecFaithful` holds. **U1 identifies the
  dependency; it does not introduce it.**
* **Evidence for it.** Every rewrite the optimizer applies has a proved equivalence
  lemma in Blaster (`Optimize/Decidable.lean:36,43`;
  `Optimize/Lemmas/LemmasProp.lean:10,15,20`). What is missing is a reification of
  the *composite*.
* **Evidence against taking it on faith.** Defect **D6**
  (`WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`): `#prep_uplc` emits a
  kernel-**ill-typed** `Blaster.dite'` when a CIP-153 `Value`-builtin result stays
  symbolic, because the motive is not updated after a Bool-polarity rewrite. The
  transformation is demonstrably not unconditionally well-behaved. This is why the
  residual is *not* axiomatized here.
* **What would discharge it**, best first:
  1. Have `#prep_uplc` emit a fourth declaration `X.prop_eq_exec : X.prop = X.exec`,
     assembled from the per-rewrite equivalence lemmas the optimizer already
     applies. This is a certificate-producing optimizer and is a contained change to
     `PreProcess.lean:36-58` plus a proof-term accumulator in the `Optimize` stack.
  2. Verify `Optimize.main` once, against a reified rewrite relation.
  3. Keep the campaign at Tier-A budgets, where the bridge needs nothing of the kind.

**Tier A does not depend on `PropExecFaithful`** — `bridge_B1`/`M1`/`M2`/`G1`/
`GIdx`/`GNIdx` relate two `.prop`s and never mention `.exec`.

## 6. §UNSHAPED-PREP-REACH — why Tier B cannot be lifted by spending compute

| validator | budget | unshaped symbolic prep | source |
|---|---|---|---|
| `programmableLogicBase` | 600 | 1.0 s | measured, this session |
| `programmableTokenMinting` | 600 / 900 | 11.1 s / 27.6 s | K-MEASUREMENTS §5.1 |
| `programmableTokenMinting` | 1200 | 131.6 s | K-MEASUREMENTS §5.1 |
| `programmableTokenMinting` | 1700 | **never completed in 48.6 min** | K-MEASUREMENTS §5.1 |
| `programmableLogicGlobal` | 1600 | **39 s** | measured, this session |
| `programmableLogicGlobal` | 3300 | **did not complete in 10 min** (killed); a second run was still unfinished at **>75 min**, when it was killed | measured, this session, `WSC/Shaped/Probe/UnshapedCost.lean` |
| `programmableSeize` | 2000 | never completed in 77 min | SPIKE-FINDINGS |

Every SHAPED prep, by contrast, is cheap — measured this session:
B1 0.71 s · M1 0.75 s · M2 0.81 s · G1 0.83 s · G6 1.1 s · L1 1.2 s · DT1 1.2 s ·
DS1 1.2 s · S1 3.5 s · T1 1.0 s · T2 1.2 s · T6/T7 2.1 s. Whole `WSC.ShapeBridge`
module including all 16 preps, 32 `rfl`s, 16 `blaster` bridges, 6 `#blaster`
controls, the concrete instances and the `GlobalNonVacuous` discharge: **38 s**.

## 7. Controls and non-vacuity

### 7.1 Negative controls (all `#blaster … (solve-result: 1)`, all `✅ Expected Falsified`)

| control | perturbation | verdict |
|---|---|---|
| `control_B1_pubkey_param` | first base parameter handed to the unshaped prep as `PubKeyCredential` (`Constr 0`) not `ScriptCredential` (`Constr 1`) | Falsified |
| `control_B1_collapsed_wdrl` | shape's second withdrawal credential collapsed onto the first, right side only | Falsified |
| `control_B1_polarity` | `isSuccessful ↔ isUnsuccessful` | Falsified |
| `control_M1_collapsed_wdrl` | both withdrawal credentials collapsed onto `w1`, right side only | Falsified |
| `control_M1_negated_q` | minted quantity negated, right side only (the `BurnOnly` sign test, Issuance.hs:251-254) | Falsified |
| `control_T1_polarity` | polarity at the Tier-B run form, budget 4400 | Falsified |

**Methodological finding, recorded because it bit this task.** A perturbation that
*looks* like a change may be a **symmetry of the statement**. Swapping the shape's
two withdrawal credentials `w0 ↔ w1` on one side only returns **`Valid`** — and
correctly so: both are universally quantified and the base validator's membership
test is symmetric in them. That is a badly-chosen control, not a false positive.
Any future bridge control must perturb **asymmetrically**. (First observed as
`negControlWrongCtx` in `WSC/Shaped/Probe/BridgeProbe4.lean`.)

### 7.2 Concrete instance across all four corners (§CONCRETE)

SHAPE M1's accepting witness (`WSC/Props/Shaped/P4Shaped.lean:281`): burn 3 of
`OWNCS.TOK` out of an input holding 5, output holding 2, 40 lovelace fee of 100,
withdrawals `[(Script "MINTLOGIC", 0), (Script "ZZZ", 0)]`.

| corner | statement | closed by |
|---|---|---|
| `ctx_valid` | `validMintingContext ctx = true` | `native_decide` |
| `corner1_shaped_exec` | shaped applied term accepts | `native_decide` |
| `corner2_ledger_run` | `mintingRun 900 ppCS mlh ctx` accepts — the raw bytecode on the denoted `ScriptContext` | `native_decide` |
| `corner3_shaped_prop` | shaped `.prop` accepts | `blaster` |
| `corner4_unshaped_prop` | **`appliedMinting900.prop ppCS mlh ctx` accepts** — the exact proposition `LR_BUDGET_minting` trades against `NodeAcceptsMinting` | `blaster` |

Corners 1 and 2 are the *same term* by `exec_M1`; both are stated so the bridge is
visible on a closed instance. Corner 4 is what makes `bridge_M1` non-vacuous where
it matters.

Plus a discrimination pair on SHAPE B1: the bytecode **rejects** when neither base
credential is in the withdrawal map and **accepts** when the global credential is
(`b1_rejects_when_neither_cred_present`, `b1_accepts_when_global_present`, both
`native_decide` through `baseRun 600`; `#eval` cross-check in
`WSC/Shaped/Probe/B1Accept.lean`).

Non-vacuity of each shape class itself is *not* re-established here — it is already
carried by the mandatory vacuity probe in each shaped Props module (all `Falsified`,
SHAPING-RESULTS §4-§6). A bridge is an `↔`, so it cannot be vacuous in the
accept-hypothesis sense, but a bridge over an accept-UNSAT class would be
`False ↔ False`; the polarity controls and the concrete corners rule that out for
B1, M1 and T1.

## 8. Interaction with the composition, as of HEAD `92f3255` (task U2)

U2 landed while U1 was in progress and changed exactly the axioms this module feeds.
Restating against the current text:

* **`LR_BUDGET_minting` — REPAIRED by U2** to name `appliedMinting900.prop`, with
  non-vacuity now a theorem (`Composition.mintingNonVacuous`). `bridge_M1` and
  `bridge_M2` are stated against that same prep, so the minting path
  *shaped P4 theorem → `NodeAcceptsMinting` → composition* is now complete except
  for the arm-scope caveat U2 records (K = 1257/1466/1681 > 900 for the three
  non-burn arms).
* **`LR_BUDGET_global` — now PREP-PARAMETRIC** (`globalProp`, `K`, side condition
  `GlobalPreppedAt globalProp K`). Its docstring lists two instantiations and says
  the second one *"additionally owes the **SHAPE BRIDGE** of `WSC/Composition.lean`
  §9.4"*, with the named TODO `LR_BUDGET_global_shaped`. **That is exactly
  `bridge_T1`/`bridge_T2`/`bridge_T6`/`bridge_T7`** (Tier B, budget 4400, run form),
  and `bridge_G1`/`bridge_GIdx`/`bridge_GNIdx` for the 1600 instantiation.
* **`K_global` is now 4400** (U2), with `K_global_nonmember = 1600` retained as the
  P5 sub-bound. Consequence worth naming: **there is no unshaped 4400 prep and there
  cannot affordably be one** (§6), so `LR_BUDGET_global` at `K = 4400` can only ever
  be instantiated at a SHAPED prop — which makes the shape bridge not an optional
  extra but the *only* route, and makes the Tier-B health warning (§5.2) part of the
  global path's trust base until `PropExecFaithful` is discharged or `LR_BUDGET_*`
  is restated against `XRun K` (§9, follow-on).
* **`GlobalNonVacuous` — U2 records it OPEN; U1 DISCHARGES it on the `prop` term;
  TASK A1 DISCHARGES IT AT ALL THREE GLOBAL BUDGETS on the run term.** A1's version
  (`WSC.NonVacuity.globalNonVacuous_at_{1600,3300,4400}`) is `native_decide` on the
  real CEK — no solver, no `sorryAx` — because after the restatement the predicate
  names `Runs.globalRun K`, the term the witnesses were always about. U1's `prop`-term
  version is RETAINED as independent corroboration; neither instrument subsumes the
  other. The rest of this bullet is U1's original text and still holds: U2's grounds are that the SYMBOLIC vacuity probe over
  `appliedGlobal1600.prop` returned no verdict in 87 min and that "`exec` acceptance
  does not transfer to `prop`". Both true, and neither needed: non-vacuity is an ∃,
  so a CLOSED goal suffices, and `blaster` on a closed goal is the idiom that already
  discharges `BaseNonVacuous` (`P3_Base.lean:209`). Applied to `P5ShapedWitness`'s
  SHAPE G1 context (which is `validRewardingContext`-true with zero failing
  conjuncts) it closes in **< 1 s** —
  `ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`, stated in unfolded form so
  this module need not import `WSC/Honest.lean`. Trust status identical to
  `BaseNonVacuous` / `mintingNonVacuous`; strictly stronger than the `exec`-only
  evidence, because it is about the `prop` term.
* **`GlobalPreppedAt`** (U2's new abstract declaration) was unaffected by U1: it is a
  statement about the elaborator, discharged by inspection of a `#prep_uplc` line.
  Note that a `LR_BUDGET_*` restated against `XRun K` (§9) would **not need it at
  all**, since `XRun K` is a definition, not an elaborator output — a second reason
  to prefer that restatement. **TASK A1 DID THAT AND DELETED IT.**
* **Defect D6** blocks the SHAPE T3/T4 preps, so those shapes have no `.prop` and
  hence no bridge row. Unchanged by U1.

## 9. Honest summary — which case of the task's rubric, and the follow-on

### Recommended follow-on (highest value U1 identified) — **DONE BY TASK A1**

> **STATUS (task A1, 2026-07-25): IMPLEMENTED, with three of the four predicted
> benefits delivered in full and one only partly.**
>
> The four `XRun` definitions moved from `WSC/ShapeBridge.lean` §RUN to the new leaf
> module **`WSC/Runs.lean`** (they had to: `Honest.lean` cannot import
> `ShapeBridge`, which imports the shaped preps, which import `Honest` — that cycle
> is why this had not been done). `Honest.lean` and `ShapeBridge.lean` now both
> import `WSC/Runs.lean` and name the same four constants; this module's 25 verdicts
> are unchanged in statement and were re-run green.
>
> * **(a) composition on the kernel-checked bridge — DELIVERED.** `LR_BUDGET_*`'s
>   right-hand side is now exactly what the 16 `exec_<S>` `rfl`s land on.
> * **(b) `PropExecFaithful` out of the trust base — DELIVERED ONLY ON THE
>   BASE/KEYSTONE PATH.** This prediction was too strong. Restating the AXIOM does
>   not remove the residual, because the shaped P-THEOREMS are still stated on
>   `appliedXShaped.prop` and reach the ledger through `bridge_<S>` (Tier B), not
>   through `exec_<S>`. A1 removed it from `Composition.p3_lifted` by restating P3
>   ITSELF on the run term (`WSC/Props/P3_BaseRun.lean`, `✅ Valid`, own vacuity probe
>   `✅ Expected Falsified` at the run term) — which is the technique that WOULD remove
>   it campaign-wide, applied to one theorem group out of fifteen.
> * **(c) `GlobalPreppedAt` unnecessary — DELIVERED.** Deleted; `Honest.lean` 38 → 37
>   axioms.
> * **(d) Tier A/B split dissolved — DELIVERED FOR THE LEDGER BRIDGE ONLY.** Both
>   tiers' right-hand sides are now consumable. The split still marks a real
>   difference in what the verdict EVIDENCES: Tier A's RHS went through
>   `Optimize.main` on a symbolic context, Tier B's never went through it, so only
>   Tier A says anything about shaping-commutes-with-the-optimizer. §5.2's health
>   warning is unchanged.
>
> Unpredicted bonus: with the axioms stated at every budget, three new `K` constants
> became publishable with PROVED non-vacuity — `K_mint_custody = 2500`,
> `K_global_member = 3300`, `K_seize = 3800` (the last reverses a "no `K_seize` can
> exist" entry) — and all five previously-open `*NonVacuous` obligations are now
> theorems (`WSC/Props/Shaped/NonVacuity.lean`). See `WSC/STATUS.md` §0.0.
>
> NOT delivered, and not claimable: the `LeafSet` is still un-instantiated
> (audit F1), shape coverage is untouched (audit F2), and `top_claim`'s 26 project
> axioms plus `sorryAx` are unchanged (re-measured; identical list).

**Restate `LR_BUDGET_base/minting/global/seize` against `ShapeBridge.XRun K` instead
of `appliedX_K.prop`.** `XRun K` is imported production bytecode + the audited
`WSC/Prep/*` inputs function + `cekExecuteProgram`, and nothing else: no optimizer,
no prep, no elaboration cost, available at *every* budget. Doing so would
(a) put the whole composition on the **kernel-checked** LEVEL-2 bridge instead of a
solver verdict, (b) remove `PropExecFaithful` from the trust base, (c) remove the
need for `GlobalPreppedAt`, and (d) dissolve the Tier-A/Tier-B split, since the
`XRun` right-hand side exists at 2500 / 3300 / 3800 / 4400 where no unshaped prep can
be built. It is a rewrite of four axiom statements plus their use sites; no new
proving. Cost of NOT doing it: the global path at `K_global = 4400` has no unshaped
prep at all, so it must go through Tier B and inherits §5.2's warning.

### Rubric

| level | statement | status |
|---|---|---|
| LEVEL 1 (inputs) | `shapedInputs leaves = unshapedInputs (params leaves) (σ leaves)` | **PROVED, `rfl`, zero axioms**, 16/16 shapes |
| LEVEL 2 (exec) | `appliedXShaped.exec leaves = XRun K (params leaves) (σ leaves)` | **PROVED, `rfl`, no `sorryAx`**, 16/16 shapes, any budget |
| LEVEL 3 Tier A (prop↔prop) | `isSuccessful (shaped.prop) ↔ isSuccessful (appliedX_K.prop … (σ leaves))` | **PROVED by `blaster`**, 6/6 shapes at the three published K; controls Falsified; **no residual** |
| LEVEL 3′ Tier B (prop↔run) | `isSuccessful (shaped.prop) ↔ isSuccessful (Runs.XRun K … (σ leaves))` | **PROVED by `blaster`**, 10/10 shapes; residual `PropExecFaithful` precisely stated, **not axiomatized** |
| **(A1) LEDGER BRIDGE** | `NodeAcceptsX ctx ↔ isSuccessful (Runs.XRun K params ctx)` for `nodeStepsX … ≤ K` | **AXIOM** (`WSC.LR_BUDGET_*`), 4/4 restated against `Runs.XRun K`, `K`-parametric, each with a PROVED non-vacuity hypothesis at every published `K`. What it asserts is `runSteps` monotonicity, unchanged; what it no longer requires is `GlobalPreppedAt` or a prep at the budget |
| COVERAGE | "the shapes cover all transactions" | **NOT established, NOT axiomatized** — see §10 |

So: **case (a) of the task's rubric for the six Tier-A shapes** (a proved theorem,
at the strongest available statement, with the unshaped prep on the right-hand
side), and **case (b) for the ten Tier-B shapes** (a proved kernel-level exec bridge
plus a solver-verified prop↔run bridge, with the `prop`-vs-`exec` residual stated
precisely and left unaxiomatized). **Case (c) — an axiom — was not needed anywhere.**

## 10. SHAPE COVERAGE — recorded, not solved

The bridge says

```
shaped theorem about σ's leaves   ⟹   statement about every ScriptContext in range σ
```

and says **nothing** about contexts outside `range σ`. Sixteen shapes, each pinning
every list length, constructor tag and `Option` in the `Data` skeleton, cover a
finite set of transaction *skeletons* — not the set of transactions. SHAPE M1 fixes
"1 input, 1 output, 0 reference inputs, 2 withdrawals, 1 redeemer, redeemer tag 3";
a two-input burn is outside it.

A coverage argument would require **one** of:

1. **An enumeration plus a closure theorem** — a finite list `σ₁ … σₙ` and
   `∀ ctx, validXContext ctx → nodeSteps … ctx ≤ K → ∃ i leaves, ctx = σᵢ leaves`.
   For this to be *true*, shapes would have to be parameterised over list LENGTHS,
   which the `#prep_uplc` mechanism cannot do — baking the skeleton in is precisely
   what fixes the lengths. A budget-based finiteness argument is conceivable (a
   `K`-step run traverses boundedly many list cells, so only boundedly many
   skeletons are distinguishable), but it is a meta-theorem about the CEK machine
   the substrate does not have (SPIKE-FINDINGS: *"budget monotonicity is a
   meta-theorem SMT doesn't have"*), and the bound would be astronomically larger
   than sixteen.
2. **A shape-generalization lemma** — e.g. "if the validator accepts an `n`-input
   context then it accepts the projection onto the relevant input". **FALSE in
   general for these validators**: the global validator's containment check
   aggregates over ALL inputs and outputs (`WSC/Props/Shaped/P1Shaped.lean`). It
   would have to be proved per property with real side conditions.
3. **Dropping to the source model** (`WSC/Model/*`, which quantify over arbitrary
   contexts) with a separately argued compilation-fidelity bridge — one faithfulness
   axiom per model, which is exactly the trade the UPLC route was chosen to avoid.

**No such argument is offered — BY THIS MODULE.** `WSC/ShapeBridge.lean` writes the
obligation down as `M1Covers : Prop` — unproved, **not** an axiom, and noted there as
*false as stated* for M1 alone.

> **SUPERSEDED IN PART (task E4, re-checked at the G stage 2026-07-25).** The
> sentence above was written when coverage was an UNKNOWN. It no longer is.
> `WSC/Coverage.lean` states coverage in Lean (`Covers`) and **proves it FALSE**
> for the **thirteen** re-cut shapes at `SizeBound 2 2 2 2 0` — SHAPE T1R's own
> size — with three node-realizable witnesses the production bytecode accepts in
> exactly 2,603 CEK steps, the shape's own step count; no project axiom, no
> `sorryAx`. Route 1 of the three above is additionally **priced out**: ≈971
> single-core CPU-years for one property at the smallest bound admitting a real
> transfer. Read `WSC/COVERAGE.md` and `WSC/AUDIT.md` §8 F2-coverage instead of
> this paragraph. What survives from it unchanged is the DIAGNOSIS — that shapes
> cannot be parameterised over list lengths and constructor tags — which is
> precisely the mechanism `Coverage.lean`'s three counterexamples exploit. The honest framing remains the one ARCHITECTURE publishes: **bounded
model checking beneath the axiomatic layer**, now bounded in two dimensions (step
budget `K`, shape `σ`), with the second dimension formally connected to the
ledger-supplied `ScriptContext` by this module.

## 11. Files

| path | role |
|---|---|
| `WSC/ShapeBridge.lean` | the deliverable: 16 × (LEVEL 1 + LEVEL 2 + LEVEL 3/3′), 6 controls, 4-corner concrete instance, §BONUS `GlobalNonVacuous` discharge, `PropExecFaithful`, `M1Covers`, `#print axioms` audit |
| `WSC/SHAPE-BRIDGE.md` | this document |
| `WSC/status-fragments/U1.md` | STATUS row awaiting merge |
| `WSC/Shaped/Probe/BridgeProbe.lean` | LEVEL 1 + 2 first probe (base) |
| `WSC/Shaped/Probe/BridgeProbe2FAILS.lean` | **`prop = exec` is NOT defeq** — the kernel error, retained as evidence. **EXPECTED TO FAIL to build**, in the style of `T3PrepFAILS.lean`; the failure is the measurement |
| `WSC/Shaped/Probe/BridgeProbe3.lean` | `prop ↔ exec` via `blaster` at 600 — `Valid` in ≈1 s |
| `WSC/Shaped/Probe/BridgeProbe4.lean` | first full prop↔prop bridge + the symmetric-control finding; expectations now set to the measured verdicts so it builds, with the finding recorded in its docstring |
| `WSC/Shaped/Probe/BridgeProbe5.lean` | corrected controls, all as expected |
| `WSC/Shaped/Probe/BridgeProbe6.lean` | SHAPE M1 bridge + 2 controls |
| `WSC/Shaped/Probe/BridgeProbe7.lean` | run-form bridge at budget 4400 |
| `WSC/Shaped/Probe/B1Accept.lean` | `#eval` search for an accepting SHAPE B1 leaf assignment |
| `WSC/Shaped/Probe/UnshapedCost.lean` | unshaped `programmableLogicGlobal` prep at 3300 — cost probe, not expected to complete |
| `WSC/Shaped/Probe/AxAudit.lean` | standalone `#print axioms` run |

---

## §12 TASK A2 (2026-07-25) — WHY THE BRIDGE HAS NO CONSUMER, PROVED

A1 restated the four `LR_BUDGET_*` axioms onto `Runs.XRun K` so that the 16
kernel-checked `exec_<S>` `rfl`s are the connective between a shaped theorem and the
ledger side (§11 above). What was left was to build the consumer: a
`Composition.LeafSet hp Shape` with `Shape :=` "an instance of SHAPE T1 / L1 / M1 /
S1". Task A2 tried, and found the obstacle is not plumbing:

> **Every shaped class in this library is EMPTY as a class of ledger transactions.**
> A tractable `#prep_uplc` needs the redeemer map inside the frozen `Data` skeleton,
> so every shape bakes a ONE-entry redeemer map (two for DS1) — while every shape
> bakes a TWO-entry withdrawal map whose entries are BOTH script credentials
> (`p1ShapedWdrl`, `localShapedWdrl`, `mintShapedWdrl`, `globalShapedWdrl`,
> `seizeShapedWdrl`). Conway UTXOW (`MissingRedeemers`) requires one redeemer-map
> entry per script witness, and a script-credential withdrawal is one — that is the
> very rule `WSC.LR_WDRL_RUNS_VALIDATOR` encodes.

`WSC/Props/Shaped/ShapeRealizability.lean` proves it. For SHAPE T1 the proof needs no
new assumption at all: T1 spends an input at the base credential (it must, or the
shaped conclusion's `Model.outSum (.ScriptCredential plc)` is not the composition's
`outAtB hp.progLogicCred`), so `WSC.LR_SPEND_RUNS_VALIDATOR` runs the base validator
on the transaction and `WSC.LR_CTX` then demands a `Spending` redeemer entry that
T1's singleton `Rewarding` map does not contain. `#print axioms t1_class_is_empty` =
`[propext, Quot.sound, WSC.Deployed, WSC.LR_CTX, WSC.LR_SPEND_RUNS_VALIDATOR,
WSC.NodeAcceptsBase, WSC.OnChain]` — **no `sorryAx`**. For L1 / DT1 / M1 / G1 / S1 /
DS1 the emptiness is proved under `RedeemerCoverageAllPlutus`, the `MissingRedeemers` rule
stated as a `Prop` and deliberately **not** as an axiom.

Consequences for this document:

* §5's Tier A / Tier B analysis, §11's restatement and every `bridge_<S>` verdict
  stand unchanged — none of them is about realizability.
* §10's three routes to shape coverage are now known to be **necessary but not
  sufficient**: a coverage argument over classes that are empty proves nothing. The
  first step is re-cutting the shapes with ledger-realistic redeemer maps (new prep
  per shape — ≈1 s, budget-independent — then re-verification of every theorem over
  it; the risk is the enlarged residual).
* The line above, *"NOT delivered, and not claimable: the `LeafSet` is still
  un-instantiated (audit F1)"*, is amended: a `LeafSet` IS now constructed
  (`WSC/Composition.lean` §11, `containedLeaves`) but over an ACCOUNTING class that
  uses no UPLC result, and the shaped instantiation is exhibited as vacuous
  (`ShapeRealizability.t1VacuousLeaves` next to `t1_no_honest_step`).
