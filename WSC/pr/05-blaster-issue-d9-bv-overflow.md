# D9 — SMT backend: "Overflow encountered when expanding vector" on SHAPE G6R

Status: **OPEN, NOT DIAGNOSED.** Filed by task N4, 2026-07-28. Two hypotheses
tested and BOTH REFUTED — this file records the bisections so the next person
does not repeat them.

**This is the defect that currently costs the library P6.** All four solver
stanzas of `WSC/Props/Shaped/P6ShapedR.lean` — the two theorems AND both
mandatory probes — return this error instead of a verdict, so P6 has no verdict
at all against wsc-poc main @ `2306678`.

## Symptom

```
error: WSC/Props/Shaped/P6ShapedR.lean:102:55: Unexpected smt error:
  (error "line 209 column 521: Overflow encountered when expanding vector")
error: WSC/Props/Shaped/P6ShapedR.lean:151:89: … "line 209 column 2146: …"
error: WSC/Props/Shaped/P6ShapedR.lean:175:0:  … "line 209 column 520: …"
error: WSC/Props/Shaped/P6ShapedR.lean:199:0:  … "line 119 column 3827: …"
```
The message is Z3's, surfaced through Blaster's `Unexpected smt error` path. The
goal translates; the backend then fails on it. No counterexample, no verdict.

## What it is NOT

### Not defect D6, and not caused by D6's fix
D6 (`WSC/pr/02…`, fixed in `WSC/pr/03…`) was a KERNEL error from `addDecl` on the
optimizer's output — those goals never reached the solver. D9 is raised by the
SMT backend on a goal that now translates cleanly. D6's fix is what lets these
goals get far enough to hit D9; it did not create it.

Corroboration that the fix is not the cause: with the same patched Blaster, the
three probes in `WSC/Shaped/Probe/D9Probe.lean` return `✅ Expected Falsified`
normally, and `WSC/Prep/Global1600.lean` — the biggest symbolic prep in the
library — now elaborates to completion (1826 s) where before it died.

### Not the CIP-153 mint merge — HYPOTHESIS 1, REFUTED
The obvious suspect was PR #112's rewrite of the mint merge onto `punionValue`
(`ProgrammableLogicBase.hs:1245-1268`) and its 128-bit `Quantity` range guard,
since `±2^127` is visible in D6's own error text. Predicted split: empty-mint
shapes fine, nonzero-mint shapes broken.

`WSC/Shaped/Probe/D9Probe.lean` tests exactly that. Result — **all three pass**:

| probe | shape | mint | result |
|---|---|---|---|
| `D9_T1R_vacuity` | T1R | empty | `✅ Expected Falsified` |
| `D9_T8R_vacuity` | T8R | empty | `✅ Expected Falsified` |
| `D9_G1R_vacuity` | G1R | **nonzero** | `✅ Expected Falsified` |

SHAPE G1R has a nonzero mint, goes through `punionValue`, and is fine. Hypothesis
refuted.

### Not the budget / term size — HYPOTHESIS 2, REFUTED
The remaining difference between the passing G1R probe and the failing G6R ones
was the prep budget: 1600 vs 3300. `WSC/Shaped/Probe/D9Budget.lean` re-preps the
SAME SHAPE G6R at budget **2400** and runs the SAME vacuity probe.

Result: **identical failure**, and — the telling part — at the *identical* SMT
source position, `line 119 column 3827`, as the 3300 run. Budget 2400 was chosen
as still accept-capable: the G6R witness's step count was re-measured against the
#112 bytecode at **K = 2196** (down from 2837; a 22.6 % drop consistent with the
6.5-14.7 % reductions unit N2 measured on the global goldens). Hypothesis
refuted.

## What is left — for whoever picks this up

The failing goals and the passing ones differ in the SHAPE, with mint and budget
both eliminated. SHAPE G6R (`WSC/Shaped/GlobalShapedR.lean` §2) against SHAPE G1R
(§1):

| | G1R (passes) | G6R (fails) |
|---|---|---|
| outputs | **1**, at `PubKeyCredential dest` | **2**, both at `ScriptCredential`, hashes `ob0`/`ob1` FREE and distinct from `plc` |
| reference inputs | 2 (params + directory node) | 1 (params only) |
| mint proof | `NonMember 1` | `Member` |

The two free script-credential hashes compared against a third free hash `plc`
are the most conspicuous difference, and "expanding vector" is a
`ByteString`-shaped complaint rather than an arithmetic one — so the next
bisection to run is a SHAPE G1R variant with a second free-hash script output,
holding everything else fixed. **That was not run here.**

Note the two free output hashes are NOT incidental: they are what makes P6
non-tautological ("WHY TWO OUTPUTS", `WSC/Shaped/GlobalMemberShaped.lean`'s
header). Collapsing them to dodge D9 would make the ledger's own `isBalanced`
imply P6's postcondition, so that is not an acceptable workaround.

## What still works at SHAPE G6R, so the scope of the loss is clear

Everything executable. On the same bytecode and the same shape, by
`native_decide`, no SMT involved:

* the witness is `validRewardingContext` and satisfies P6's postcondition
  (4 + 3 = 7 at base against a +7 mint, zero base inputs);
* the real compiled bytecode ACCEPTS it at budget 3300;
* a ledger-legal ESCAPING variant (3 of 7 minted tokens to a non-base
  credential) is REJECTED under the `Member` claim.

So P6's executable evidence survives PR #112 intact. What is missing is the
UNIVERSALLY QUANTIFIED statement over the shape class — the theorem and its
probes. P6 must not be quoted as proved against `2306678` until D9 is fixed.
