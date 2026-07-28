# N4 — re-prove P1 / P5 / P6 against the PR #112 global validator

Task N4, 2026-07-28. wsc-poc `main` @ `2306678`, CLAB workspace copied from
`wsc-containment-proofs` @ `bbc9f26` (N2's HEAD).

## Headline

The global validator's **shapes are re-cut and every one of them preps again**;
the substrate blocker that stood in the way (D6, of which N1's D8 turned out to
be a duplicate) is **diagnosed and fixed**. Of the three properties:

| | shape | prep | four-point bar | status |
|---|---|---|---|---|
| **P1** | T1R/T2R/T6R/T7R re-cut, **T8R new** | ✔ all | probes (b) green for T1R, T8R | gated on **D7** |
| **P5** | G1R re-cut | ✔ | probe (b) green at G1R | gated on **D7** |
| **P6** | G6R re-cut | ✔ | (b) **fails: D9** | **NOT RESTORED** |

D7 is the seize flat not decoding (`ScaleValue`, unit N5's deliverable); it
reaches P1 and P5 only through `Props/* → Honest → Runs → Prep.Seize`, an import
edge, not through anything either property says.

## What the source actually changed, read at `2306678`

`PTransferAct` gained `pownerWdrlIdxs` third (`ProgrammableLogicBase.hs:1148`,
record decl `:1046-1052`). Inside `pvalueFromCred` (`:328-439`) the owner witness
for a SCRIPT-owned mini-ledger input is now one indexed comparison,

```
ownerCredData #== pforgetData
  (pfstBuiltin # (phead # (pdropList # pfromData (phead # idxs) # withdrawalEntries)))
```
(`:386-393`), replacing the old scan `pisScriptInvokedEntries` (`:282-294`, now
dead and retained only as the benchmark's scan baseline, per its own comment at
`:275-280`). The PUBKEY arm (`:370-376`) does NOT consume an index — it calls
`k resolvedOutValueData idxs` with the cursor unadvanced.

**Consequence for the re-cut, and it is not a free choice.** Every pre-existing
global shape witnesses its mini-ledger owner by SIGNATURE (T1R/T2R/T6R/T7R:
`StakingHash (PubKeyCredential owner)` with `owner` a signatory) or has no
mini-ledger input at all (G1R/G6R: the sole input sits at a pubkey credential, so
`withContributing`'s payment gate at `:351-352` fails). So `ownerWdrlIdxs = []`
is what each shape FORCES, and no shape needs a second withdrawal entry.
Corroborated externally: all four regenerated transfer goldens carry `[]`
(`Goldens/RedeemerGate.lean:286-332`).

The brief asked specifically whether G1R/G6R still get away with one script
withdrawal now that owner indices exist. **They do**, for the reason above: no
mini-ledger input, so the script arm is unreachable and entry 0 remains the only
one dereferenced (`cachedTransferScript0`, `:1205`).

## SHAPE T8R — the gap that answer opens, and closing it

If every shape takes the pubkey arm, then **no theorem in this library touches
the line PR #112 was written to add.** N2 found the identical hole on the goldens
side ("no golden has a non-empty `ownerWdrlIdxs`"). SHAPE T8R
(`Shaped/GlobalShapedR.lean` §7) is SHAPE T1R with the mini-ledger input owned by
a SCRIPT, **no signatories at all**, three script withdrawals `w0<w1<w2`,
`ownerWdrlIdxs = [2]`, and a 4-entry redeemer map covering the spend and all
three withdrawals. `sOwn` and `w2` are independent free variables, so
`sOwn = w2` has to be earned rather than baked in.

Stated over it: P1 in signed form (`P1R_T8`), and
`P1R_T8_owner_witness_enforced` — *acceptance implies the redeemer's index really
named the input's own owner*, which is the compiled-code form of the source's
claim at `:381-385`. Its mandatory vacuity probe is green
(`Probe/D9Probe.lean`); the two `by blaster` stanzas are written and are gated on
D7 with the rest of P1.

## D6 — diagnosed and FIXED (and D8 is the same defect)

`WSC/pr/03-blaster-d6-FIX.md` has the full account. In brief: the optimizer
walked a `Blaster.dite'`'s condition and its two branch lambdas separately, so
`optimizeNot`'s De Morgan and Bool-polarity rules rewrote the else-branch's
BINDER TYPE while the node's own `p` stayed put, and the kernel rejected the
result. Fix: force each branch's binder type from the already-optimized
condition. Two files, `Optimize/Basic.lean` and `Optimize/OptimizeStack.lean`.

Why it mattered here: PR #112 moved the mint merge onto CIP-153 `punionValue`
(`:1245-1268`), whose 128-bit range guard is a `Not`-shaped proposition in a
`dite'` binder. So after #112 **every nonzero-mint shape stopped elaborating** —
G1R, G6R, T2R, T7R — and P5 and P6 are inherently mint-side. D6 had gone from
blocking two shape families to blocking two of this unit's three properties.

The fix removes a rewrite rather than adding reasoning, so its failure mode is
`Undetermined`, not a false `Valid` (argument in the fix note). It is
**unpushed**; everything global here is unreproducible until it is upstreamed.

## D9 — new, open, and it is why P6 is not restored

`WSC/pr/05-blaster-issue-d9-bv-overflow.md`. SMT backend returns
`Overflow encountered when expanding vector` on all four G6R solver stanzas. Two
hypotheses tested, both refuted with committed probes:

* **the CIP-153 mint merge** — refuted: `Probe/D9Probe.lean`'s G1R probe has a
  nonzero mint and passes;
* **the budget / term size** — refuted: `Probe/D9Budget.lean` re-preps G6R at
  2400 (still accept-capable, new K = 2196) and fails at the *same* SMT source
  position as the 3300 run.

P6's executable evidence is unaffected and green: witness valid, bytecode accepts
at 3300, ledger-legal escaping variant rejected under `Member`. It is the
quantified statement that has no verdict. **P6 must not be quoted as proved
against `2306678`.**

## Measurements

* SHAPE G6R witness **K = 2837 → 2196** (−22.6 %), two-sided. Consistent with
  N2's golden K reductions. `K_is_2837` is now false and fails at
  `P6ShapedR:253`.
* `Prep/Global.lean`'s 600-step vacuity characterization is **still `✅ Valid`**
  against the new bytecode — 600 remains vacuous, as expected.
* `Prep/Global1600` after the D6 fix: **1826 s**, succeeds. Seven shaped global
  preps: 1.7-2.8 s each.
* Vacuity probes green at their own terms and shapes: T1R, T8R, G1R.

## Deliberately not done

* **The ScaleValue/PCB fix was not attempted.** It is unit N5's assigned
  deliverable and a multi-file PCB change; duplicating it would collide on
  copy-back.
* **`Probe/T3PrepFAILS` / `T4PrepFAILS` were not re-run** against the fixed
  Blaster. They are named for a failure the fix may have removed; if so, P1's
  dispatch Paths B/C and the input-side aggregation axis reopen. Highest-value
  follow-up.
* **No full-library regression run.** The D6 fix touches a code path every prep
  goes through, including the minting side that was already green. `P4_Minting`
  and the six minting shapes must be re-run before the fix is trusted beyond this
  unit. No new baseline counts are claimed.
* `Model/GlobalModel.lean` got an ARITY-ONLY fix so it compiles; it remains
  semantically stale (it still transcribes the pre-#112 scan) and says so loudly
  at the patch site.
