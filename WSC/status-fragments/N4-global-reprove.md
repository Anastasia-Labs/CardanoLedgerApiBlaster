# N4 — re-prove P1 / P5 / P6 against the PR #112 global validator

Task N4, 2026-07-28. wsc-poc `main` @ `2306678`. CLAB workspace copied from
`wsc-containment-proofs` @ `bbc9f26`, merged with canonical `e607ac2` (N3 + N5)
before commit. Substrate: PCB `3fdd3fb`, `Lean-blaster-wsc` `4d320dd`.

## Outcome — all three restored

| property | shapes | solver verdicts | K (was → is) |
|---|---|---|---|
| **P1** | T1R, T2R, T6R, T7R, **T8R (new)** | 6 `✅ Valid`, 7 `✅ Expected Falsified` | 2603→2343, 3572→2567, 3150→2777, 3572→2567 |
| **P5** | G1R | 2 `✅ Valid`, 2 `✅ Expected Falsified` | 1541→**1402** |
| **P6** | G6R | 2 `✅ Valid`, 2 `✅ Expected Falsified` | 2837→**2196** |

Four-point bar met for each: theorem; vacuity probe at its OWN prep term and OWN
shape; two-sided K on a concrete accepting CEK witness; inhabited shape class.
Statements are unchanged in meaning — P1 in the SIGNED form (`out ≥ in + mintOf`)
in ground-truth vocabulary (`Model.outSum` / `inSum` / `mintSigned` over
`ScriptContext` fields), never a validator accumulator.

## What the source changed, read at `2306678`

`PTransferAct` gained `pownerWdrlIdxs` third (`ProgrammableLogicBase.hs:1148`,
record decl `:1046-1052`). In `pvalueFromCred` (`:328-439`) the owner witness for
a SCRIPT-owned mini-ledger input is now one indexed comparison against
`pdropList # idx # withdrawalEntries` (`:386-393`), replacing the scan
`pisScriptInvokedEntries` (`:282-294`, now dead by its own comment at `:275-280`).
The PUBKEY arm (`:370-376`) does not consume an index.

**`ownerWdrlIdxs = []` is FORCED in every pre-existing shape, not chosen.**
T1R/T2R/T6R/T7R own their mini-ledger input by `StakingHash (PubKeyCredential
owner)` with `owner` a signatory, so the pubkey arm runs; G1R/G6R have no input at
the mini-ledger credential at all, so `withContributing`'s payment gate
(`:351-352`) fails first. Corroborated externally: all four regenerated transfer
goldens carry `[]` (`Goldens/RedeemerGate.lean:286-332`).

**The brief's specific question — do G1R/G6R still get away with ONE script
withdrawal now that owner indices exist? Yes.** No mini-ledger input means the
script arm is unreachable, so entry 0 (`cachedTransferScript0`, `:1205`) remains
the only entry dereferenced.

## SHAPE T8R — closing the gap that answer opens

If every shape takes the pubkey arm, then no theorem touches the line PR #112 was
written to add. N2 found the identical hole on the goldens side. SHAPE T8R
(`Shaped/GlobalShapedR.lean` §7) is T1R with the mini-ledger input owned by a
SCRIPT, **no signatories at all**, three script withdrawals `w0<w1<w2`,
`ownerWdrlIdxs = [2]`, 4-entry redeemer map. `sOwn` and `w2` are independent free
variables.

* `P1R_T8` — P1 in signed form over it: `✅ Valid`.
* `P1R_T8_owner_witness_enforced_thm` — **acceptance implies `sOwn = w2`**:
  `✅ Valid`. This is the compiled-code form of the source's claim at `:381-385`
  that a wrong index "resolves to some other credential and fails this equality".
  With no signatories in the shape, that equality is the ONLY owner authorisation
  in the transaction.
* `P1R_T8_vacuity_probe` — `✅ Expected Falsified`.

## D6 — reach, and a correction about the fix

N4 and N5 hit D6 independently and reached the same root-cause diagnosis. **N5's
fix landed**; N4's workspace patch was different, was wrong, and was discarded.
`WSC/pr/03-blaster-d6-FIX.md`.

N4's contribution is the REACH: N1's **D8 is D6** on a bigger term, and after
PR #112 D6 blocked **every nonzero-mint shaped prep** (G1R, G6R, T2R, T7R),
because #112 moved the mint merge onto CIP-153 `punionValue` (`:1245-1268`).
P5 and P6 are inherently mint-side, so D6 was the difference between them being
provable and being unstatable.

## ⚠ "D9" — I reported a defect that does not exist

An earlier revision of this fragment and of `WSC/pr/05-…` reported a new open
Blaster defect ("Overflow encountered when expanding vector") and concluded
**P6 could not be restored**. That was wrong. The errors were produced by N4's
own bad patch, which discarded the optimized `dite'` binder type but still ran
the optimization over it, leaving the optimizer's caches inconsistent with the
emitted binder. Under N5's fix P6 is green with no other change.

Two bisections were run and both were right about what it was NOT (not the mint
merge; not the budget). Neither tested the variable that had changed under my own
feet — the prover. **The control that would have caught it in minutes is
re-running known-green modules with and without the patch.** My own fix note
listed that control as "not yet done" and I proceeded anyway. Retraction and full
post-mortem: `WSC/pr/05-blaster-issue-d9-bv-overflow.md`.

Nothing in the library was ever at risk from it: the failure mode was a hard
build failure, never a green tick.

## Structural changes

* **`WSC/Prep/GlobalImport.lean` (new)** — `#import_uplc` + `globalInputs1600`,
  split out of `Prep/Global1600.lean` so the shaped preps stop inheriting the
  unshaped prep's failures. They never used `appliedGlobal1600`. (Same idea as
  N3's `Runs/Base.lean` split, arrived at independently.)
* **`WSC/Props/Shaped/P6Vocab.lean` (new)** — P6's ground-truth vocabulary and
  witness helpers, split out of `P6Shaped` so `P6ShapedR` is not coupled to the
  INVALIDATED shape's solver results. Both import it, which keeps the two
  postconditions structurally the same object rather than a drifted restatement.
* **`WSC/Shaped/GlobalShapedP1SOwnPrep.lean` (new)** — SHAPE T8R's prep at 4400.
* **Explicit `(timeout: 1500)` on every solver call** in the six global
  P-modules. They had none and Blaster's default is infinite — a real hang risk
  once the bytecode moved. Hang guard, not a soundness hole.
* `Model/GlobalModel.lean` got an ARITY-ONLY fix so it compiles; it remains
  semantically STALE (still transcribes the pre-#112 scan) and says so at the
  patch site.

## Measurements worth keeping

* `Prep/Global.lean`'s 600-step vacuity characterization is **still `✅ Valid`** —
  600 remains vacuous against the new bytecode.
* `Prep/Global1600` (unshaped, D8's old victim) now succeeds: **1826 s**.
* Seven global shaped preps: 1.7–2.8 s each.
* SHAPE G6R is accept-capable at budget **2400** (`Probe/D9Budget.lean`), so P6's
  3300 carries 1104 steps of slack. NOT acted on: lowering a budget is exactly
  how SHAPE G6 was once silently accept-UNSAT at 2500.
* Axiom census: the Blaster-closed theorems carry `sorryAx` (Blaster closes via
  `admit`) and nothing else; `P5R_shaped_groundtruth` additionally carries
  `Deployed`, `OnChain`, `TS3` — its documented trust surface, unchanged. The K
  theorems carry `ofReduceBool`/`trustCompiler` and NO `sorryAx`.

## Not done

* **No full-library build**, so no new baseline counts are claimed. The
  431-job/162-verdict baseline remains historical.
* **`Probe/T3PrepFAILS` / `T4PrepFAILS` not re-run** against the landed fix.
  They are named for a failure it may have removed; if so, P1's dispatch Paths
  B/C and the input-side aggregation axis reopen. Highest-value follow-up.
* **SHAPE T8R has no class-level realizability theorem.** Its point-level
  inhabitant is established (vacuity probe green ⇒ an accepting
  `validRewardingContext` instance exists), and its redeemer map is built to the
  C1 discipline — 4 entries = 1 script input + 0 mint policies + 3 script
  withdrawals, matching Conway's exact-redeemer count. But the
  `redeemerCoverageAllPlutus … = true` theorem that G1R/G6R/T1R-T7R each carry in
  `GlobalRealizability.lean` was NOT written for T8R. Point (d) is therefore
  partial for T8R and complete for the other five shapes.
* `AUDIT.md`, `STATUS.md`, `README.md`, `EXEC-SUMMARY.md`, `SHAPING-RESULTS.md`,
  `COVERAGE.md`, `SHAPE-BRIDGE.md` still describe the pre-#112 state.
