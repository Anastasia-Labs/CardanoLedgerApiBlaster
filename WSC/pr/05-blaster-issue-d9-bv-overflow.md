# D9 — RETRACTED. There is no such defect.

Task N4, 2026-07-28. **This file is kept as a correction, not as a defect
report.** An earlier revision of it reported "D9" as a new, open Blaster defect
and concluded that P6 could not be restored against wsc-poc main @ `2306678`.
**Both claims were wrong.** P6 is restored and green.

## What was reported

All four solver stanzas of `WSC/Props/Shaped/P6ShapedR.lean` — both theorems and
both mandatory probes — returned

    Unexpected smt error: (error "… Overflow encountered when expanding vector")

instead of a verdict. Two hypotheses were tested and both refuted with committed
probes: the CIP-153 mint merge (`Probe/D9Probe.lean` — SHAPE G1R has a nonzero
mint and passed) and the prep budget (`Probe/D9Budget.lean` — SHAPE G6R at 2400
failed at the identical SMT source position as at 3300).

Those two bisections were sound and their results stand. The conclusion drawn
from them did not.

## What it actually was

**A defect in N4's own workspace patch to Blaster.**

N4 and N5 independently diagnosed D6 (the kernel-ill-typed `Blaster.dite'`) and
independently wrote a fix. The root-cause diagnosis was the same and correct in
both cases. The repairs were not equivalent:

* **N5's, which landed** (`Lean-blaster-wsc` @ `4d320dd`): `optimizeDITE`
  rebuilds both branch binder types from the final condition — the binder types
  are never optimized separately at all.
* **N4's, discarded**: kept optimizing the binder type and then DISCARDED the
  result in the `LambdaWaitForType` continuation (`diteBT.getD optExpr`).

Both produce kernel-well-typed terms, which is why the kernel error went away
under either. But N4's still RAN `optimizeNot` over the binder type, so the
optimizer's hypothesis context and rewrite caches were populated from the
De-Morgan-normalised form while the binder itself carried the un-normalised one.
The SMT translation then ran on an inconsistent state, and Z3 was handed a
malformed vector — "D9".

Once the workspace patch was dropped and the merged tree picked up N5's fix,
`P6ShapedR` went green with no other change:

```
info: WSC/Props/Shaped/P6ShapedR.lean:102:55: ✅ Valid
info: WSC/Props/Shaped/P6ShapedR.lean:151:89: ✅ Valid
info: WSC/Props/Shaped/P6ShapedR.lean:175:57: ✅ Expected Falsified
info: WSC/Props/Shaped/P6ShapedR.lean:199:57: ✅ Expected Falsified
```

## Why this is worth keeping in the record

1. **Nothing in the library ever depended on the wrong fix.** The failure mode
   was a hard SMT error and a hard build failure, never a `✅ Valid`. The bad
   patch could not have produced a green tick over a false goal — it could only
   destroy verdicts. That is the direction the fix note argued a
   rewrite-removing change must fail in, and it is what happened.

2. **"A regression measured and reported" is only a success if the measurement
   is attributed correctly.** Two careful bisections were run and both were
   right about what D9 was NOT; neither tested the one variable that had actually
   changed under this unit's feet — the prover itself. The control that would
   have caught it immediately is the one N5 ran and N4 did not: re-run a set of
   KNOWN-GREEN modules with and without the patch. N4's own fix note listed that
   control as "not yet done" and proceeded anyway. That was the error.

3. **Do not resurrect D9.** If the "expanding vector" error reappears, check the
   Blaster pin before assuming a backend bug.

The two probe modules are kept — `Probe/D9Probe.lean` supplies the mandatory
vacuity probes for SHAPES T1R and T8R and is load-bearing; `Probe/D9Budget.lean`
records a genuine measurement (SHAPE G6R is accept-capable at budget 2400, new
K = 2196). Their headers are corrected.
