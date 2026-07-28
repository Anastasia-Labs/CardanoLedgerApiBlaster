/-
WSC/Shaped/Probe/T4PrepFAILS.lean — **REGRESSION TEST for upstream Blaster
defect D6. THE FILENAME IS HISTORICAL: THIS MODULE NOW BUILDS.**

Companion to `T3PrepFAILS.lean`; read that module's header first, it carries the
full account. Kept under its old name for the same reason (cited by path across
`WSC/`).

SHAPES T4/T5 exercise INPUT-SIDE aggregation: two mini-ledger inputs, so
`pvalueFromCred` reaches phase 3 and merges them with the CIP-153 builtin
`punionValue`. Until 2026-07-28 both preps died in the kernel with the D6
`Blaster.dite'` motive mismatch — here the offending rewrite is De Morgan on
`¬(A ∧ B)` rather than T3's `¬(true = b)`, which is why the pair is worth
keeping: they cover the two DISTINCT normalisations that trigger the defect.

**D6 IS FIXED** (Blaster `wsc-d6-dite-branch-retype` @ `4d320dd`, task N5:
`optimizeDITE` rebuilds both branch binder types from the final condition).
MEASURED at that commit, warm: `lake build WSC.Shaped.Probe.T4PrepFAILS` →
**exit 0, 0 errors, 9.4 s**, both `#prep_uplc` commands completing.

**RETRACTED.** This docstring used to say:

> Phase 3 of `pvalueFromCred` is therefore unreachable at UPLC with this
> substrate, and with it ARCHITECTURE.md §3-P1's lemma L1.3 on shapes with more
> than one mini-ledger input.

That is now FALSE and is withdrawn: phase 3 preps. What is still true, and is
the reason no P1 result is claimed here, is that SHAPES T4/T5 are PRE-RE-CUT and
so are not node-realizable (their redeemer maps are not exact — audit **F2**);
input-side aggregation needs a re-cut T4R before it can be proved to this
library's four-point bar. Unlike T3 no vacuity probe is stated here, so the
non-emptiness of T4/T5's accept classes is UNMEASURED — do not assume it.

The shape definitions themselves are fine and are still used: the K measurements
and the source-model cross-check in `WSC/Shaped/Probe/T4Probe.lean` build and
pass (SHAPE T4 K = 3001, SHAPE T5 burn K = 3970). The OUTPUT-side aggregation
dimension does not go through any builtin (Path A adds with plain Integer
addition) and IS proved — SHAPES T6/T7, `WSC/Props/Shaped/P1Shaped.lean` §5.
Recorded in `WSC/status-fragments/V1-P1-shaped.md`.
-/
import WSC.Shaped.GlobalShapedP1Agg
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC

#prep_uplc appliedGlobalShapedT4 programmableLogicGlobal1600 p1ShapedAggInputs 4400
#prep_uplc appliedGlobalShapedT5 programmableLogicGlobal1600 p1ShapedAggMintInputs 4400

end WSC
