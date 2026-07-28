/-
WSC/Shaped/Calib/P3Unshaped.lean — CALIBRATION BASELINE (task Z2, rung 1),
**RETIRED AS AN EXECUTABLE RUNG BY TASK N3** (wsc-poc PR #112).

WHAT THIS MODULE USED TO BE.  P3 and its vacuity probe against the UNSHAPED prep
(`WSC/Prep/Base.lean`, fully symbolic `ScriptContext`, budget 600), in a module
of its own so `lake build WSC.Shaped.Calib.P3Unshaped` timed the SMT solve from
scratch.  It was the CONTROL against which `WSC/Shaped/Calib/P3Shaped.lean`
measured what shaping buys, on the one property where both rungs closed.

WHY IT IS NOW PROSE.  Against the post-#112 bytecode NEITHER unshaped goal
returns a verdict:

| goal, UNSHAPED at `appliedBase.prop`, budget 600 | Z3 cap | verdict |
|---|---|---|
| `P3_unshaped`         | 600 s | `⚠️ Undetermined` |
| `P3_unshaped_vacuity` | 600 s | `⚠️ Undetermined` |
| both, again           | 2400 s | `⚠️ Undetermined` |
| both, uncapped (what this module shipped: `by blaster` with no timeout) | ∞ | no verdict at 93 min |

The last row is why the declarations are DELETED rather than merely re-measured:
an uncapped `blaster` on this goal does not terminate, so leaving it here hangs
every `lake build WSC` forever.  That is not a soundness problem — a `blaster`
that returns no verdict leaves the goal open and the build FAILS, it never
admits — it is a liveness one, and the honest fix is to retire the rung and
publish the measurement.

THE CALIBRATION ITSELF SURVIVES, with a different and sharper answer: see
`WSC/Shaped/Calib/P3Shaped.lean`, which is now the whole rung.

RE-RUNNABLE COPIES of every goal above, with explicit caps and the exact
commands, are in `WSC/Props/P3Unshaped.lean.disabled`.  Nothing is lost; it is
just not built.

CROSS-REFERENCES: `WSC/Props/P3_Base.lean` §MEASUREMENT (the full table,
including two further escalations that also fail — a redeemer-only shape, and a
smaller prep budget), `WSC/IMPACT-PR112.md` APPENDIX N3.
-/
import WSC.Prep.Base

namespace WSC.Z2Calib

-- Deliberately empty of declarations.  See the header: every declaration this
-- module used to carry is a `blaster` goal that no longer returns a verdict
-- against the post-#112 base bytecode.  The import is kept so the module still
-- names the prep the retired rung was about.

end WSC.Z2Calib
