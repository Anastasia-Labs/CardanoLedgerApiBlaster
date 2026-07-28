/-
WSC/Shaped/Calib/P3Shaped.lean — CALIBRATION (task Z2, rung 1),
**RE-CUT BY TASK N3** against wsc-poc `main` @ 2306678 (PR #112).

════════════════════════════════════════════════════════════════════════════
THE CALIBRATION, RE-RUN — and the answer changed
════════════════════════════════════════════════════════════════════════════
Rung 1 exists to isolate exactly one variable — the shape — on the one property
where the unshaped route was known to work. Same flat, same budget 600, same
statement, same postcondition; only the `Data` skeleton differs.

PRE-#112 the answer was "shaping is a speed-up": both rungs closed, the shaped
one faster.

POST-#112 the answer is "shaping is the difference between a verdict and no
verdict", and there is a third rung that did not exist before:

| rung | shape | P3 | vacuity probe | wall |
|---|---|---|---|---|
| 1 — UNSHAPED (`WSC/Shaped/Calib/P3Unshaped.lean`) | fully symbolic ctx | `⚠️ Undetermined` @600 s, @2400 s; no verdict uncapped at 93 min | `⚠️ Undetermined` | — |
| 2 — SHAPE B1, the OLD cut (`WSC/Shaped/BaseShaped.lean`) | 2 script wdrl, 1 redeemer entry, redeemer `Data.I red` | vacuously true | **`Valid`** — the accept class is EMPTY | 5.1 s |
| 3 — SHAPES B1RG/B1RS, the NEW cut (`WSC/Shaped/BaseShapedR.lean`) | 2 script wdrl, 3 redeemer entries, redeemer `Constr tag [I red]`, `red` symbolic | **`✅ Valid`** | **`✅ Expected Falsified`** | < 2 s |

Rung 2 is the module below, and it is the one measurement in this campaign where
a vacuity probe returning `Valid` is the INTENDED result: SHAPE B1's redeemer is
a bare `Data.I`, the post-#112 validator opens the redeemer with `pasConstr`,
and `pasConstr` on a `Data.I` errors. So nothing of that shape can be accepted,
and everything ever proved over `appliedBaseShaped` is now VACUOUSLY true —
exactly the failure mode this campaign's four-point bar exists to catch.

The live rung-3 results are in `WSC/Props/Shaped/P3ShapedR.lean` (which carries
the same emptiness result as its §5 retirement notice, since that is where a
reader of P3 will look for it). This module keeps the CALIBRATION framing and
the before/after table; it deliberately does not duplicate the rung-3 theorems.

WHAT THE CALIBRATION NOW SAYS, in one sentence: on this validator the shape is
not an optimisation — it is the only reason there is a theorem at all, and the
cut has to be redeemer-aware or the class it names is empty.

The postcondition is unchanged and is still quoted through ledger vocabulary;
see `WSC.baseRShapedCtx_wdrl` in the new shape module for the `rfl` audit link
that `WSC.baseShapedCtx_wdrl` used to provide here.
-/
import WSC.Shaped.BaseShaped
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Calib

open CardanoLedgerApi.V3 (ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **RUNG 2 — SHAPE B1'S ACCEPT CLASS IS EMPTY UNDER THE POST-#112 BYTECODE.**

Expected result: **Valid** — note the polarity, and note that it is the OPPOSITE
of what a vacuity probe normally must return. `Valid` here means "no leaf
assignment of SHAPE B1 is accepted", i.e. the class `WSC/ShapeBridge.lean`'s
`bridge_B1` / `inputs_B1` / `exec_B1` / `control_B1_*` stanzas range over
contains no accepting transaction at all.

CAUSE, from the source: the shape sets `scriptContextRedeemer := Data.I red`
(`WSC/Shaped/BaseShaped.lean`), because the PRE-#112 validator never read its
redeemer. The POST-#112 validator opens it with `pasConstr`
(`ProgrammableLogicBase.hs:715`), which errors on a `Data.I` before any
withdrawal is looked at.

Stated as a `def` + `#blaster` rather than a `theorem` on purpose: it is a
MEASUREMENT of a class that should now be deleted, not a result to build on. -/
def B1_accept_class_is_empty : Prop :=
  ∀ (gh sh : ScriptHash) (txid : ByteString) (idx : Integer) (baseHash : ScriptHash)
    (lovelace : Integer) (w0 w1 : ScriptHash) (a0 a1 fee red lo hi : Integer)
    (tid : ByteString),
    ¬ isSuccessful (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1
                      a0 a1 fee red lo hi tid)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 0) [B1_accept_class_is_empty]

end WSC.Z2Calib
