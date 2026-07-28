/-
WSC/Shaped/S1Witnesses.lean — the FOUR SHAPE-S1 witness contexts, kept alive
after `WSC/Props/Shaped/P2Shaped.lean` was DELETED (task N6).

WHY THIS FILE EXISTS.  `WSC/Props/Shaped/P2Shaped.lean` — P2 over the PRE-re-cut
SHAPE S1 — is REFUTED at wsc-poc `main` @ 2306678 (PR #112).  Measured, three
failures, all of them real behaviour changes and not bit-rot:

* `P2a_shaped_structure`  ❌ Falsified — #112 deliberately legalised an ada
  top-up on the continuing output (`adaToppedUp`), so "every non-seized policy
  equal, ada included" is false of production.  Task N5 found the same thing at
  SHAPE S1R and restated the conjunct there
  (`WSC.P2a_R_structure` over `seizeStructurePreservedAdaTopUp`, plus
  `WSC.P2a_R_ada_only_tops_up` proving the relaxation is one-directional).
* `P2a_shaped_negative_control` ❌ Falsified — its contrapositive, as expected.
* `P2ShapedWitness.K_is_3004_and_3328` — `native_decide` FALSE: #112 changed the
  seize step counts (the goldens moved 3002→2305, 5079→2905, 2261→1677;
  `WSC/goldens/K-MEASUREMENTS.md` §3).

The module is therefore superseded by `WSC/Props/Shaped/P2ShapedR.lean` over the
node-realizable SHAPE S1R and was deleted rather than repaired: repairing it
would mean redoing task N5's work at a shape that audit finding **F2** already
showed is NOT node-realizable.

WHAT SURVIVES, and is here: the four concrete SHAPE-S1 contexts.  Their ONE
remaining consumer is `WSC/Props/Shaped/RealizableShapes.lean`, whose measurement
*"none of the four old SHAPE-S1 witnesses is redeemer-covered"* is the historical
justification for the S1 → S1R re-cut and is still true and still worth keeping.
`validRewardingContext` still holds of all four (`all_four_valid`, re-checked
against the post-#112 tree).

WHAT IS NOT CARRIED FORWARD, deliberately: the old K measurement and the
`appliedSeizeShaped3800.exec` acceptance witnesses.  Both are about the
superseded shape; the live seize step counts are task N5's
(`WSC.P2RWitness.K_is_2301_and_2412`) and the goldens'.
-/
import WSC.Shaped.SeizeShaped

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

namespace P2ShapedWitness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1 at a leaf assignment; the three instances differ only in the
quantities, the second output's credential and the two non-ada policies. -/
def mk (i0Qty o0Qty : Integer) (escH : ByteString) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (i1CS i1Tn : ByteString) (i1Qty : Integer) (mQ : Integer) : ScriptContext :=
  seizeShapedCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") i0Qty (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 i1CS i1Tn i1Qty
    (ByteString.mk "USERSTK") 300 o0Qty (ByteString.mk "DTM")
    escH 50 o1CS o1Tn o1Qty
    (ByteString.mk "MMM") (ByteString.mk "TOK") mQ
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    50

def ctxAccept : ScriptContext :=
  mk 10 12 (ByteString.mk "CHANGE") (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
     (ByteString.mk "ZZZP") (ByteString.mk "WT") 1 2

def ctxResidual : ScriptContext :=
  mk 9 4 (ByteString.mk "PROGLOGIC") (ByteString.mk "MMM") (ByteString.mk "TOK") 8
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

def ctxEscape : ScriptContext :=
  mk 10 4 (ByteString.mk "CHANGE") (ByteString.mk "MMM") (ByteString.mk "TOK") 9
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

/-- INSTANCE 4 — THE OTHER EXCLUDED CASE, for conjunct 1: `ctxAccept` with the
continuing output's STAKING credential changed from `USERSTK` to `THIEFSTK`, i.e.
a seizure that keeps the tokens at the mini-ledger payment credential but
re-points them at a different holder.  Ledger-legal, inside SHAPE S1, and
violating `seizeStructurePreserved`'s address clause.  Must be REJECTED. -/
def ctxStolen : ScriptContext :=
  seizeShapedCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") 10 (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "THIEFSTK") 300 12 (ByteString.mk "DTM")
    (ByteString.mk "CHANGE") 50 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "MMM") (ByteString.mk "TOK") 2
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    50

-- (`isHaltB` / `isHaltB_sound` are NOT carried over: they only served the deleted
-- module's `native_decide` acceptance and K theorems, which are false at 2306678.
-- The live copies are `WSC.P2RWitness.isHaltB` / `isHaltB_sound`.)

/-- All three instances satisfy the theorems' ledger-normalization hypothesis IN
FULL — including `isBalanced`, which is what makes `ctxEscape` a legitimate
counterexample candidate rather than an impossible transaction. -/
theorem all_four_valid :
    validRewardingContext ctxAccept = true ∧
    validRewardingContext ctxResidual = true ∧
    validRewardingContext ctxEscape = true ∧
    validRewardingContext ctxStolen = true := by native_decide

end P2ShapedWitness

end WSC
