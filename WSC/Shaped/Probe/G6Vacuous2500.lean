-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/Probe/G6Vacuous2500.lean — task V3 NEGATIVE RESULT, preserved.

SHAPE G6 (WSC/Shaped/GlobalMemberShaped.lean) was FIRST attempted at CEK budget
**2500**, by analogy with the P4 shapes.  At that budget the shape class is
**accept-UNSAT**: the mandatory vacuity probe returns `Valid` (= genuinely
vacuous), so the P6 obligation, which also returned `Valid` there, was EMPTY.

Cause, measured in `WSC/Shaped/Probe/G6Diag.lean`: the concrete SHAPE G6 witness
costs **K = 2837** CEK steps, and the real CEK machine `Error`s on budget
exhaustion at 2500.  Budget 3300 fixes it and is what
`WSC/Props/Shaped/P6Shaped.lean` uses.

WHY THIS FILE EXISTS. It is the machine-checked record that the vacuity probe
earned its keep on this shape: no other stanza in the control set (negative
control, tightness, the `Valid` main obligation) distinguishes "proved" from
"the accept hypothesis is unsatisfiable".  Keep it green — `solve-result: 0`
encodes "expected `Valid`", i.e. expected VACUOUS, as in
WSC/Props/P4_Minting.lean's `minting600_is_vacuous`.
-/
import WSC.Shaped.GlobalMemberShaped
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (CurrencySymbol validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

-- The SAME shape, prepped at the budget that turned out to be too low.
#prep_uplc appliedGlobalMemberShaped2500 programmableLogicGlobal1600 memberShapedInputs 2500

/-- **MEASURED NEGATIVE RESULT.** "No accepting shape-G6 context exists within
2500 CEK steps" is **`Valid`** — the class really is empty at that budget, because
the witness needs 2837 steps.  Expected `Valid` ⟹ `solve-result: 0`. -/
def G6_vacuous_at_2500 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalMemberShaped2500.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)

#blaster (gen-cex: 0) (solve-result: 0) [G6_vacuous_at_2500]

end WSC
