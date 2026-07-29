/-
WSC/Model/SeizeModelRefuted.lean — **`WSC.SeizeModel.seizeModel_faithful` IS NOW
FALSE, machine-checked** (task N5, wsc-poc main `2306678`, PR #112).

WHY THIS MODULE EXISTS.  `WSC/Model/SeizeModel.lean` is a clause-by-clause hand
transcription of the PRE-#112 `mkProgrammableSeize`, and `P2a_bytecode` /
`P2b_model_implies_bytecode` in `WSC/Props/P2_Seize.lean` are bridged to the real
bytecode by the AXIOM `WSC.SeizeModel.seizeModel_faithful`.  That axiom's entire
warrant is the differential test in `WSC/Model/SeizeDiff.lean`.

THE TRAP, and it is a live one.  Re-run against the post-#112 bytecode and the
regenerated goldens, `SeizeDiff` STILL PASSES — `all_13_model_agrees_with_bytecode`
is still `native_decide`-true, 13 out of 13.  A reader who stops there concludes
the model survived PR #112 untouched.  It did not.  The test passes only because
**no golden exercises the behaviour that changed**: all four transfer goldens and
all three seize goldens carry equal lovelace on every continuing pair, so none of
them can tell the old rule from the new one.  A green differential test over a
suite that does not cover the delta is not evidence of fidelity.

WHAT ACTUALLY CHANGED.  #112 deleted the hand-rolled sorted lockstep walk that
`SeizeModel` transcribes and replaced it with a CIP-153 builtin value delta
(`punionValue` of the input and `pscaleValue (-1)` of the output), and in doing
so it legalised an ADA TOP-UP on the continuing output — see the `adaToppedUp`
rationale quoted in `WSC/Spec.lean`.  `SeizeModel` still implements the old
exact-equality rule, so on an ada-topped-up seize the two disagree.

`seize_model_and_bytecode_DISAGREE` below exhibits exactly that: ONE context, on
which the real compiled `programmableSeize` HALTS (accepts) and `seizeModel`
returns `false`.  Both halves are `native_decide`, so this is a computation, not
an argument.  It refutes `seizeModel_faithful` outright.

CONSEQUENCE, stated plainly: every result that flows through
`seizeModel_faithful` — `WSC.P2.P2a_bytecode` and
`WSC.P2.P2b_model_implies_bytecode`, and with them the library's only UNBOUNDED
(non-shape-limited) seize result `P2a_seizeModel_preserves_structure` as a
statement ABOUT PRODUCTION — is INVALID at `2306678`.  The unbounded theorem
itself is still a true theorem about `seizeModel`; it is the bridge to the
bytecode that is broken.  The shaped route is unaffected: `WSC/Props/Shaped/
P2ShapedR.lean` proves P2 against the bytecode directly and cites no model.

NOT DONE, and deliberately so: `SeizeModel` was NOT re-transcribed.  Doing it
honestly means re-transcribing 855 lines against the new builtin-valued delta,
re-proving the unbounded theorem over it, and re-running this gate — a unit of
work in its own right.  Leaving a refuted axiom in place unmarked would have been
worse than leaving it undone and saying so.
-/
import WSC.Shaped.SeizeShapedR
import WSC.Model.SeizeModel
import WSC.Prep.Seize

set_option warn.sorry false
set_option maxRecDepth 1000000

namespace WSC
namespace SeizeModelRefuted

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1R at a leaf assignment, with input-0 and output-0 lovelace given
SEPARATELY (`P2RWitness.mk` pins both at 300, which is precisely why the existing
witnesses cannot see this). -/
def mkAda (i0Ada o0Ada : Integer) (i0Qty o0Qty : Integer) : ScriptContext :=
  seizeRCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") i0Ada
      (ByteString.mk "MMM") (ByteString.mk "TOK") i0Qty (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "USERSTK") o0Ada o0Qty (ByteString.mk "DTM")
    (ByteString.mk "CHANGE") 50 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "MMM") (ByteString.mk "TOK") 2
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    (ByteString.mk "SPRED") (ByteString.mk "MTRED") (ByteString.mk "ILRED")
    50

/-- The CONTROL: lovelace equal on the pair. Old rule and new rule coincide here,
and this is the only case the golden suite covers. -/
def ctxAdaEqual : ScriptContext := mkAda 300 300 10 12

/-- The WITNESS: identical except that the continuing output carries 400 lovelace
where the input it continues carried 300 — an ada TOP-UP, legal under #112 and
illegal under the rule `SeizeModel` transcribes. -/
def ctxAdaToppedUp : ScriptContext := mkAda 300 400 10 12

/-- `true` exactly when the machine reaches a `Halt` state (same definition the
K-pinning probes use, e.g. `WSC/Shaped/Probe/S1K.lean`). -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _       => false

def bytecodeAccepts (ctx : ScriptContext) : Bool :=
  isHaltB
    (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
      (WSC.seizeInputs ppCS ctx) 20000)

/-- **CONTROL — on the ada-EQUAL context the model and the bytecode still agree**
(both accept). Without this the disagreement below could be blamed on a broken
context rather than on the rule change. -/
theorem control_ada_equal_they_agree :
    bytecodeAccepts ctxAdaEqual = true
    ∧ SeizeModel.seizeModel ppCS ctxAdaEqual = true := by native_decide

/-- **`seizeModel_faithful` IS REFUTED.** On `ctxAdaToppedUp` the real compiled
`programmableSeize` ACCEPTS and `seizeModel` REJECTS.

The two contexts differ in exactly ONE leaf — output 0's lovelace, 300 vs 400 —
so the disagreement is attributable to the ada top-up and to nothing else. The
budget is 20000, far above the ~2.3k this shape needs, so the accept is a genuine
halt and not budget-limited. -/
theorem seize_model_and_bytecode_DISAGREE :
    bytecodeAccepts ctxAdaToppedUp = true
    ∧ SeizeModel.seizeModel ppCS ctxAdaToppedUp = false := by native_decide

/-! ## The retraction certificate (task R1)

`seizeModel_faithful` was DELETED at task R1, so the two theorems above no
longer contradict anything that is in the environment.  The theorem below is what
replaces the axiom: the axiom's STATEMENT, refuted as an ordinary Lean fact, so
that the deletion stays justified even after the axiom's text is gone and cannot
be reinstated by accident. -/

/-- **NO SUCH BRIDGE EXISTS.**  The proposition `seizeModel_faithful` used to
assert is refutable: `ctxAdaToppedUp` is accepted by the real compiled
`programmableSeize` (at 20,000 steps, against the ~2.3k this shape needs) and
rejected by `seizeModel`.  A `↔` cannot hold at that context, so no axiom of that
shape may be re-added. -/
theorem no_faithful_bridge :
    ¬ (∀ (pcs : CurrencySymbol) (ctx : ScriptContext),
        SeizeModel.seizeModel pcs ctx = true ↔ SeizeModel.seizeAcceptsUnbounded pcs ctx) := by
  intro h
  have hd := seize_model_and_bytecode_DISAGREE
  have hacc : SeizeModel.seizeAcceptsUnbounded ppCS ctxAdaToppedUp := by
    refine ⟨20000, ?_⟩
    have := hd.1
    unfold bytecodeAccepts isHaltB at this
    unfold SeizeModel.seizeExecAt PlutusCore.UPLC.Utils.isSuccessful
      PlutusCore.UPLC.Utils.isHaltState
    split at this
    · next h' => rw [h']; trivial
    · exact absurd this (by simp)
  have hmodel := (h ppCS ctxAdaToppedUp).mpr hacc
  rw [hd.2] at hmodel
  exact Bool.noConfusion hmodel

end SeizeModelRefuted
end WSC
