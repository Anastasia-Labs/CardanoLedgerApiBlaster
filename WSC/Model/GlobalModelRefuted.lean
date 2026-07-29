/-
WSC/Model/GlobalModelRefuted.lean — **THE RETRACTION CERTIFICATE for
`WSC.Model.globalModel_faithful`** (task R1, wsc-poc main `2306678`, PR #112).

WHAT THIS MODULE IS.  Until task R1 `WSC/Props/P1_Transfer.lean` carried an
axiom

    globalModel_faithful :
      ∀ ppCS ctx, globalModel ppCS ctx = true ↔ isSuccessful (appliedGlobal1600.prop ppCS ctx)

described in its own docstring as "the single trust delta of the B3 route".  It
is FALSE.  Task R1 deleted it and everything that rested on it; this module is
the machine-checked record of WHY, so that the deletion is a measurement in the
build and not a claim in a changelog.

TWO INDEPENDENT REFUTATIONS, both `native_decide`.

**(1) SEMANTIC — finding F24, and the dangerous one.**  PR #112 replaced the
withdrawal-map SCAN that witnessed a script-owned mini-ledger input's owner with
an INDEXED lookup driven by the redeemer's new `plgrOwnerWdrlIdxs` field
(`ProgrammableLogicBase.hs:386-393` at `2306678`; the redeemer field is declared
at `:1043-1051`).  `WSC/Model/GlobalModel.lean` still transcribes the scan
(`gateInput`, `:231-233`) and binds the new field as `_ownerWdrlIdxsUnmodelled`
(`:668-676`).  On `WSC.P1RShapedWitness.ctxSOwnMisindexed` — an owner whose stake
script IS invoked, at withdrawal entry 1, while the redeemer names entry 2 — the
MODEL ACCEPTS and the REAL BYTECODE reaches `State.Error`.  The model is
therefore UNSOUND, not merely conservative: it accepts a transaction the
production script refuses.  The two contexts differ in exactly one leaf (`sOwn`),
and `ctxSOwn` (the accepting sibling) plus `ctxSOwnNoWitness` (an owner in no
withdrawal entry at all) are the controls on either side.

**(2) BUDGET — structural, and it did not need PR #112 at all.**  The axiom's
right-hand side is `appliedGlobal1600`, i.e. a run METERED AT 1600 CEK STEPS
(`WSC/Prep/Global1600.lean`, whose own header says 1600 is the only measured
accept-capable budget that terminates in prep).  `WSC/Model/GlobalGoldens.lean`
proves the model ACCEPTS `programmableLogicGlobal.transfer-member-single-policy`
— and that golden's run costs **K = 2,782** CEK steps, measured here and pinned
two-sided (`golden_shows_budget_gap`).  2,782 > 1,600, so on that context the
axiom's left-hand side is `true` and its right-hand side is FALSE: the
left-to-right direction fails at a real off-chain-produced transaction, for a
reason that has nothing to do with PR #112.  Any accepting transfer above the
budget refutes it the same way; this golden is merely the cheapest one in the
suite that does.  (K = 2,782 is a NEW measurement at `2306678`; the 3,262 in
`WSC/goldens/K-MEASUREMENTS.md` §3 is the PRE-#112 figure for the pre-#112
golden, and PR #112's scan-to-index rewrite made the run cheaper, exactly as
`P1RShapedWitness.K_T8R_is_2288` reports at shape level.)

WHY THE `exec` FORM.  `WSC/Shaped/Probe/BridgeProbe2FAILS.lean` measured that
`#prep_uplc`'s `prop` and `exec` are NOT definitionally equal, so a `native_decide`
cannot speak about `prop`.  Every statement below is therefore about
`cekExecuteProgram programmableLogicGlobal1600.script (globalInputs1600 …)` — the
`exec` side, i.e. the actual CEK run of the imported production flat, which is the
same object the library's K-measurements, its acceptance witnesses and
`WSC/Model/SeizeModelRefuted.lean` all use.  Refutation (1) is about that program
at any budget it is given: the machine reaches `State.Error`, not budget
exhaustion, so no larger meter rescues it.

CONSEQUENCE, and it is a STRICT IMPROVEMENT.  Everything that routed through it
is gone: `P1_bytecode`, `P1_bytecode_of_P1_model`, `P6_bytecode`,
`P6_bytecode_of_P6_model`.  Nothing of value went with them — `P1_model` and
`P6_model` were never proved (they are `Prop` definitions whose links L1.1a/b and
L1.2-L1.6 are open), so the B3 route never produced a proved statement about the
bytecode for P1 or P6 in the first place, and P1/P5/P6 are all proved AT UPLC
against the compiled program with no faithfulness axiom at all
(`WSC/Props/Shaped/P1Shaped.lean`, `P1ShapedR.lean`, `P1ShapedBC.lean`,
`P5ShapedR.lean`, `P6ShapedR.lean`).  See `WSC/AUDIT.md` entry **R1**.
-/
import WSC.Props.Shaped.P1ShapedR
import WSC.Model.GlobalGoldens

set_option warn.sorry false
set_option maxRecDepth 1000000

namespace WSC
namespace GlobalModelRefuted

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)
open WSC.P1ShapedWitness (ppCS isHaltB isHaltB_sound)
open WSC.P1RShapedWitness (ctxSOwn ctxSOwnMisindexed ctxSOwnNoWitness)

/-- `true` exactly on `State.Error` — the machine REFUSED, as opposed to running
out of meter.  Mirror of `PlutusCore.UPLC.Utils.isUnsuccessful`, in `Bool` so that
`native_decide` can see it. -/
def isErrB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Error => true
  | _      => false

theorem isErrB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isErrB s = true → isUnsuccessful s := by
  intro h; cases s <;> simp [isErrB] at h <;> trivial

/-- The real compiled `programmableLogicGlobal` run on exactly the inputs
`appliedGlobal1600` is prepped over (`WSC/Prep/GlobalImport.lean`
`globalInputs1600`), with the step count left FREE. -/
def globalExecAt (n : Nat) (pcs : CurrencySymbol) (ctx : ScriptContext) :
    PlutusCore.UPLC.CekMachine.State :=
  PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
    (globalInputs1600 pcs ctx) n

/-! ## 1. The SEMANTIC refutation (F24) -/

/-- **CONTROL — the accepting sibling.**  On `ctxSOwn` the model and the bytecode
still agree: both accept.  Without this the disagreement below could be blamed on
a malformed context rather than on the rule PR #112 changed. -/
theorem control_ctxSOwn_they_agree :
    Model.globalModel ppCS ctxSOwn = true
    ∧ isHaltB (globalExecAt 20000 ppCS ctxSOwn) = true := by native_decide

/-- **`globalModel_faithful` IS REFUTED — the model ACCEPTS what production
REFUSES.**  `ctxSOwnMisindexed` differs from `ctxSOwn` in the single leaf `sOwn`.
The model says `true`; the real bytecode reaches `State.Error` with 20,000 steps
available, against the 2,288 the accepting sibling needs
(`P1RShapedWitness.K_T8R_is_2288`), so this is a refusal and not budget
exhaustion.  The divergence runs in the UNSOUND direction. -/
theorem global_model_and_bytecode_DISAGREE :
    Model.globalModel ppCS ctxSOwnMisindexed = true
    ∧ isErrB (globalExecAt 20000 ppCS ctxSOwnMisindexed) = true := by native_decide

/-- The same fact in the library's `Prop` vocabulary: the production program is
`isUnsuccessful` on a context the source model accepts. -/
theorem bytecode_rejects_what_the_model_accepts :
    Model.globalModel ppCS ctxSOwnMisindexed = true
    ∧ isUnsuccessful (globalExecAt 20000 ppCS ctxSOwnMisindexed) :=
  ⟨global_model_and_bytecode_DISAGREE.1,
   isErrB_sound _ global_model_and_bytecode_DISAGREE.2⟩

/-- **CONTROL — the failure mode the pre-#112 scan also rejected.**  On
`ctxSOwnNoWitness` the owner appears in no withdrawal entry at all; model and
bytecode agree that this is a reject.  So the model is not simply broken: it is
broken exactly at the line #112 added. -/
theorem control_ctxSOwnNoWitness_they_agree :
    Model.globalModel ppCS ctxSOwnNoWitness = false
    ∧ isErrB (globalExecAt 20000 ppCS ctxSOwnNoWitness) = true := by native_decide

/-! ## 2. The BUDGET refutation — true before PR #112 as well -/

/-- The golden the model is proved to accept in
`WSC/Model/GlobalGoldens.lean` (`model_matches_bytecode_member_single_policy`). -/
def memberSinglePolicy : WSC.Goldens.Vector :=
  WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy

/-- **THE BUDGET GAP, as a computation.**  On the decoded
`transfer-member-single-policy` golden: the model ACCEPTS, the bytecode does NOT
halt within the axiom's own 1,600-step meter, and K is pinned TWO-SIDED at
**2,782** (halts at 2782, budget-errors at 2781).  So
`globalModel … = true ↔ isSuccessful (appliedGlobal1600 … )` fails
left-to-right at a real off-chain-produced transaction — a defect of the axiom's
STATEMENT, independent of PR #112 and of the F24 divergence above. -/
def goldenBudgetGap : Bool :=
  match Model.Goldens.ppCSOf memberSinglePolicy, Model.Goldens.ctxOf memberSinglePolicy with
  | some p, some c =>
      Model.globalModel p c
        && !isHaltB (globalExecAt 1600 p c)
        && isHaltB (globalExecAt 2782 p c)
        && !isHaltB (globalExecAt 2781 p c)
  | _, _ => false

theorem golden_shows_budget_gap : goldenBudgetGap = true := by native_decide

end GlobalModelRefuted
end WSC
