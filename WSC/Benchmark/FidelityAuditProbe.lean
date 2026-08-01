/-
WSC/Benchmark/FidelityAuditProbe.lean — DIFFERENTIAL PROBES for the
model-vs-bytecode fidelity audit of `P1UnshapedForm`'s covering-node clause.

This module does not state or refute anything on its own. It MEASURES, against
the real compiled `programmableLogicGlobal` bytecode, the three questions the
proposed fix (`BaseAbsentProbe.coveringNodeExistsMint`) leaves open:

1. the fix's node pattern is `Data.List (Data.B k :: Data.B n :: _)`. Does the
   bytecode's `pmatch (pfromData (punsafeCoerce @(PAsData PDirectorySetNode) …))`
   (ProgrammableLogicBase.hs:997-1001 at wsc-poc `2306678`) also accept a
   `Data.Constr` or a `Data.Map` datum? If it did, the fix would still be
   STRICTER than the bytecode and the same defect would survive in a new form;
2. `pdropList` is used RAW for the node index (:995). Does an OVERSIZED index
   error (reject), or does it silently resolve to something?
3. does a NEGATIVE index (clamped to 0 by the builtin) open a route the model's
   whole-reference-list scan does not already cover?

Every scenario reuses `BaseAbsentProbe`'s `probeCtx` skeleton, so the only thing
that moves relative to the published refutation `ctxD` is the node datum or the
proof's index.
-/
import WSC.Benchmark.BaseAbsentProbe

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace FidelityAuditProbe

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext TokenName
                          TxInInfo validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open WSC.BaseAbsentProbe (probeCtx redNonMember absentCred dirCS csMMM tnTOK
                          coveringNodeExistsMint)
open P1ShapedWitness (ppCS isHaltB)

/-! ## §1 — candidate node datums the FIX's pattern rejects -/

/-- Same two fields as `BaseAbsentProbe.nodeShort`, but wrapped in a `Constr`
instead of a `List`. `Model.dirNodeFields` and `coveringNodeExistsMint` BOTH
return `none`/`false` here. -/
def nodeConstr2 : Data :=
  Data.Constr 0 [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ")]

/-- Five fields, `Constr`-wrapped — i.e. the honest node payload under the other
`Data` constructor. -/
def nodeConstr5 : Data :=
  Data.Constr 0 [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"),
                 Data.B (ByteString.mk "TLS"), Data.B (ByteString.mk "ILS"),
                 Data.B (ByteString.mk "GS")]

/-- The two fields as a `Map` instead of a `List`. -/
def nodeMap2 : Data :=
  Data.Map [(Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"))]

/-! ## §2 — index probes (raw `pdropList`, :995) -/

/-- `TransferAct [1] [1] [] [NonMember 99] 0` — the node index is past the end
of the two-element reference-input list. -/
def redNonMemberBig : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember 99] 0)

/-- `TransferAct [1] [1] [] [NonMember (-1)] 0` — a NEGATIVE node index, which
the `dropList` builtin clamps to zero (reference input 0 = the params UTxO). -/
def redNonMemberNeg : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember (-1)] 0)

/-! ## §3 — the measurement

`(validRewardingContext, coveringNodeExists CURRENT, coveringNodeExists FIXED,
params clause, outSum, inSum, mintSigned, halts at 4400)`. -/
def report8 (ctx : ScriptContext) (base : Credential)
    : Bool × Bool × Bool × Bool × Integer × Integer × Integer × Bool :=
  let ti := ctx.scriptContextTxInfo
  ( validRewardingContext ctx
  , Model.coveringNodeExists dirCS csMMM ti.txInfoReferenceInputs
  , coveringNodeExistsMint dirCS csMMM ti.txInfoReferenceInputs
  , Benchmark.paramsPublishedBy ctx == some (dirCS, IsData.toData base)
  , Model.outSum base csMMM tnTOK ti.txInfoOutputs
  , Model.inSum base csMMM tnTOK ti.txInfoInputs
  , Model.mintSigned csMMM tnTOK ti.txInfoMint
  , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 4400) )

/-- H — `Constr`-wrapped two-field node, `NonMember` proof, base ABSENT. -/
def ctxH : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeConstr2 redNonMember 4 9 4

/-- I — `Constr`-wrapped FIVE-field node. -/
def ctxI : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeConstr5 redNonMember 4 9 4

/-- J — `Map`-wrapped two-field node. -/
def ctxJ : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeMap2 redNonMember 4 9 4

/-- K — well-formed truncated node, but the proof's index is OUT OF RANGE. -/
def ctxK : ScriptContext :=
  probeCtx (ByteString.mk "ABSENT") BaseAbsentProbe.nodeShort redNonMemberBig 4 9 4

/-- L — well-formed truncated node, but the proof's index is NEGATIVE (clamps to
reference input 0, the params UTxO, whose datum's field 1 is a `Constr`). -/
def ctxL : ScriptContext :=
  probeCtx (ByteString.mk "ABSENT") BaseAbsentProbe.nodeShort redNonMemberNeg 4 9 4

#eval report8 ctxH absentCred
#eval report8 ctxI absentCred
#eval report8 ctxJ absentCred
#eval report8 ctxK absentCred
#eval report8 ctxL absentCred
#eval report8 BaseAbsentProbe.ctxD absentCred

/-! ## §4 — THE MEASURED TABLE

`ctxD` (the published refutation) is the only accepting row. Every perturbation
of the node's `Data` CONSTRUCTOR and every out-of-range index REJECTS, so:

* the bytecode's node decode really does require a `Data.List` — the fix's
  `Data.List (Data.B k :: Data.B n :: _)` pattern is NOT stricter than the
  bytecode on the datum's constructor, which is what the fix needs;
* a `NonMember` index outside `[0, |refs|)` cannot manufacture a node.

Columns: `(validRewardingContext, coveringNodeExists CURRENT,
coveringNodeExists FIXED, params clause, outSum, inSum, mintSigned, halts)`. -/
theorem datum_constructor_and_index_probes :
    (report8 ctxH absentCred == (true, false, false, true, 0, 0, 4, false)) = true
  ∧ (report8 ctxI absentCred == (true, false, false, true, 0, 0, 4, false)) = true
  ∧ (report8 ctxJ absentCred == (true, false, false, true, 0, 0, 4, false)) = true
  ∧ (report8 ctxK absentCred == (true, false, true,  true, 0, 0, 4, false)) = true
  ∧ (report8 ctxL absentCred == (true, false, true,  true, 0, 0, 4, false)) = true
  ∧ (report8 BaseAbsentProbe.ctxD absentCred
       == (true, false, true, true, 0, 0, 4, true)) = true := by
  native_decide

/-- **THE FIVE REJECTIONS ARE `perror`s, NOT BUDGET EXHAUSTION** — same control
as `BaseAbsentProbe.rejections_are_errors_not_budget`, ten times the budget. -/
theorem probe_rejections_are_errors_not_budget :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxH) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxI) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxJ) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxK) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxL) 44000) = false := by
  native_decide

/-! ## §5 — DOES THE WALK'S INPUT-SIDE MEMBERSHIP AGREE WITH `Model.inSum`?

`pvalueFromCred` (:345-395) compares the input's payment credential AS `Data`
against the params datum's raw `progLogicCred` field, while `Model.inSum`
(`WSC/Model/Ground.lean:53-58`) compares the DECODED `WSC.payCred` against
`base`. The two agree only if the context encoder spells an address's payment
credential exactly as `IsData.toData (base : Credential)` does.

`ctxM` discriminates. Base PRESENT, the honest 5-field node keyed `MMM` (so the
transfer proof takes the POSITIVE arm and the policy is RETAINED), a `Member`
mint proof, and only `4` of `MMM.TOK` sent back to the base output:

* if the walk COUNTS the base input, expected = `5 + 4 = 9 > 4` ⇒ REJECT;
* if the walk had SKIPPED it, expected = `4 ≤ 4` ⇒ ACCEPT.

Measured: REJECT — so the walk counts exactly the input `Model.inSum` counts.
`ctxA` (same shape, `qOut = 9`) accepts, which pins that the rejection is the
containment bound and not the shape itself. -/
def ctxM : ScriptContext :=
  probeCtx (ByteString.mk "PROGLOGIC") BaseAbsentProbe.nodeMMM
    BaseAbsentProbe.redMember 4 4 9

theorem walk_counts_the_base_input :
    (report8 ctxM BaseAbsentProbe.plcCred == (true, false, false, true, 4, 5, 4, false)) = true
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxM) 44000) = false
  ∧ (report8 BaseAbsentProbe.ctxA BaseAbsentProbe.plcCred
       == (true, false, false, true, 9, 5, 4, true)) = true := by
  native_decide

#print axioms datum_constructor_and_index_probes
#print axioms probe_rejections_are_errors_not_budget
#print axioms walk_counts_the_base_input

end FidelityAuditProbe
end WSC
