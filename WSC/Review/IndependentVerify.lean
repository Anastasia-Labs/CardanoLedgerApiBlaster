/-
WSC/Review/IndependentVerify.lean — **INDEPENDENT ADVERSARIAL VERIFICATION of the
repaired P1 statement.** Written by the verifying agent, NOT by the implementer;
it deliberately does not reuse `BaseAbsentProbe.report` or
`ExemptionCensus.halts`, and it re-derives every quantity it compares.

It answers four questions the implementer's own probes do not:

1. **Is `dirCS` the one the STATEMENT pins, or a hardcoded constant?**
   `BaseAbsentProbe.repaired_statement_excludes_the_witnesses` evaluates
   `Model.isProgrammable dirCS …` at the LITERAL `dirCS = "DIRCS"`. The statement
   pins `dirCS` through `Model.paramsPublishedBy`. §1 below derives it from the
   context and checks the exclusion at THAT value.
2. **Does the repaired hypothesis form H actually have no counterexample among
   the known-bad contexts?** §2 computes all four hypotheses AND the conclusion
   of `P1UnshapedFormH` at five contexts in one table.
3. **Is the accept class non-empty at the OBLIGATION's meter?** §3 runs the CEK
   at 300000 — `WSC/Benchmark/P1Unshaped.lean:156`'s `#prep_uplc` budget — not at
   the 4400 of the shipped non-vacuity certificate.
4. **Is there a THIRD node-shape / node-authentication route?** §4 sweeps datum
   shapes and a mis-ordered directory NFT that the shipped census does not cover,
   comparing bytecode acceptance against `Model.exemptible` point by point.
-/
import WSC.Benchmark.BaseAbsentProbe
import WSC.Benchmark.P1UnshapedStatement

namespace WSC
namespace IndependentVerify

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open P1ShapedWitness (ppCS isHaltB)
open BaseAbsentProbe (ctxA ctxD ctxF ctxG nodeShort probeCtx probeCtxN redNonMember
                      csMMM tnTOK plcCred absentCred)

/-! ## §1 — the exclusion, at the `dirCS` the STATEMENT pins -/

/-- The directory CS this transaction's own params datum publishes, read through
the shipped `Model.paramsPublishedBy`. `none` is reported as `""`, which is the
ada slot, so a `none` here could not masquerade as a passing test. -/
def publishedDirCS (ctx : ScriptContext) : CurrencySymbol :=
  match Model.paramsPublishedBy ctx with
  | some (d, _) => d
  | none => ByteString.mk ""

/-- `isProgrammable` at the DERIVED `dirCS`, not at a literal. -/
def progAtPublished (ctx : ScriptContext) (cs : CurrencySymbol) : Bool :=
  Model.isProgrammable (publishedDirCS ctx) cs
    ctx.scriptContextTxInfo.txInfoReferenceInputs

/-- **The published `dirCS` really is `"DIRCS"` at all five probe contexts**, so
the shipped exclusion theorem is not checking the wrong currency symbol. -/
theorem published_dirCS_is_DIRCS :
    (( publishedDirCS ctxD, publishedDirCS ctxF, publishedDirCS ctxG
     , publishedDirCS ctxA, publishedDirCS P1RShapedWitness.ctxOk )
     == (ByteString.mk "DIRCS", ByteString.mk "DIRCS", ByteString.mk "DIRCS",
         ByteString.mk "DIRCS", ByteString.mk "DIRCS")) = true := by native_decide

/-- **The exclusion, re-measured at the derived `dirCS`.** Same verdict as the
shipped theorem, but nothing is hardcoded. -/
theorem exclusion_at_derived_dirCS :
    (( progAtPublished ctxD csMMM, progAtPublished ctxF csMMM
     , progAtPublished ctxG csMMM, progAtPublished ctxA csMMM
     , progAtPublished P1RShapedWitness.ctxOk csMMM )
     == (false, false, false, true, true)) = true := by native_decide

/-! ## §2 — the whole of `P1UnshapedFormH`, at five contexts, in one table -/

/-- `(validRewardingContext, params-clause, isProgrammable, halts@44000,
outSum, inSum, mintSigned)` — every hypothesis of `P1UnshapedFormH` plus the
three numbers its conclusion compares. A REFUTATION is a row whose first four
components are `true` and whose `outSum < inSum + mintSigned`.

The meter is 44000 — ten times the benchmark's 4400 — so a row reading `false`
in the halting column is a genuine REJECTION and not a budget artefact. -/
def hRow (ctx : ScriptContext) (base : Credential) (cs : CurrencySymbol)
    (tn : TokenName) : Bool × Bool × Bool × Bool × Integer × Integer × Integer :=
  let ti := ctx.scriptContextTxInfo
  ( validRewardingContext ctx
  , Model.paramsPublishedBy ctx == some (publishedDirCS ctx, IsData.toData base)
  , progAtPublished ctx cs
  , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 44000)
  , Model.outSum base cs tn ti.txInfoOutputs
  , Model.inSum base cs tn ti.txInfoInputs
  , Model.mintSigned cs tn ti.txInfoMint )

/-- `true` iff this row is a counterexample to `P1UnshapedFormH`. -/
def refutes (r : Bool × Bool × Bool × Bool × Integer × Integer × Integer) : Bool :=
  r.1 && r.2.1 && r.2.2.1 && r.2.2.2.1 &&
    decide (r.2.2.2.2.1 < r.2.2.2.2.2.1 + r.2.2.2.2.2.2)

/-- **NO KNOWN-BAD CONTEXT REFUTES THE REPAIRED FORM.** `ctxD`/`ctxF` (mint walk)
and `ctxG` (transfer walk) all fail the `isProgrammable` hypothesis; the two
accepting controls satisfy every hypothesis and their conclusions HOLD. -/
theorem no_row_refutes_H :
    (( refutes (hRow ctxD absentCred csMMM tnTOK)
     , refutes (hRow ctxF plcCred csMMM tnTOK)
     , refutes (hRow ctxG plcCred csMMM tnTOK)
     , refutes (hRow ctxA plcCred csMMM tnTOK)
     , refutes (hRow P1RShapedWitness.ctxOk plcCred csMMM tnTOK) )
     == (false, false, false, false, false)) = true := by native_decide

/-! The same five rows, printed, so the `false`s above are traceable to numbers
rather than taken on trust. Also: the SHIPPED §4 certificate's docstring claims
`Model.Contained` at `ctxOk` "reads 150 ≥ 150 + 0"; the two `#eval`s at the end
measure what it actually reads. -/
#eval hRow ctxD absentCred csMMM tnTOK
#eval hRow ctxF plcCred csMMM tnTOK
#eval hRow ctxG plcCred csMMM tnTOK
#eval hRow ctxA plcCred csMMM tnTOK
#eval hRow P1RShapedWitness.ctxOk plcCred csMMM tnTOK
#eval Model.outSum plcCred csMMM tnTOK
  P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoOutputs
#eval Model.inSum plcCred csMMM tnTOK
  P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoInputs

/-! ## §3 — non-vacuity AT THE OBLIGATION'S OWN METER

`WSC/Benchmark/P1Unshaped.lean:156` preps at **300000**, not at 4400. The shipped
non-vacuity certificate (`P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600`) is
measured at 4400 and relies on the reader to accept that halting at 4400 implies
halting at 300000. That step is not proved anywhere in the tree, so it is
measured directly here. -/
theorem accept_class_inhabited_at_the_obligation_meter :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script
      (globalInputs1600 ppCS P1RShapedWitness.ctxOk) 300000) = true := by native_decide

/-- …and the same at the accepting control, on a different validator path
(`Member` mint, base present). Two distinct accepting transactions. -/
theorem control_also_halts_at_the_obligation_meter :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script
      (globalInputs1600 ppCS ctxA) 300000) = true := by native_decide

/-! ## §4 — HUNTING A THIRD ROUTE

Two attacks the shipped census does not run.

**(a) DATUM SHAPES.** The shipped arity floor sweeps a one-field list, a non-`B`
key, a non-`B` next, `Constr 0 [B, B]` and `Map [(B, B)]`. It does NOT sweep a
NON-ZERO constructor index, a bare `B`, a bare `I`, or a list whose third field
is present but junk. Each row below is `(bytecode accepts, Model.exemptible)`; a
route is a row reading `(true, false)`.

**(b) A MISPLACED DIRECTORY NFT.** `Model.hasCSH` reads the SECOND value entry
only, mirroring `phasCSH` (:750-753). If the bytecode instead SCANNED — the
`phasCSHOrFalse` semantics used at :807 for params discovery — then a node whose
directory token sits at the THIRD entry would exempt in the bytecode and be
invisible to `Model.exemptible`. That is a defect-2-shaped hole one level down,
and nothing in the tree measures it. -/

/-- `Constr 1`, not `Constr 0`. -/
def nodeConstr1 : Data :=
  Data.Constr 1 [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ")]

/-- A bare bytestring where a node should be. -/
def nodeBareB : Data := Data.B (ByteString.mk "AAA")

/-- A bare integer where a node should be. -/
def nodeBareI : Data := Data.I 7

/-- Two `B` fields and a junk third — accepted by BOTH readers, so this row is a
control that the sweep can distinguish `(true, true)` from `(true, false)`. -/
def nodeJunkThird : Data :=
  Data.List [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"), Data.I 0]

/-- Six fields — beyond the honest arity. -/
def nodeSix : Data :=
  Data.List [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"),
             Data.I 1, Data.I 2, Data.I 3, Data.I 4]

/-- `(bytecode accepts at 44000, Model.exemptible at the published dirCS)` for a
`NonMember` mint proof pointed at a node carrying datum `d`. -/
def shapeRow (d : Data) : Bool × Bool :=
  let ctx := probeCtx (ByteString.mk "ABSENT") d redNonMember 4 9 4
  ( isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 44000)
  , Model.exemptible (publishedDirCS ctx) csMMM
      ctx.scriptContextTxInfo.txInfoReferenceInputs )

/-- **NO DATUM SHAPE SEPARATES THE BYTECODE FROM `Model.exemptible`.** Every row
is `(true, true)` or `(false, _)`; none is `(true, false)`. -/
theorem datum_shape_sweep :
    (( shapeRow nodeShort, shapeRow nodeJunkThird, shapeRow nodeSix
     , shapeRow nodeConstr1, shapeRow nodeBareB, shapeRow nodeBareI )
     == ( (true, true), (true, true), (true, true)
        , (false, false), (false, false), (false, false) )) = true := by
  native_decide

/-- A node whose value carries the directory NFT at the THIRD entry, behind an
unrelated policy: `[ada, ("AAAA", …), ("DIRCS", …)]`. Sorted and positive, so it
clears `validTxOutValue`. -/
def misplacedNFTNode : TxInInfo :=
  ⟨⟨ByteString.mk "", 3⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "DIRNODE"), none⟩
   , txOutValue :=
       [ (Data.B (ByteString.mk ""), Data.Map [(Data.B (ByteString.mk ""), Data.I 100)])
       , (Data.B (ByteString.mk "AAAA"), Data.Map [(Data.B (ByteString.mk "T"), Data.I 1)])
       , (Data.B (ByteString.mk "DIRCS"),
          Data.Map [(Data.B (ByteString.mk "NODETOK"), Data.I 1)]) ]
   , txOutDatum := .OutputDatum nodeShort
   , txOutReferenceScript := none }⟩

/-- `ctxD` with the directory node's NFT moved off the first non-ada slot. -/
def ctxMisplaced : ScriptContext :=
  { ctxD with scriptContextTxInfo :=
      { ctxD.scriptContextTxInfo with
        txInfoReferenceInputs :=
          match ctxD.scriptContextTxInfo.txInfoReferenceInputs with
          | p :: _ => [p, misplacedNFTNode]
          | [] => [] } }

/-- **`phasCSH` IS POSITIONAL ON THE EXEMPTION PATH, AND `Model.hasCSH` AGREES.**
The context is still ledger-valid and the params clause still holds, but the
bytecode REJECTS and `Model.exemptible` is FALSE — the two move together, so this
is not a route. (Had the bytecode accepted, the row would read `(…, true, false)`
and `P1UnshapedFormH` would be refuted with `0 ≥ 0 + 4`.) -/
theorem misplaced_nft_is_not_a_route :
    (( validRewardingContext ctxMisplaced
     , Model.paramsPublishedBy ctxMisplaced
         == some (ByteString.mk "DIRCS", IsData.toData absentCred)
     , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxMisplaced) 44000)
     , Model.exemptible (ByteString.mk "DIRCS") csMMM
         ctxMisplaced.scriptContextTxInfo.txInfoReferenceInputs )
     == (true, true, false, false)) = true := by native_decide

/-! ## §5 — THE ADDRESSING OVER-APPROXIMATION, MEASURED

`Model.exemptible` is an existential over the whole reference-input list while
the bytecode reads the node the redeemer ADDRESSES. The direction of that
looseness is the safe one — it can only make `exempt` fire more often — but it is
worth exhibiting, because a reader who assumes the two coincide will
mis-attribute the next refutation. Below: the proof index is out of range, so the
bytecode `perror`s, yet `exemptible` still sees the covering node. -/

/-- `TransferAct [1] [1] [] [NonMember 5] 0` — index 5 is past the end of a
2-element reference list. -/
def redNonMemberFar : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember 5] 0)

/-- `TransferAct [1] [1] [] [NonMember (-1)] 0` — `pdropList` CLAMPS to 0, which
addresses the params UTxO, whose second field is a `Constr` and not a `B`. -/
def redNonMemberNeg : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember (-1)] 0)

/-- **THE OVER-APPROXIMATION IS REAL AND ONE-SIDED.** Both contexts REJECT while
`Model.exemptible` reads `true`: the statement declines to speak about them. It
never runs the other way — that would be the refutation. -/
theorem addressing_overapproximation :
    (( isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script
         (globalInputs1600 ppCS (probeCtx (ByteString.mk "ABSENT") nodeShort
             redNonMemberFar 4 9 4)) 44000)
     , Model.exemptible (ByteString.mk "DIRCS") csMMM
         (probeCtx (ByteString.mk "ABSENT") nodeShort redNonMemberFar 4 9
             4).scriptContextTxInfo.txInfoReferenceInputs
     , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script
         (globalInputs1600 ppCS (probeCtx (ByteString.mk "ABSENT") nodeShort
             redNonMemberNeg 4 9 4)) 44000)
     , Model.exemptible (ByteString.mk "DIRCS") csMMM
         (probeCtx (ByteString.mk "ABSENT") nodeShort redNonMemberNeg 4 9
             4).scriptContextTxInfo.txInfoReferenceInputs )
     == (false, true, false, true)) = true := by native_decide

#print axioms published_dirCS_is_DIRCS
#print axioms exclusion_at_derived_dirCS
#print axioms no_row_refutes_H

#print axioms accept_class_inhabited_at_the_obligation_meter
#print axioms control_also_halts_at_the_obligation_meter
#print axioms datum_shape_sweep
#print axioms misplaced_nft_is_not_a_route
#print axioms addressing_overapproximation

end IndependentVerify
end WSC
