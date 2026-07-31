/-
WSC/Review/DesignProbe.lean — **ADVERSARIAL PROBE of the proposed repair of
`WSC.Benchmark.P1UnshapedForm`** (the `coveringNodeExists` / base-absent defect).

Nothing here is part of the deliverable; it exists so that the DESIGN's
load-bearing claims are settled by construction rather than by argument. Five
things are measured:

* §1 Fix A's reader (`dirNodeInterval`) and covering predicate
  (`coveringNodeExistsWalk`), plus the two kernel lemmas the design owes:
  the refinement `dirNodeFields ⟹ dirNodeInterval` and the strengthening
  `Walk = false ⟹ coveringNodeExists = false`.
* §2 **KILL CRITERION K2** — at all FOUR P1 shapes the two covering tests
  COINCIDE, by `rfl`, for all leaves. So the four published shaped theorems are
  untouched by the repair and the four §3 specialisations can discharge the
  strengthened hypothesis for free.
* §3 **KILL CRITERION K6** — the design records that it is UNMEASURED whether
  the hand TRANSCRIPTION (`Model.globalModel`) accepts the refuting witnesses,
  and therefore whether `WSC.Model.P1_model` is LITERALLY refuted. It is
  measured here: the transcription REJECTS all three (`ctxD`, `ctxF`, `ctxG`)
  while the compiled bytecode ACCEPTS them, so `P1_model` is NOT refuted by this
  witness family. The control (`ctxOk`) shows the transcription is not simply
  rejecting everything. NOTE the cause: the transcription reads a directory node
  through `Model.dirNodeAt`/`Model.dirNodeFields`, which demands a THIRD field on
  BOTH branches, so the model `perror`s where the bytecode's negative branch
  accepts. The model's blind spot and its rejection have the SAME root cause.
* §4 **KILL CRITERION K4** — Fix C's one new hypothesis (`paramsAuthAtIdx`) is
  inhabited at `ctxOk`. It is ALSO true at all three refuting witnesses, which is
  the design's central point measured rather than argued: the honest-deployment
  gate does NOT exclude them, only the repaired covering clause does.
* §5 the `hasCSH ⟹ hasCurrencySymbol` step of Fix C's pinning chain, proved at
  the Lean standard axiom set (no TS axiom) — the design's "easy direction".
-/
import WSC.Benchmark.BaseAbsentProbe
import WSC.Composition

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Review
namespace DesignProbe

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## §1 — Fix A, as proposed -/

def dirNodeInterval : Data → Option (CurrencySymbol × CurrencySymbol)
  | Data.List (Data.B k :: Data.B n :: _) => some (k, n)
  | _ => none

def coveringNodeExistsWalk (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeInterval d with
            | some (k, n) =>
                decide (k < cs) && decide (cs < n) &&
                  (Model.hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || coveringNodeExistsWalk dirCS cs rest

theorem dirNodeInterval_of_dirNodeFields {d : Data} {k n : CurrencySymbol} {tls : Data}
    (h : Model.dirNodeFields d = some (k, n, tls)) : dirNodeInterval d = some (k, n) := by
  unfold Model.dirNodeFields at h
  split at h
  · injection h with h; injection h with h1 h2; subst h1
    injection h2 with h3 _; subst h3
    rfl
  · exact Option.noConfusion h

/-- NOT CLOSED HERE. The design's second Fix-A lemma
(`coveringNodeExistsWalk … = false → Model.coveringNodeExists … = false`, i.e.
"the repaired clause is strictly STRONGER") is a routine list induction on top of
`dirNodeInterval_of_dirNodeFields` above; it is left to the implementer, so the
design's effort estimate for Fix A is credible but is NOT verified by this
module. Everything else the design leans on IS measured below. -/
theorem monotonicity_is_left_to_the_implementer : True := trivial

/-! ## §2 — K2: the two covering tests COINCIDE at every P1 shape (`rfl`) -/

theorem coveringWalk_eq_covering_T1R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    coveringNodeExistsWalk dirCS cs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs
      = Model.coveringNodeExists dirCS cs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs := rfl

theorem coveringWalk_eq_covering_T2R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    coveringNodeExistsWalk dirCS cs
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs
      = Model.coveringNodeExists dirCS cs
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs := rfl

theorem coveringWalk_eq_covering_T6R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    coveringNodeExistsWalk dirCS cs
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs
      = Model.coveringNodeExists dirCS cs
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs := rfl

theorem coveringWalk_eq_covering_T7R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    coveringNodeExistsWalk dirCS cs
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs
      = Model.coveringNodeExists dirCS cs
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs := rfl

/-! ## §3 — K6: does the TRANSCRIPTION accept the refuting witnesses? -/

/-- **NO.** `Model.globalModel` REJECTS all three witnesses the compiled bytecode
ACCEPTS, so `WSC.Model.P1_model` is not LITERALLY refuted by them. -/
theorem K6_transcription_rejects_all_three_witnesses :
    Model.globalModel (ByteString.mk "PARAMS") BaseAbsentProbe.ctxD = false
  ∧ Model.globalModel (ByteString.mk "PARAMS") BaseAbsentProbe.ctxF = false
  ∧ Model.globalModel (ByteString.mk "PARAMS") BaseAbsentProbe.ctxG = false := by
  native_decide

/-- The control: the transcription is not rejecting everything. -/
theorem K6_control_transcription_accepts_ctxOk :
    Model.globalModel (ByteString.mk "PARAMS") P1RShapedWitness.ctxOk = true := by
  native_decide

/-- …and `P1_model`'s OWN params clause (the ∀-scan `paramsPinned`, NOT the
benchmark's indexed read) HOLDS at all three witnesses and at `ctxOk`. So the
only thing standing between `P1_model` and the same refutation is the
transcription's own too-strict node read. -/
theorem K6_paramsPinned_holds_at_all_four :
    Model.paramsPinned (ByteString.mk "PARAMS") (ByteString.mk "DIRCS")
        (Credential.ScriptCredential (ByteString.mk "ABSENT"))
        BaseAbsentProbe.ctxD.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ Model.paramsPinned (ByteString.mk "PARAMS") (ByteString.mk "DIRCS")
        (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        BaseAbsentProbe.ctxF.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ Model.paramsPinned (ByteString.mk "PARAMS") (ByteString.mk "DIRCS")
        (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        BaseAbsentProbe.ctxG.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ Model.paramsPinned (ByteString.mk "PARAMS") (ByteString.mk "DIRCS")
        (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoReferenceInputs = true := by
  native_decide

/-! ## §4 — K4: Fix C's new hypothesis, and what it does NOT exclude -/

/-- The design's `paramsAuthAtIdx`: the reference input the redeemer's
`plgrParamsRefIdx` names passes the validator's `phasCSH` gate at `ppCS`. -/
def paramsAuthAtIdx (ppCS : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  match Benchmark.transferParamsRefIdx ctx.scriptContextRedeemer with
  | none => false
  | some idx =>
      match SeizeModel.headM
              (SeizeModel.dropL idx ctx.scriptContextTxInfo.txInfoReferenceInputs) with
      | none => false
      | some i => Model.hasCSH ppCS i.txInInfoResolved.txOutValue == some true

/-- INHABITED at `ctxOk` (so the honest corollary is not vacuous for want of the
gate) — and TRUE at all three refuting witnesses, i.e. the honest-deployment
framing does NOT exclude them. Only the repaired covering clause does. -/
theorem K4_gate_inhabited_and_does_not_exclude_the_witnesses :
    paramsAuthAtIdx (ByteString.mk "PARAMS") P1RShapedWitness.ctxOk = true
  ∧ paramsAuthAtIdx (ByteString.mk "PARAMS") BaseAbsentProbe.ctxD = true
  ∧ paramsAuthAtIdx (ByteString.mk "PARAMS") BaseAbsentProbe.ctxF = true
  ∧ paramsAuthAtIdx (ByteString.mk "PARAMS") BaseAbsentProbe.ctxG = true := by
  native_decide

/-! ## §5 — the pinning chain's first step -/

theorem hasCurrencySymbol_of_hasCSH (cs : CurrencySymbol) (v : CardanoLedgerApi.V1.Value)
    (h : Model.hasCSH cs v = some true) :
    CardanoLedgerApi.V1.hasCurrencySymbol cs v = true := by
  unfold Model.hasCSH at h
  split at h
  · exact Option.noConfusion h
  · next _ _ _ =>
      split at h
      · exact Option.noConfusion h
      · next q _ _ =>
          injection h with h
          have hq : q = cs := by simpa using h
          subst hq
          simp [CardanoLedgerApi.V1.hasCurrencySymbol]
      · exact Option.noConfusion h

#print axioms dirNodeInterval_of_dirNodeFields

#print axioms coveringWalk_eq_covering_T1R
#print axioms coveringWalk_eq_covering_T2R
#print axioms coveringWalk_eq_covering_T6R
#print axioms coveringWalk_eq_covering_T7R
#print axioms K6_transcription_rejects_all_three_witnesses
#print axioms K6_control_transcription_accepts_ctxOk
#print axioms K6_paramsPinned_holds_at_all_four
#print axioms K4_gate_inhabited_and_does_not_exclude_the_witnesses
#print axioms hasCurrencySymbol_of_hasCSH

end DesignProbe
end Review
end WSC
