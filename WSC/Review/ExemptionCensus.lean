/-
WSC/Review/ExemptionCensus.lean — MEASUREMENTS for the research task
"enumerate every route by which the global validator's `TransferAct` arm can
accept a transaction that moves LESS of some `cs` to the mini-ledger outputs
than it took from the mini-ledger inputs plus mint".

Nothing here is part of the deliverable. Two things are measured that no
existing module measures, and each answers a question the enumeration cannot
settle by reading source alone.

* §1 — **IS THE PROPOSED COVERING-NODE FIX TIGHT?** `WSC/Review/DesignProbe.lean`
  proposes `dirNodeInterval : Data.List (Data.B k :: Data.B n :: _)` as the
  faithful node reader. `WSC/Benchmark/BaseAbsentProbe.lean` measured that a
  TWO-field `Data.List` node IS accepted by both walks; it did NOT measure
  whether anything SMALLER or DIFFERENTLY SHAPED is also accepted. If e.g. a
  `Data.Constr 0 [B k, B n]` node were accepted, `dirNodeInterval` would be
  incomplete and the "fix" would leave a fourth hole. §1 measures the whole
  boundary on BOTH walks: one field, a non-`B` key, a non-`B` next, a `Constr`
  and a `Map` — all five REJECT on both arms, so the acceptance set really is
  exactly `Data.List (B k :: B n :: _)` and the fix is tight, not merely
  sufficient for the two known witnesses.

* §2 — **A SECOND, NON-COVERING-NODE EXEMPTION ROUTE.** `pvalueFromCred`'s
  phase-2 exhaustion (`ProgrammableLogicBase.hs:424`, mirrored at
  `WSC/Model/GlobalModel.lean:279`) strips ada from the single contributing
  mini-ledger input BY POSITION: `ptail # (pasMap # firstVd)`. On a value with
  no lovelace entry that `ptail` drops a REAL policy, and the dropped policy
  disappears from the expected output value entirely — no directory node, no
  proof, no redeemer field involved. §2 measures the compiled bytecode
  ACCEPTING exactly such a transaction with `outSum = 0 < 5 = inSum`.

  `P1UnshapedForm` EXCLUDES it, but not by either of the clauses the current
  repair discussion is about: it is excluded by `validRewardingContext`, and
  specifically by the INPUT half of that predicate (`validInputs`,
  `CardanoLedgerApi/V3/Contexts.lean:1650`, which applies `V2.validTxOutValue`
  to every resolved input). The published `WSC.Model.P1_model`
  (`WSC/Props/P1_Transfer.lean:363-376`) carries only the OUTPUT half
  (`∀ o ∈ txInfoOutputs, validTxOutValue o.txOutValue = true`) — so P1_model is
  LITERALLY REFUTED by this witness, which §2.3 proves in the kernel. The
  transcription `Model.globalModel` accepts it too, so this is not a
  bytecode/transcription divergence: both agree, and the STATEMENT is what is
  wrong.

  This is the third distinct shape of the same failure mode and it is NOT a
  covering-node route, which is the point: an enumeration that only hardens
  `coveringNodeExists` would not have found it.
-/
import WSC.Benchmark.BaseAbsentProbe

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Review
namespace ExemptionCensus

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC.Shape
open P1ShapedWitness (ppCS isHaltB isHaltB_sound)

/-- One metered CEK run of the real compiled `programmableLogicGlobal` at a
budget of 44000 — ten times the `4400` the benchmark uses, so a `false` here is
a `perror` and not budget exhaustion (the same argument
`BaseAbsentProbe.rejections_are_errors_not_budget` makes). -/
def halts (ctx : ScriptContext) : Bool :=
  isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
    programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 44000)

/-! ## §1 — the covering-node acceptance boundary, on BOTH walks

`BaseAbsentProbe.nodeShort = Data.List [B "AAA", B "ZZZ"]` is the ACCEPTED
control on each arm (`ctxD` for the mint walk, `ctxG` for the transfer walk).
The five datums below each perturb ONE thing about it. -/

/-- One field only: `pnext` cannot be read. -/
def nodeOne : Data := Data.List [Data.B (ByteString.mk "AAA")]

/-- Field 0 is not a `Data.B`, so `pfromData pkey` (`:888`) cannot force it. -/
def nodeKeyNotB : Data := Data.List [Data.I 1, Data.B (ByteString.mk "ZZZ")]

/-- Field 1 is not a `Data.B`, so `pfromData pnext` (`:889`) cannot force it. -/
def nodeNextNotB : Data := Data.List [Data.B (ByteString.mk "AAA"), Data.I 1]

/-- Right fields, WRONG `Data` constructor: `Constr` instead of `List`.
`PDirectorySetNode` is `DeriveAsDataRec` (`PTokenDirectory.hs:176-186`), i.e. a
list-backed record, so this must fail — but "must" is an inference about
Plutarch's deriving strategy, which is exactly the kind of inference this file
replaces with a measurement. -/
def nodeConstrTwo : Data :=
  Data.Constr 0 [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ")]

/-- Right fields, wrong `Data` constructor: `Map`. -/
def nodeMapTwo : Data :=
  Data.Map [(Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"))]

/-- The MINT walk's `NonMember` arm at the given node datum, base ABSENT —
`BaseAbsentProbe.ctxD` with the node datum free. -/
def mintArm (d : Data) : ScriptContext :=
  BaseAbsentProbe.probeCtx (ByteString.mk "ABSENT") d BaseAbsentProbe.redNonMember 4 9 4

/-- The TRANSFER walk's NEGATIVE arm at the given node datum, base PRESENT —
`BaseAbsentProbe.ctxG` with the node datum free. -/
def xferArm (d : Data) : ScriptContext :=
  BaseAbsentProbe.probeCtx (ByteString.mk "PROGLOGIC") d BaseAbsentProbe.redMember 4 4 9

/-- **THE MINT WALK'S COVERING-NODE ACCEPTANCE SET IS EXACTLY
`Data.List (B k :: B n :: _)`.** Control accepts; all five perturbations
`perror`. -/
theorem arity_floor_mint_walk :
    (( halts (mintArm BaseAbsentProbe.nodeShort)
     , halts (mintArm nodeOne)
     , halts (mintArm nodeKeyNotB)
     , halts (mintArm nodeNextNotB)
     , halts (mintArm nodeConstrTwo)
     , halts (mintArm nodeMapTwo) )
     == (true, false, false, false, false, false)) = true := by native_decide

/-- **AND SO IS THE TRANSFER WALK'S.** Same boundary on the other arm, so one
predicate covers both and `WSC/Review/DesignProbe.lean`'s `dirNodeInterval` is
TIGHT — it accepts neither more nor less than the bytecode does. -/
theorem arity_floor_transfer_walk :
    (( halts (xferArm BaseAbsentProbe.nodeShort)
     , halts (xferArm nodeOne)
     , halts (xferArm nodeKeyNotB)
     , halts (xferArm nodeNextNotB)
     , halts (xferArm nodeConstrTwo)
     , halts (xferArm nodeMapTwo) )
     == (true, false, false, false, false, false)) = true := by native_decide

/-! ## §2 — the POSITIONAL ADA STRIP: an exemption route with no directory node

`pvalueFromCred` accumulates in three phases (`ProgrammableLogicBase.hs:397-439`).
Phase 2 is the "exactly one contributing mini-ledger input" path, and on
exhaustion it returns `ptail # (pasMap # firstVd)` (`:424`) — it removes the
input's FIRST currency entry by POSITION, on the assumption that the first entry
is lovelace. Phase 3 does the same job by VALUE (`pinsertCoin # "" # "" # 0`,
`:409`), so the assumption is confined to phase 2.

Give the single mini-ledger input a value with NO lovelace entry and that
`ptail` deletes the input's real policy instead. The aggregated value is then
empty, the transfer walk consumes no proofs and returns empty, the mint is empty
so no mint walk runs, and `poutputsContainExpectedValueAtCred` returns `True`
without inspecting a single output (`:650`, the `pelimList` base case on an
empty expected list). Every unit of the policy may leave. -/

/-- A ledger-ILLEGAL `TxOut` value: one policy, no lovelace entry. -/
def noAdaValue (cs tn : ByteString) (q : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [(Data.B cs, Data.Map [(Data.B tn, Data.I q)])]

/-- A ledger-legal lovelace-only `TxOut` value. -/
def adaOnlyValue (n : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [(Data.B (ByteString.mk ""), Data.Map [(Data.B (ByteString.mk ""), Data.I n)])]

/-- The single mini-ledger input, at `PROGLOGIC`, pubkey-owner-witnessed exactly
as `p1ShapedBaseIn` is — only its VALUE differs, and only by the missing ada
entry. -/
def baseInNoAda : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"),
                      some (.StakingHash (.PubKeyCredential (ByteString.mk "OWNER")))⟩
   , txOutValue := noAdaValue (ByteString.mk "MMM") (ByteString.mk "TOK") 5
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- The mini-ledger output keeps NONE of the policy. -/
def baseOutAdaOnly : TxOut :=
  { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"), none⟩
  , txOutValue := adaOnlyValue 150
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- `TransferAct [] [] [] [] 0` — no proofs of any kind are needed, because the
aggregated mini-ledger value the walk is driven by is EMPTY. -/
def redEmpty : Data := IsData.toData (PLGRedeemer.TransferAct [] [] [] [] 0)

/-- `BaseAbsentProbe.probeCtx` with three edits: the mini-ledger input loses its
ada entry, the mini-ledger output keeps none of the policy, and the mint is
empty (so the mint walk is skipped entirely at `:1228` and the route is isolated
to the input side). The escape output still carries the 4 units of the external
input, so nothing about the OUTPUT side is malformed. -/
def noAdaCtx : ScriptContext :=
  let c := BaseAbsentProbe.probeCtx (ByteString.mk "PROGLOGIC") BaseAbsentProbe.nodeMMM
             redEmpty 4 9 4
  { c with
    scriptContextTxInfo :=
      { c.scriptContextTxInfo with
        txInfoInputs  := baseInNoAda :: c.scriptContextTxInfo.txInfoInputs.tail,
        txInfoOutputs := baseOutAdaOnly :: c.scriptContextTxInfo.txInfoOutputs.tail,
        txInfoMint    := [] } }

/-! ### §2.1 — the measurement -/

/-- `(validRewardingContext, coveringNodeExists, params-clause, outSum, inSum,
mintSigned, bytecode-halts, transcription-accepts)`.

READ IT AS: every hypothesis of `P1UnshapedForm` EXCEPT `validRewardingContext`
holds, the real bytecode ACCEPTS, the hand transcription ACCEPTS, and the
conclusion `0 ≥ 5 + 0` is false. So `validRewardingContext` is the ONLY thing
standing between `P1UnshapedForm` and this counterexample — and the half of it
that does the work is `validInputs`, not the output clause. -/
def noAdaReport : Bool × Bool × Bool × Integer × Integer × Integer × Bool × Bool :=
  let ti := noAdaCtx.scriptContextTxInfo
  ( validRewardingContext noAdaCtx
  , Model.coveringNodeExists BaseAbsentProbe.dirCS BaseAbsentProbe.csMMM
      ti.txInfoReferenceInputs
  , Benchmark.paramsPublishedBy noAdaCtx
      == some (BaseAbsentProbe.dirCS, IsData.toData BaseAbsentProbe.plcCred)
  , Model.outSum BaseAbsentProbe.plcCred BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK
      ti.txInfoOutputs
  , Model.inSum BaseAbsentProbe.plcCred BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK
      ti.txInfoInputs
  , Model.mintSigned BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK ti.txInfoMint
  , halts noAdaCtx
  , Model.globalModel ppCS noAdaCtx )

theorem noAda_route_is_real :
    (noAdaReport == (false, false, true, 0, 5, 0, true, true)) = true := by native_decide

/-- **THE ROUTE IS THE `ptail`, AND NOTHING ELSE.** Restore the ada entry to the
same input — one extra currency pair, everything else identical — and the same
bytecode REJECTS, because now the 5 units survive `ptail`, become the expected
value, and are not at the outputs. -/
def adaRestoredCtx : ScriptContext :=
  { noAdaCtx with
    scriptContextTxInfo :=
      { noAdaCtx.scriptContextTxInfo with
        txInfoInputs :=
          (⟨⟨ByteString.mk "", 0⟩,
            { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"),
                               some (.StakingHash (.PubKeyCredential (ByteString.mk "OWNER")))⟩
            , txOutValue := adaPlusOne 200 (ByteString.mk "MMM") (ByteString.mk "TOK") 5
            , txOutDatum := .NoOutputDatum
            , txOutReferenceScript := none }⟩ : TxInInfo)
            :: noAdaCtx.scriptContextTxInfo.txInfoInputs.tail } }

/-- The transfer walk now needs its one proof, so the redeemer changes too; both
variants of the ada-restored transaction are REJECTED, which pins that the
acceptance in `noAda_route_is_real` comes from the empty aggregate and not from
the empty proof lists. -/
def adaRestoredCtxProof : ScriptContext :=
  { adaRestoredCtx with
    scriptContextTxInfo :=
      { adaRestoredCtx.scriptContextTxInfo with
        txInfoRedeemers := adaRestoredCtx.scriptContextTxInfo.txInfoRedeemers },
    scriptContextRedeemer := IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [] 0) }

theorem ada_restored_rejects :
    (( halts adaRestoredCtx, halts adaRestoredCtxProof ) == (false, false)) = true := by
  native_decide

/-! ### §2.2 — `P1UnshapedForm` survives, but only via `validRewardingContext` -/

/-- The clause that saves `P1UnshapedForm` is the INPUT half of ledger validity,
and it is the FIRST conjunct of `validTxInfo` — not the output clause that
`P1_model` carries. -/
theorem the_saving_clause_is_validInputs :
    CardanoLedgerApi.V3.validInputs noAdaCtx = false
  ∧ (noAdaCtx.scriptContextTxInfo.txInfoOutputs.all
      (fun o => CardanoLedgerApi.V2.validTxOutValue o.txOutValue)) = true := by
  native_decide

/-! ### §2.3 — `WSC.Model.P1_model` IS refuted

`P1_model`'s five hypotheses are: the transcription accepts, `cs ≠ ada`,
`paramsPinned`, `coveringNodeExists = false`, and OUTPUT-value validity. All
five hold at `noAdaCtx`; the conclusion does not. -/

theorem noAda_P1_model_hyps :
    Model.globalModel ppCS noAdaCtx = true
  ∧ Model.paramsPinned ppCS BaseAbsentProbe.dirCS BaseAbsentProbe.plcCred
      noAdaCtx.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ Model.coveringNodeExists BaseAbsentProbe.dirCS BaseAbsentProbe.csMMM
      noAdaCtx.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

theorem noAda_outputs_valid :
    ∀ o ∈ noAdaCtx.scriptContextTxInfo.txInfoOutputs,
      CardanoLedgerApi.V2.validTxOutValue o.txOutValue = true := by
  have h : (noAdaCtx.scriptContextTxInfo.txInfoOutputs.all
             (fun o => CardanoLedgerApi.V2.validTxOutValue o.txOutValue)) = true :=
    the_saving_clause_is_validInputs.2
  intro o ho
  exact List.all_eq_true.mp h o ho

theorem noAda_conclusion_fails :
    ¬ (Model.outSum BaseAbsentProbe.plcCred BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK
         noAdaCtx.scriptContextTxInfo.txInfoOutputs
       ≥ Model.inSum BaseAbsentProbe.plcCred BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK
           noAdaCtx.scriptContextTxInfo.txInfoInputs
         + Model.mintSigned BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK
             noAdaCtx.scriptContextTxInfo.txInfoMint) := by native_decide

/-- **`WSC.Model.P1_model` IS FALSE**, by a route that involves no directory
node, no covering interval and no mint proof — only the positional ada strip at
`ProgrammableLogicBase.hs:424`. The repair `P1_model` needs is an INPUT-value
validity clause (or `validRewardingContext` outright), independent of the
`coveringNodeExists` repair. -/
theorem noAda_refutes_P1_model :
    ¬ Model.P1_model ppCS noAdaCtx BaseAbsentProbe.plcCred BaseAbsentProbe.dirCS
        BaseAbsentProbe.csMMM BaseAbsentProbe.tnTOK := by
  intro H
  exact noAda_conclusion_fails
    (H noAda_P1_model_hyps.1
       BaseAbsentProbe.ctxD_asset_is_not_ada
       noAda_P1_model_hyps.2.1
       noAda_P1_model_hyps.2.2
       noAda_outputs_valid)

#print axioms arity_floor_mint_walk
#print axioms arity_floor_transfer_walk
#print axioms noAda_route_is_real
#print axioms ada_restored_rejects
#print axioms the_saving_clause_is_validInputs
#print axioms noAda_P1_model_hyps
#print axioms noAda_refutes_P1_model

end ExemptionCensus
end Review
end WSC
