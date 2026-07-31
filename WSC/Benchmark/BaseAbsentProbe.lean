/-
WSC/Benchmark/BaseAbsentProbe.lean — **THE REFUTATION ARTIFACT for the
`base-absent` hole of `WSC/Benchmark/P1UnshapedStatement.lean` §2.**

THE HOLE AS POSED. `P1UnshapedForm`'s params hypothesis PINS `base` to whatever
the transaction's own protocol-params datum publishes, so an adversary cannot
freely CHOOSE it — but nothing forces that published credential to be a
credential the transaction TOUCHES. Publish one that no input and no output
uses and `Model.outSum = Model.inSum = 0`, so the conclusion degenerates to
`0 ≥ Model.mintSigned cs tn`. With a POSITIVE mint that is `0 ≥ q > 0` — false.
The question is therefore exactly: **can the real compiled
`programmableLogicGlobal` ACCEPT such a transaction while every other hypothesis
of `P1UnshapedForm` holds?**

THE ANSWER IS YES, and §3's `ctxD` is the witness. Everything below is MEASURED
against the real compiled bytecode (`programmableLogicGlobal1600.script`,
`WSC/flats/programmableLogicGlobal.flat`) with a metered CEK run, never argued.

WHAT THE PRIOR EXPECTED, AND WHERE IT IS RIGHT. The expectation was that the
mint is ABSORBED into the expected value and then compared against outputs AT
THE PUBLISHED CREDENTIAL, so an absent credential gives `expected > 0` vs
`actual 0` and the validator REJECTS. §3's `ctxB` MEASURES exactly that: base
absent, `+4` mint, `Member` proof ⇒ the bytecode REJECTS. That half of the prior
is CONFIRMED, and it is why the naive attack does not work.

WHERE IT IS WRONG. `pcheckMintLogicAndGetProgrammableValue`
(ProgrammableLogicBase.hs:970-1020) has a SECOND arm. A `NonMember` proof DROPS
the minted policy from the expected value instead of absorbing it, at the price
of exhibiting a covering directory node (:986-1002) — and `P1UnshapedForm`'s
`Model.coveringNodeExists … = false` hypothesis is supposed to shut that door.
IT DOES NOT SHUT IT, because the two do not agree about what a directory node is:

* the validator's mint walk reads ONLY fields 0 (`key`) and 1 (`next`) of the
  node datum (:986-1002) — it never touches `transferLogicScript`. The TRANSFER
  walk's `pmatch` (:873-878) does NAME `ptransferLogicScript`, but its negative
  branch (:882-898) never forces it: §7's `ctxG` MEASURES the compiled code
  accepting a two-field node on that branch too;
* `Model.dirNodeFields` (`WSC/Model/GlobalModel.lean:318-320`) pattern-matches
  `Data.List (Data.B k :: Data.B n :: tls :: _)` — it demands a THIRD field,
  because it is written for the TRANSFER walk, which does read field 2.

So a reference input whose inline datum is the TWO-element `Data.List [B key,
B next]` is a perfectly good covering node to the mint walk and is INVISIBLE to
`Model.coveringNodeExists`. §3's `ctxD` is that transaction; §5's
`base_absent_refutes_P1UnshapedForm` is the machine-checked refutation, and §4's
negative controls show the covering interval and the directory-NFT
authentication are both genuinely being checked on that truncated node — i.e.
`ctxD` really does travel the `NonMember` arm and is not an accident.

SCOPE. §6 measures the same defect with the base PRESENT, so this is not
specific to base-absence: what base-absence buys is only the cleanest possible
failure, `0 ≥ 4`.

WHAT THIS IS AND IS NOT — READ BEFORE QUOTING IT.

* It IS a refutation of `P1UnshapedForm` as written, at the benchmark's own
  accept predicate. `¬ P1UnshapedForm acceptCEK` is a kernel-checked theorem
  below, with NO `sorryAx`. Handing the benchmark to the optimiser team in this
  state would ask them to prove a false goal.
* It is NOT a demonstrated on-chain exploit, and it is NOT a bytecode defect.
  Reachability needs a UTxO that carries the DIRECTORY NFT and whose inline
  datum is a two-field list. `WSC.DirWF` conjunct (iii) (`WSC/Honest.lean:1655`,
  via `dirNodeDatum`, :168-171, which decodes only the FIVE-field
  `DirectorySetNode`) says no such UTxO exists in the audited deployment, and
  `WSC.DIRWF` (:1685) assumes that of every on-chain transaction (discharge:
  U10, still open). `P1UnshapedForm` assumes NEITHER. So the defect is that the
  statement's registration hypothesis is too WEAK to stand in for the escape
  route the bytecode actually offers — the same category of error as the
  `cs ≠ ada` defect: a side condition the SHAPE supplied by construction and an
  arbitrary `ctx` does not.
* THE FOUR SHAPED THEOREMS ARE UNAFFECTED, for the same reason they survived the
  ada defect: `p1ShapedNode` (`WSC/Shaped/GlobalShapedP1.lean:233`) builds its
  datum as `IsData.toData (DirectorySetNode.mk …)`, five fields BY CONSTRUCTION,
  so at every P1 shape `Model.coveringNodeExists` and the bytecode's covering
  test agree. Only `key`/`next`/`nCS` are free there, and those are exactly what
  both sides read.

THE MINIMAL FIX is to state the hypothesis against what the MINT walk reads —
a covering test that requires only fields 0 and 1 of the node datum, i.e.
`Data.List (Data.B k :: Data.B n :: _)` in place of `Model.dirNodeFields`'
`Data.List (Data.B k :: Data.B n :: tls :: _)`. That predicate is TRUE on
strictly more contexts, so `= false` is a strictly STRONGER hypothesis, and it
is the faithful one. `Model.coveringNodeExists` is also a clause of the
published `WSC.Model.P1_model` (`WSC/Props/P1_Transfer.lean:363-376`), so the
same repair is owed there.
-/
import WSC.Benchmark.P1UnshapedStatement

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace BaseAbsentProbe

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC.Shape
open P1ShapedWitness (ppCS isHaltB isHaltB_sound)

/-! ## §1 — the context skeleton

SHAPE T2R (`WSC/Shaped/GlobalShapedR.lean:369`) at `P1RShapedWitness.ctxOk`'s
leaves, with the things the shape TIES TOGETHER split apart:

* `pub` — the credential the protocol-params datum PUBLISHES as `progLogicCred`.
  The shape passes `plc` here AND uses `plc` as the mini-ledger payment
  credential; that identification is exactly what §1 of
  `WSC/Benchmark/P1UnshapedStatement.lean` calls "supplied by construction of
  the shape", and it is the one the unshaped statement does NOT re-supply;
* `nodeCS`, `nodeDat` — the directory node's first non-ada policy and its inline
  datum, both raw, so a MALFORMED node can be presented;
* `red` — the redeemer, so the mint proof can be `Member` or `NonMember`;
* `q`, `qOut`, `qEsc` — the signed mint quantity and the two output quantities.

The mini-ledger input and output stay at `ScriptCredential "PROGLOGIC"` in every
scenario; only what the params datum PUBLISHES moves. -/

/-- The directory-node reference input, with its policy and its inline datum
free. At `nodeCS = "DIRCS"` and `nodeDat = nodeMMM` this is `p1ShapedNode`
(`WSC/Shaped/GlobalShapedP1.lean:233`) at `ctxOk`'s leaves. -/
def probeNode (nodeCS : ByteString) (d : Data) : TxInInfo :=
  ⟨⟨ByteString.mk "", 3⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "DIRNODE"), none⟩
   , txOutValue := adaPlusOne 100 nodeCS (ByteString.mk "NODETOK") 1
   , txOutDatum := .OutputDatum d
   , txOutReferenceScript := none }⟩

def probeCtxN (pub : ByteString) (nodeCS : ByteString) (nodeDat : Data) (red : Data)
    (q qOut qEsc : Integer) : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200
              (ByteString.mk "MMM") (ByteString.mk "TOK") 5
          , p1ShapedExtIn (ByteString.mk "EXT") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS")
              (ByteString.mk "PTOK") 100 1
              (ByteString.mk "DIRCS") pub (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          , probeNode nodeCS nodeDat ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 150
              (ByteString.mk "MMM") (ByteString.mk "TOK") qOut
          , p1ShapedEscOut (ByteString.mk "DEST") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") qEsc ]
      , txInfoFee := 50
      , txInfoMint := mintOne (ByteString.mk "MMM") (ByteString.mk "TOK") q
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [ByteString.mk "OWNER"]
      , txInfoRedeemers :=
          p1RMintRedeemers (ByteString.mk "MMM") (ByteString.mk "GLOBAL")
            (ByteString.mk "TLS") 77 99 88 red
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := red
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential (ByteString.mk "GLOBAL")) }

/-- The node carries the directory NFT, as every honest node does. -/
def probeCtx (pub : ByteString) (nodeDat : Data) (red : Data)
    (q qOut qEsc : Integer) : ScriptContext :=
  probeCtxN pub (ByteString.mk "DIRCS") nodeDat red q qOut qEsc

/-! ## §2 — the node datums and the two redeemers -/

/-- `ctxOk`'s node datum: keyed exactly `MMM`, all FIVE fields
(`WSC/Redeemer.lean:356-373`). -/
def nodeMMM : Data :=
  IsData.toData (DirectorySetNode.mk (ByteString.mk "MMM") (ByteString.mk "ZZZ")
    (.ScriptCredential (ByteString.mk "TLS")) (.ScriptCredential (ByteString.mk "ILS"))
    (ByteString.mk "GS"))

/-- A WELL-FORMED five-field node that strictly COVERS `MMM` (`AAA < MMM < ZZZ`).
`Model.coveringNodeExists` SEES this one. -/
def nodeCover : Data :=
  IsData.toData (DirectorySetNode.mk (ByteString.mk "AAA") (ByteString.mk "ZZZ")
    (.ScriptCredential (ByteString.mk "TLS")) (.ScriptCredential (ByteString.mk "ILS"))
    (ByteString.mk "GS"))

/-- **THE TRUNCATED NODE.** `key` and `next` only — the two fields the MINT walk
reads. `Model.dirNodeFields` needs a third and so returns `none`. -/
def nodeShort : Data :=
  Data.List [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ")]

/-- Truncated, but the interval does NOT cover `MMM` from below
(`key = "NNN" > "MMM"`). -/
def nodeShortHighKey : Data :=
  Data.List [Data.B (ByteString.mk "NNN"), Data.B (ByteString.mk "ZZZ")]

/-- Truncated, but the interval does NOT cover `MMM` from above
(`next = "BBB" < "MMM"`). -/
def nodeShortLowNext : Data :=
  Data.List [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "BBB")]

/-- THREE fields — the smallest datum `Model.dirNodeFields` accepts. Pins that
the model's blind spot is EXACTLY the arity. -/
def nodeThree : Data :=
  Data.List [Data.B (ByteString.mk "AAA"), Data.B (ByteString.mk "ZZZ"),
             Data.B (ByteString.mk "TLS")]

/-- `TransferAct [1] [1] [] [Member] 0` (`WSC/Shaped/GlobalShapedR.lean`). -/
def redMember : Data := p1ShapedRedeemerMint

/-- `TransferAct [1] [1] [] [NonMember 1] 0` — the mint proof points at
reference input 1, the directory node. -/
def redNonMember : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember 1] 0)

/-! ### ANCHOR — `probeCtx` really is SHAPE T2R and not a look-alike -/

/-- At `pub = plc`, `ctxOk`'s node and the `Member` redeemer, `probeCtx` is
`WSC.P1RShapedWitness.ctxBurn` ON THE NOSE — the published, bytecode-ACCEPTED
T2R burn witness. Definitional, no solver. -/
theorem probeCtx_is_ctxBurn :
    probeCtx (ByteString.mk "PROGLOGIC") nodeMMM redMember (-4) 1 4
      = P1RShapedWitness.ctxBurn := rfl

/-! ## §3 — THE FIVE SCENARIOS

Ledger balance is respected in all five: `5 + 4` of `MMM.TOK` enter, `q` is
minted, `qOut + qEsc = 9 + q` leave. -/

/-- **A — CONTROL, base PRESENT**, mint `+4`, `Member` proof, `qOut = 9`. -/
def ctxA : ScriptContext := probeCtx (ByteString.mk "PROGLOGIC") nodeMMM redMember 4 9 4

/-- **B — base ABSENT**, mint `+4`, `Member` proof. The prior's case. -/
def ctxB : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeMMM redMember 4 9 4

/-- **C — base ABSENT**, mint `+4`, `NonMember` proof at a WELL-FORMED covering
node. Accepted — but `Model.coveringNodeExists = true`, so `P1UnshapedForm`
excludes it. This is the hypothesis doing its job. -/
def ctxC : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeCover redNonMember 4 9 4

/-- **D — THE REFUTATION.** base ABSENT, mint `+4`, `NonMember` proof at the
TRUNCATED node. Accepted, and `Model.coveringNodeExists = false`. -/
def ctxD : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeShort redNonMember 4 9 4

/-- **E — base ABSENT, BURN.** `0 ≥ −4` holds, so this is NOT a refutation — but
it MEASURES that base-absence is not itself rejected. -/
def ctxE : ScriptContext := probeCtx (ByteString.mk "ABSENT") nodeMMM redMember (-4) 1 4

def absentCred : Credential := .ScriptCredential (ByteString.mk "ABSENT")
def plcCred : Credential := .ScriptCredential (ByteString.mk "PROGLOGIC")
def dirCS : CurrencySymbol := ByteString.mk "DIRCS"
def csMMM : CurrencySymbol := ByteString.mk "MMM"
def tnTOK : TokenName := ByteString.mk "TOK"

/-- `(validRewardingContext, coveringNodeExists, params-clause-holds, outSum,
inSum, mintSigned, halts-at-4400)`. -/
def report (ctx : ScriptContext) (base : Credential)
    : Bool × Bool × Bool × Integer × Integer × Integer × Bool :=
  let ti := ctx.scriptContextTxInfo
  ( validRewardingContext ctx
  , Model.coveringNodeExists dirCS csMMM ti.txInfoReferenceInputs
  , Benchmark.paramsPublishedBy ctx == some (dirCS, IsData.toData base)
  , Model.outSum base csMMM tnTOK ti.txInfoOutputs
  , Model.inSum base csMMM tnTOK ti.txInfoInputs
  , Model.mintSigned csMMM tnTOK ti.txInfoMint
  , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 4400) )

/-- **THE FIVE-POINT TABLE, MEASURED.**

| | published cred | mint | proof | node datum | cover | halts | conclusion |
|---|---|---|---|---|---|---|---|
| A | PROGLOGIC (present) | +4 | Member | 5-field | false | **true** | `9 ≥ 5+4` ✓ |
| B | ABSENT | +4 | Member | 5-field | false | **false** | vacuous |
| C | ABSENT | +4 | NonMember | 5-field covering | **true** | true | excluded by hyp. |
| D | ABSENT | +4 | NonMember | **2-field** | **false** | **true** | `0 ≥ 0+4` ✗ |
| E | ABSENT | −4 | Member | 5-field | false | true | `0 ≥ 0−4` ✓ | -/
theorem five_point_table :
    (report ctxA plcCred    == (true, false, true, 9, 5,  4, true))  = true
  ∧ (report ctxB absentCred == (true, false, true, 0, 0,  4, false)) = true
  ∧ (report ctxC absentCred == (true, true,  true, 0, 0,  4, true))  = true
  ∧ (report ctxD absentCred == (true, false, true, 0, 0,  4, true))  = true
  ∧ (report ctxE absentCred == (true, false, true, 0, 0, -4, true))  = true := by
  native_decide

/-! ## §4 — `ctxD` REALLY TRAVELS THE `NonMember` ARM

Three negative controls. Each changes ONE thing about the truncated node and
each makes the bytecode REJECT, so the acceptance in `ctxD` is the mint walk's
`NonMember` arm passing its three checks (:993-999) and not an accident of the
malformed datum being ignored. -/

/-- `key = "NNN"`, so `nodeKey #< currCS` fails. -/
def ctxD_highKey : ScriptContext :=
  probeCtx (ByteString.mk "ABSENT") nodeShortHighKey redNonMember 4 9 4

/-- `next = "BBB"`, so `currCS #< nodeNext` fails. -/
def ctxD_lowNext : ScriptContext :=
  probeCtx (ByteString.mk "ABSENT") nodeShortLowNext redNonMember 4 9 4

/-- The node does not carry the directory NFT, so `phasCSH` fails. -/
def ctxD_noNFT : ScriptContext :=
  probeCtxN (ByteString.mk "ABSENT") (ByteString.mk "NOTDIR") nodeShort redNonMember 4 9 4

/-- The truncated node passes the `NonMember` arm ONLY when it genuinely covers
`MMM` and genuinely carries the directory NFT. All three perturbations REJECT. -/
theorem nonmember_arm_is_really_checked :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_highKey) 4400) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_lowNext) 4400) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_noNFT) 4400) = false := by
  native_decide

/-- **THE REJECTIONS ARE `perror`s, NOT BUDGET EXHAUSTION.** Ten times the
budget — 44000 steps, 16× the most expensive P1 shape — changes nothing for
`ctxB` or for the three negative controls. Without this, "does not halt at 4400"
would be compatible with "needs 4401". -/
theorem rejections_are_errors_not_budget :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxB) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_highKey) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_lowNext) 44000) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_noNFT) 44000) = false := by
  native_decide

/-- **THE MODEL'S BLIND SPOT IS EXACTLY THE ARITY.** Same interval, same NFT,
one extra field: `Model.coveringNodeExists` flips to `true` and the hypothesis
closes again. So the defect is `Model.dirNodeFields`' third-field demand and
nothing else. -/
def ctxD_three : ScriptContext :=
  probeCtx (ByteString.mk "ABSENT") nodeThree redNonMember 4 9 4

theorem arity_is_the_whole_gap :
    Model.coveringNodeExists dirCS csMMM
        ctxD.scriptContextTxInfo.txInfoReferenceInputs = false
  ∧ Model.coveringNodeExists dirCS csMMM
        ctxD_three.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD_three) 4400) = true := by
  native_decide

/-- **TWO-SIDED COST PIN.** `ctxD` HALTS at 1528 steps and is budget-`Error` at
1527, so its `true` above is a genuine successful halt and not a meter artifact.
Two things worth recording: the refutation is CHEAPER than every accepting P1
shape (`ctxOk` = 2343, the family is [2288, 2777] —
`WSC.P1RShapedWitness.K_T1R_is_2343`), and 1528 < 1600, so it also fits inside
`WSC.appliedGlobal1600`'s budget. The control `ctxA` costs 2567 — the mint arm
that is NOT taken here is where the extra 1039 steps go. -/
theorem K_ctxD_is_1528 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD) 1528) = true
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD) 1527) = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxA) 2567) = true
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxA) 2566) = false := by
  native_decide

/-! ## §5 — THE REFUTATION

The accept predicate is the SAME term `WSC/Benchmark/P1UnshapedStatement.lean`
§4 uses to certify the benchmark NON-VACUOUS at 4400
(`P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600`), so this is an
apples-to-apples instantiation of `P1UnshapedForm`, not a different program. -/

def acceptCEK (ppCS' : CurrencySymbol) (ctx : ScriptContext) : Prop :=
  isSuccessful (PlutusCore.UPLC.CekMachine.cekExecuteProgram
    programmableLogicGlobal1600.script (globalInputs1600 ppCS' ctx) 4400)

/-- Every TRANSACTION-level hypothesis of `P1UnshapedForm` holds at `ctxD`. -/
theorem ctxD_satisfies_hypotheses :
    validRewardingContext ctxD = true
  ∧ Benchmark.paramsPublishedBy ctxD = some (dirCS, IsData.toData absentCred)
  ∧ Model.coveringNodeExists dirCS csMMM
      ctxD.scriptContextTxInfo.txInfoReferenceInputs = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxD) 4400) = true := by
  native_decide

/-- …and the ASSET hypothesis, the one `native_decide` cannot carry. -/
theorem ctxD_asset_is_not_ada : csMMM ≠ ByteString.mk "" := by decide

/-- …and the CONCLUSION FAILS: `0 ≥ 0 + 4`. -/
theorem ctxD_conclusion_fails :
    ¬ (Model.outSum absentCred csMMM tnTOK ctxD.scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum absentCred csMMM tnTOK ctxD.scriptContextTxInfo.txInfoInputs
          + Model.mintSigned csMMM tnTOK ctxD.scriptContextTxInfo.txInfoMint) := by
  native_decide

/-- **`P1UnshapedForm` IS FALSE at the benchmark's own accept predicate.** -/
theorem base_absent_refutes_P1UnshapedForm : ¬ Benchmark.P1UnshapedForm acceptCEK := by
  intro H
  exact ctxD_conclusion_fails
    (H ppCS ctxD absentCred dirCS csMMM tnTOK
      ctxD_asset_is_not_ada
      ctxD_satisfies_hypotheses.1
      ctxD_satisfies_hypotheses.2.1
      ctxD_satisfies_hypotheses.2.2.1
      (isHaltB_sound _ ctxD_satisfies_hypotheses.2.2.2))

/-! ## §6 — SCOPE: the defect is NOT specific to base-absence

Same truncated-node trick with the base PRESENT. A THIRD reference input carries
the truncated node (index 2); the transfer proof still points at the real
5-field node at index 1, so the transfer walk is undisturbed and the mini-ledger
input's 5 units are still required at the outputs. The mint's `+4` is dropped by
the `NonMember` proof at index 2, so `outSum = 5`, `inSum = 5`,
`mintSigned = 4` — and `5 ≥ 9` is false.

This matters for the FIX: repairing the params clause alone would not close the
hole. What is broken is `Model.coveringNodeExists`, which is ALSO a clause of
the published `WSC.Model.P1_model` (`WSC/Props/P1_Transfer.lean:363-376`). The
four SHAPED theorems are unaffected — their node datum is
`IsData.toData (DirectorySetNode.mk …)`, five fields BY CONSTRUCTION of the
shape, exactly as they got `cs ≠ ada` from their value skeleton. -/

def probeCtx3 (pub : ByteString) (nodeDat shortDat : Data) (red : Data)
    (q qOut qEsc : Integer) : ScriptContext :=
  let c := probeCtx pub nodeDat red q qOut qEsc
  let extra : TxInInfo :=
    ⟨⟨ByteString.mk "", 4⟩,
     { txOutAddress := ⟨.ScriptCredential (ByteString.mk "DIRNODE"), none⟩
     , txOutValue := adaPlusOne 100 (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 1
     , txOutDatum := .OutputDatum shortDat
     , txOutReferenceScript := none }⟩
  { c with
    scriptContextTxInfo :=
      { c.scriptContextTxInfo with
        txInfoReferenceInputs := c.scriptContextTxInfo.txInfoReferenceInputs ++ [extra] } }

/-- `TransferAct [1] [1] [] [NonMember 2] 0`. -/
def redNonMember2 : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.NonMember 2] 0)

/-- **F — base PRESENT, and P1 still fails.** -/
def ctxF : ScriptContext :=
  probeCtx3 (ByteString.mk "PROGLOGIC") nodeMMM nodeShort redNonMember2 4 5 8

theorem base_present_also_fails :
    report ctxF plcCred = (true, false, true, 5, 5, 4, true) := by native_decide

theorem ctxF_satisfies_hypotheses :
    validRewardingContext ctxF = true
  ∧ Benchmark.paramsPublishedBy ctxF = some (dirCS, IsData.toData plcCred)
  ∧ Model.coveringNodeExists dirCS csMMM
      ctxF.scriptContextTxInfo.txInfoReferenceInputs = false
  ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxF) 4400) = true := by
  native_decide

theorem ctxF_conclusion_fails :
    ¬ (Model.outSum plcCred csMMM tnTOK ctxF.scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum plcCred csMMM tnTOK ctxF.scriptContextTxInfo.txInfoInputs
          + Model.mintSigned csMMM tnTOK ctxF.scriptContextTxInfo.txInfoMint) := by
  native_decide

/-- …and the same instantiation refutes `P1UnshapedForm` with a PRESENT base. -/
theorem base_present_refutes_P1UnshapedForm : ¬ Benchmark.P1UnshapedForm acceptCEK := by
  intro H
  exact ctxF_conclusion_fails
    (H ppCS ctxF plcCred dirCS csMMM tnTOK
      ctxD_asset_is_not_ada
      ctxF_satisfies_hypotheses.1
      ctxF_satisfies_hypotheses.2.1
      ctxF_satisfies_hypotheses.2.2.1
      (isHaltB_sound _ ctxF_satisfies_hypotheses.2.2.2))

/-! ## §7 — THE PROPOSED FIX, AND WHETHER THE TRANSFER WALK NEEDS IT TOO

`coveringNodeExistsMint` is `Model.coveringNodeExists`
(`WSC/Props/P1_Transfer.lean:222-234`) with ONE character of difference: the
node-datum pattern demands only fields 0 and 1, which is exactly what the
bytecode's mint walk reads. It is TRUE wherever `Model.coveringNodeExists` is
(strictly more permissive), so `= false` is a strictly STRONGER hypothesis. -/

def coveringNodeExistsMint (dirCS' : CurrencySymbol) (cs : CurrencySymbol) :
    List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum (Data.List (Data.B k :: Data.B n :: _)) =>
           decide (k < cs) && decide (cs < n) &&
             (Model.hasCSH dirCS' i.txInInfoResolved.txOutValue == some true)
       | _ => false)
      || coveringNodeExistsMint dirCS' cs rest

/-- **THE FIX CLOSES BOTH WITNESSES.** On `ctxD` and on `ctxF` the strengthened
hypothesis is TRUE, so `= false` excludes them — while it still agrees with
`Model.coveringNodeExists` on the accepting control `ctxA`, i.e. the repair does
not make the statement vacuous at the transactions P1 is about. -/
theorem fix_excludes_the_witnesses :
    coveringNodeExistsMint dirCS csMMM ctxD.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ coveringNodeExistsMint dirCS csMMM ctxF.scriptContextTxInfo.txInfoReferenceInputs = true
  ∧ coveringNodeExistsMint dirCS csMMM ctxA.scriptContextTxInfo.txInfoReferenceInputs = false
  ∧ coveringNodeExistsMint dirCS csMMM
      P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoReferenceInputs = false := by
  native_decide

/-! ### Does the TRANSFER walk read field 2 of the node it exempts against?

`ctxG` points the TRANSFER proof (`transferProofs = [1]`) at the SAME truncated
covering node, with the base PRESENT and a `Member` mint proof. If the bytecode
accepts, the transfer walk's negative branch (:884-892) does not force
`transferLogicScript` either, and the truncation defeats BOTH walks — which is
why the fix above has to be applied to the hypothesis, not to a mint-only
side condition. Balance: `5 + 4` in, `+4` minted, `4 + 9` out. -/
def ctxG : ScriptContext := probeCtx (ByteString.mk "PROGLOGIC") nodeShort redMember 4 4 9

theorem transfer_walk_also_accepts_the_truncated_node :
    (report ctxG plcCred == (true, false, true, 4, 5, 4, true)) = true := by native_decide

#print axioms fix_excludes_the_witnesses
#print axioms transfer_walk_also_accepts_the_truncated_node
#print axioms five_point_table
#print axioms nonmember_arm_is_really_checked
#print axioms rejections_are_errors_not_budget
#print axioms arity_is_the_whole_gap
#print axioms K_ctxD_is_1528
#print axioms ctxD_satisfies_hypotheses
#print axioms ctxD_conclusion_fails
#print axioms base_absent_refutes_P1UnshapedForm
#print axioms ctxF_satisfies_hypotheses
#print axioms ctxF_conclusion_fails
#print axioms base_present_refutes_P1UnshapedForm

end BaseAbsentProbe
end WSC
