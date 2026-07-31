/-
WSC/Review/PpcsHole.lean — **HOLE 1 (`ppCS` adversary-choosable), settled BY
CONSTRUCTION against the real compiled bytecode.**

THE OBJECTION. `WSC.Benchmark.paramsPublishedBy`
(WSC/Benchmark/P1UnshapedStatement.lean:308-318) reads the reference input at the
redeemer's `plgrParamsRefIdx` and extracts `(directoryNodeCS, progLogicCred)`
WITHOUT the `phasCSH ppCS` authentication gate. The module's §1 (:298-307) and its
"Both readings are sound … because ACCEPT does the authenticating" paragraph
(:203-206) justify the omission by pointing at `pparamsAtRefIdx`
(ProgrammableLogicBase.hs:912-926, gate at :919). But `P1UnshapedForm` quantifies
`ppCS` UNIVERSALLY (:365), so an attacker may mint their own params NFT and
instantiate `ppCS` at their OWN policy — under which the gate passes on a params
UTxO the honest deployment would reject.

WHAT IS MEASURED HERE, all with a metered CEK run on the REAL
`programmableLogicGlobal` bytecode (`WSC/flats/programmableLogicGlobal.flat`,
wsc-poc `main` @ 2306678), never by argument:

§A  `accept` really does depend on `ppCS` — the honest witness `ctxOk` ERRORS
    when the program is applied to an attacker policy.
§B  the attacker deployment is REAL: the same transaction with the params NFT
    re-minted under the attacker's policy is ACCEPTED at `ppCS = "ATTACKER"` and
    ERRORS at `ppCS = "PARAMS"`. So the ∀ is inhabited off the honest `ppCS`;
    the objection's premise is CORRECT.
§C  the refutation attempt. Attacker publishes `progLogicCred = ScriptCredential
    "NOBODY"`, a credential the transaction never touches, and mints `+3` of a
    registered policy. Every hypothesis of `P1UnshapedForm` holds and the
    conclusion is FALSE (`0 ≥ 0 + 3`). The bytecode ERRORS.
§D  WHERE it dies. The identical context with the mint dropped is ACCEPTED, so
    the absent published base passes `pparamsAtRefIdx`, `pvalueFromCred` and the
    transfer walk; the ONLY difference in §C is the non-empty expected value, so
    the check that rejects is `poutputsContainExpectedValueAtCred`
    (ProgrammableLogicBase.hs:597-602, invoked at :1370-1374, trace
    "prog tokens escape"). §D's own conclusion is `0 ≥ 0 + 0` — true — so §D is
    not a refutation either.

VERDICT: NOT A REFUTATION. See the report for the prose defect that remains.
-/
import WSC.Benchmark.P1UnshapedStatement

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Review
namespace PpcsHole

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open WSC.Shape (mintOne range)
open WSC.Benchmark (paramsPublishedBy)

/-- `.Halt` — `WSC.P1ShapedWitness.isHaltB`, restated locally so this module has
both sides of the two-sided pin in one vocabulary. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

/-- `.Error` — the machine ERRORED, as opposed to running out of budget. This is
what makes every negative measurement below two-sided without a second, larger
budget run: `isHaltB = false ∧ isErrB = true` is "the validator rejected", not
"the meter ran out". -/
def isErrB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Error => true
  | _ => false

/-- The metered run: the UNSHAPED program and inputs the benchmark preps
(`WSC/Benchmark/P1UnshapedStatement.lean:963-968`), with only the meter changed. -/
def run (pp : CurrencySymbol) (ctx : ScriptContext) (k : Nat) :
    PlutusCore.UPLC.CekMachine.State :=
  PlutusCore.UPLC.CekMachine.cekExecuteProgram
    programmableLogicGlobal1600.script (globalInputs1600 pp ctx) k

/-- The HONEST deployment's params-NFT policy (`WSC.P1ShapedWitness.ppCS`). -/
def honestPP : CurrencySymbol := ByteString.mk "PARAMS"

/-- The ATTACKER's own params-NFT policy. -/
def atkPP : CurrencySymbol := ByteString.mk "ATTACKER"

/-! ## §A — `accept` DEPENDS ON `ppCS`

`ctxOk` (WSC/Props/Shaped/P1ShapedR.lean:582-595) is the library's accepting P1
witness; its params reference input carries the policy `"PARAMS"`. -/

/-- Halt at the honest policy, ERROR at the attacker's. The reject side is pinned
`.Error`, so it is the `phasCSH` gate firing (`pparamsAtRefIdx` :919, error at
:925), not the meter. -/
theorem A_ctxOk_accept_is_ppCS_dependent :
    isHaltB (run honestPP P1RShapedWitness.ctxOk 4400) = true
    ∧ isHaltB (run atkPP P1RShapedWitness.ctxOk 4400) = false
    ∧ isErrB (run atkPP P1RShapedWitness.ctxOk 4400) = true := by
  native_decide

/-! ## §B — THE ATTACKER DEPLOYMENT IS REAL

`ctxAtkNFT` is `ctxOk` with ONE leaf changed: the params reference input's own
non-ada policy, `pCS`, goes from `"PARAMS"` to `"ATTACKER"`. Everything else —
the published `(directoryNodeCS, progLogicCred) = ("DIRCS", ScriptCredential
"PROGLOGIC")`, the mini-ledger flows, the directory node, the withdrawal and
redeemer maps — is `ctxOk` verbatim. -/

def ctxAtkNFT : ScriptContext :=
  p1RShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 5
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "ATTACKER") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 88
    50

/-- The attacker's fake params UTxO is ACCEPTED at the attacker's own `ppCS` and
ERRORS at the honest one. Both hypotheses of `P1UnshapedForm` that the context
controls still hold, and — the point — the CONCLUSION HOLDS TOO (`5 ≥ 5 + 0`):
instantiating the ∀ at the attacker's deployment says something about the
ATTACKER's published base, not about the honest one. -/
theorem B_attacker_deployment_accepts :
    validRewardingContext ctxAtkNFT = true
    ∧ paramsPublishedBy ctxAtkNFT
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        ctxAtkNFT.scriptContextTxInfo.txInfoReferenceInputs = false
    ∧ isHaltB (run atkPP ctxAtkNFT 4400) = true
    ∧ isHaltB (run honestPP ctxAtkNFT 4400) = false
    ∧ isErrB (run honestPP ctxAtkNFT 4400) = true := by
  native_decide

/-- …and the conclusion of `P1UnshapedForm` at that instantiation: it HOLDS. -/
theorem B_conclusion_holds :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxAtkNFT.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxAtkNFT.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxAtkNFT.scriptContextTxInfo.txInfoMint = 0 := by
  native_decide

/-! ## §C / §D — THE REFUTATION ATTEMPT

The shapes tie the published `progLogicCred` to the mini-ledger address (both are
the leaf `plc`, `p1ShapedParamsIn` / `p1ShapedBaseIn`,
WSC/Shaped/GlobalShapedP1.lean:221-231 and :257-263). `P1UnshapedForm` quantifies
over an ARBITRARY `ScriptContext`, so the attacker is not bound by that: below,
the params reference input publishes `pub` while the mini-ledger sits at
`"PROGLOGIC"`.

Everything else is SHAPE T2R's witness `ctxBurn` re-cut to a POSITIVE mint:
inputs `5 + 4 = 9`, mint `+3`, outputs `8 + 4 = 12` (balanced, so
`CardanoLedgerApi.V3.isBalanced` :1774-1778 passes), ada `200 + 100 = 150 + 100 +
50`. -/

/-- One reference input, one free leaf: the credential the params datum
publishes. The NFT policy is the ATTACKER's throughout. -/
def atkParamsIn (pub : ByteString) : TxInInfo :=
  p1ShapedParamsIn (ByteString.mk "PANCHOR") (ByteString.mk "ATTACKER") (ByteString.mk "PTOK")
    100 1 (ByteString.mk "DIRCS") pub (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")

/-- SHAPE T2R with the published base DECOUPLED from the mini-ledger address and
the mint quantity free. `qOut` is the mini-ledger output quantity; balance forces
`qOut + 4 = 9 + qMint`. -/
def atkCtx (pub : ByteString) (qOut qMint : Integer) (redeemer : Data)
    (reds : CardanoLedgerApi.V3.RedeemerMap) (mint : CardanoLedgerApi.V3.MintValue)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200
              (ByteString.mk "MMM") (ByteString.mk "TOK") 5
          , p1ShapedExtIn (ByteString.mk "EXT") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoReferenceInputs :=
          [ atkParamsIn pub
          , p1ShapedNode (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS")
              (ByteString.mk "NODETOK") 100 1
              (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
              (ByteString.mk "ILS") (ByteString.mk "GS") ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 150
              (ByteString.mk "MMM") (ByteString.mk "TOK") qOut
          , p1ShapedEscOut (ByteString.mk "DEST") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoFee := 50
      , txInfoMint := mint
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [ByteString.mk "OWNER"]
      , txInfoRedeemers := reds
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := redeemer
  , scriptContextScriptInfo :=
      .RewardingScript (.ScriptCredential (ByteString.mk "GLOBAL")) }

/-- MINT variant, `+3` of `("MMM","TOK")`. Redeemer `TransferAct [1] [1] [] [Member] 0`
(`p1ShapedRedeemerMint`), redeemer map `p1RMintRedeemers`. -/
def atkMint (pub : ByteString) : ScriptContext :=
  atkCtx pub 8 3 p1ShapedRedeemerMint
    (p1RMintRedeemers (ByteString.mk "MMM") (ByteString.mk "GLOBAL") (ByteString.mk "TLS")
      77 99 88 p1ShapedRedeemerMint)
    (mintOne (ByteString.mk "MMM") (ByteString.mk "TOK") 3)

/-- NO-MINT variant, the §D control: same transaction, mint dropped, mini-ledger
output back to `5`. Redeemer `TransferAct [1] [1] [] [] 0` (`p1ShapedRedeemer`),
redeemer map `p1RRedeemers` (no `Minting` entry, since there is no mint). -/
def atkNoMint (pub : ByteString) : ScriptContext :=
  atkCtx pub 5 0 p1ShapedRedeemer
    (p1RRedeemers (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 77 88 p1ShapedRedeemer)
    []

/-- The absent published base: a script credential no input and no output of the
transaction carries. -/
def absent : ByteString := ByteString.mk "NOBODY"

/-! ### §C — every hypothesis holds, the conclusion FAILS, and the bytecode ERRORS -/

/-- **THE ATTEMPTED COUNTEREXAMPLE, and its hypotheses.** `atkMint absent`
satisfies `validRewardingContext`, publishes `("DIRCS", ScriptCredential
"NOBODY")` at the redeemer's `plgrParamsRefIdx`, and has no covering directory
node for `"MMM"`. The asset is `"MMM" ≠ ""`. -/
theorem C_hypotheses_hold :
    validRewardingContext (atkMint absent) = true
    ∧ paramsPublishedBy (atkMint absent)
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential absent))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        (atkMint absent).scriptContextTxInfo.txInfoReferenceInputs = false := by
  native_decide

/-- **THE CONCLUSION IS FALSE ON IT**: `0 ≥ 0 + 3`. -/
theorem C_conclusion_fails :
    Model.outSum (.ScriptCredential absent) (ByteString.mk "MMM")
        (ByteString.mk "TOK") (atkMint absent).scriptContextTxInfo.txInfoOutputs = 0
    ∧ Model.inSum (.ScriptCredential absent) (ByteString.mk "MMM")
        (ByteString.mk "TOK") (atkMint absent).scriptContextTxInfo.txInfoInputs = 0
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        (atkMint absent).scriptContextTxInfo.txInfoMint = 3 := by
  native_decide

/-- **AND THE BYTECODE REJECTS IT**, at the ATTACKER's own `ppCS` — the whole
point of the objection. Two-sided: `.Error`, not budget exhaustion. So the
attempted counterexample is NOT one: `accept` is false. -/
theorem C_bytecode_rejects :
    isHaltB (run atkPP (atkMint absent) 4400) = false
    ∧ isErrB (run atkPP (atkMint absent) 4400) = true := by
  native_decide

/-- The CONTROL that isolates the cause: the SAME transaction with the params
datum publishing the credential the mini-ledger actually uses is ACCEPTED at the
attacker's `ppCS`. So nothing incidental about `atkCtx` (the re-cut redeemer map,
the `+3` mint, the fake NFT) is what killed §C. -/
theorem C_control_present_base_accepts :
    isHaltB (run atkPP (atkMint (ByteString.mk "PROGLOGIC")) 4400) = true := by
  native_decide

/-! ### §D — LOCALISING THE KILL

Same absent base, mint dropped. If this ACCEPTS then `pparamsAtRefIdx`,
`pvalueFromCred` and `pcheckTransferLogicAndGetProgrammableValue` all survive an
absent `progLogicCred` (the transfer walk's outer `pelimList` is on the VALUE, so
the leftover proof `[1]` is ignored — ProgrammableLogicBase.hs:966-1036), and the
only thing §C adds is a non-empty `expectedProgrammableOutputValue`. That leaves
exactly one check as the cause: `poutputsContainExpectedValueAtCred` at :1370-1374. -/

/-- **THE ABSENT BASE ALONE IS NOT REJECTED.** And its own P1 conclusion is
`0 ≥ 0 + 0`, which HOLDS — so §D is an accepting context that satisfies every
hypothesis and does NOT refute the statement. -/
theorem D_absent_base_without_mint_accepts :
    validRewardingContext (atkNoMint absent) = true
    ∧ paramsPublishedBy (atkNoMint absent)
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential absent))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        (atkNoMint absent).scriptContextTxInfo.txInfoReferenceInputs = false
    ∧ isHaltB (run atkPP (atkNoMint absent) 4400) = true := by
  native_decide

/-- §D's quantities: `0 ≥ 0 + 0`. -/
theorem D_conclusion_holds :
    Model.outSum (.ScriptCredential absent) (ByteString.mk "MMM")
        (ByteString.mk "TOK") (atkNoMint absent).scriptContextTxInfo.txInfoOutputs = 0
    ∧ Model.inSum (.ScriptCredential absent) (ByteString.mk "MMM")
        (ByteString.mk "TOK") (atkNoMint absent).scriptContextTxInfo.txInfoInputs = 0
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        (atkNoMint absent).scriptContextTxInfo.txInfoMint = 0 := by
  native_decide

/-! ## §E — THE OTHER DIRECTION THE CONCLUSION CAN FAIL

§C makes `outSum < inSum + mintSigned` by inflating `mintSigned`. The
mint-independent way is to publish a base that HAS inputs and NO outputs, so
`0 = outSum < inSum`. That route does not touch the mint walk at all, so it tests
the containment check on its own.

`foreignIn` is a second mini-ledger-shaped input at `ScriptCredential "FOREIGN"`,
owner-witnessed by the same signatory (so `pvalueFromCred`'s fail-closed staking
gate — ProgrammableLogicBase.hs:428-431 — is SATISFIED rather than dodged), and
the params datum publishes `"FOREIGN"`. Balanced: in `5 + 4 = 9`, out `5 + 4 = 9`,
no mint. -/

def foreignIn (foreign : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.ScriptCredential foreign,
                      some (.StakingHash (.PubKeyCredential (ByteString.mk "OWNER")))⟩
   , txOutValue := Shape.adaPlusOne 100 (ByteString.mk "MMM") (ByteString.mk "TOK") 4
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

def atkForeignCtx (pub : ByteString) : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200
              (ByteString.mk "MMM") (ByteString.mk "TOK") 5
          , foreignIn (ByteString.mk "FOREIGN") ]
      , txInfoReferenceInputs :=
          [ atkParamsIn pub
          , p1ShapedNode (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS")
              (ByteString.mk "NODETOK") 100 1
              (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
              (ByteString.mk "ILS") (ByteString.mk "GS") ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 150
              (ByteString.mk "MMM") (ByteString.mk "TOK") 5
          , p1ShapedEscOut (ByteString.mk "DEST") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoFee := 50
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [ByteString.mk "OWNER"]
      , txInfoRedeemers :=
          [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I 77)
          , (.Spending ⟨ByteString.mk "", 1⟩, Data.I 78)
          , (.Rewarding (.ScriptCredential (ByteString.mk "GLOBAL")), p1ShapedRedeemer)
          , (.Rewarding (.ScriptCredential (ByteString.mk "TLS")), Data.I 88) ]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo :=
      .RewardingScript (.ScriptCredential (ByteString.mk "GLOBAL")) }

/-- Hypotheses hold; the conclusion is `0 ≥ 4`, FALSE; the bytecode ERRORS at the
attacker's own `ppCS`. Two-sided (`.Error`, not budget). -/
theorem E_inputs_only_base_rejected :
    validRewardingContext (atkForeignCtx (ByteString.mk "FOREIGN")) = true
    ∧ paramsPublishedBy (atkForeignCtx (ByteString.mk "FOREIGN"))
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential (ByteString.mk "FOREIGN")))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        (atkForeignCtx (ByteString.mk "FOREIGN")).scriptContextTxInfo.txInfoReferenceInputs
          = false
    ∧ Model.outSum (.ScriptCredential (ByteString.mk "FOREIGN")) (ByteString.mk "MMM")
        (ByteString.mk "TOK")
        (atkForeignCtx (ByteString.mk "FOREIGN")).scriptContextTxInfo.txInfoOutputs = 0
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "FOREIGN")) (ByteString.mk "MMM")
        (ByteString.mk "TOK")
        (atkForeignCtx (ByteString.mk "FOREIGN")).scriptContextTxInfo.txInfoInputs = 4
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        (atkForeignCtx (ByteString.mk "FOREIGN")).scriptContextTxInfo.txInfoMint = 0
    ∧ isHaltB (run atkPP (atkForeignCtx (ByteString.mk "FOREIGN")) 4400) = false
    ∧ isErrB (run atkPP (atkForeignCtx (ByteString.mk "FOREIGN")) 4400) = true := by
  native_decide

/-- The control: same transaction, params datum publishing the credential the
mini-ledger really uses. ACCEPTED. So §E's rejection is the published base, not
the extra script input or the widened redeemer map. -/
theorem E_control_accepts :
    isHaltB (run atkPP (atkForeignCtx (ByteString.mk "PROGLOGIC")) 4400) = true := by
  native_decide

/-! ## §F — WHAT THE HONEST DEPLOYMENT ACTUALLY FACES

§B/§C instantiate the ∀ at the ATTACKER's `ppCS`. The transaction an attacker can
really submit against the DEPLOYED validator is different: `ppCS` is baked into
the applied script, so the attacker must get the HONEST program to read a fake
params UTxO. `ctxTwoParams` is exactly that attempt — the honest params UTxO at
reference index 0, the attacker's at index 1 publishing `ScriptCredential
"NOBODY"`, the directory node pushed to index 2, and the redeemer's
`plgrParamsRefIdx` set to **1** (`TransferAct [2] [1] [] [Member] 1`).

`paramsPublishedBy` reads the ATTACKER's entry (it has no authentication gate),
so the hypothesis names `"NOBODY"` and the conclusion is again `0 ≥ 0 + 3`,
FALSE. The measurement below is that the HONEST program ERRORS on it. -/

def twoParamsRedeemer : Data :=
  IsData.toData (PLGRedeemer.TransferAct [2] [1] [] [MintProof.Member] 1)

/-- `p1ShapedParamsIn` with the `TxOutRef` index free: `validReferenceInputs`
(CardanoLedgerApi/V3/Contexts.lean) needs the reference inputs STRICTLY ascending
in `TxOutRef`, and this context carries two params UTxOs. -/
def paramsInAt (ref : Integer) (pCS pub : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", ref⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PANCHOR"), none⟩
   , txOutValue := Shape.adaPlusOne 100 pCS (ByteString.mk "PTOK") 1
   , txOutDatum := .OutputDatum
       (IsData.toData
         (GlobalParams.mk (ByteString.mk "DIRCS") (.ScriptCredential pub)
            (.ScriptCredential (ByteString.mk "GLOBAL"))
            (.ScriptCredential (ByteString.mk "SEIZE"))))
   , txOutReferenceScript := none }⟩

def ctxTwoParams : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200
              (ByteString.mk "MMM") (ByteString.mk "TOK") 5
          , p1ShapedExtIn (ByteString.mk "EXT") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoReferenceInputs :=
          [ paramsInAt 1 (ByteString.mk "PARAMS") (ByteString.mk "PROGLOGIC")
          , paramsInAt 2 (ByteString.mk "ATTACKER") absent
          , p1ShapedNode (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS")
              (ByteString.mk "NODETOK") 100 1
              (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
              (ByteString.mk "ILS") (ByteString.mk "GS") ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 150
              (ByteString.mk "MMM") (ByteString.mk "TOK") 8
          , p1ShapedEscOut (ByteString.mk "DEST") 100
              (ByteString.mk "MMM") (ByteString.mk "TOK") 4 ]
      , txInfoFee := 50
      , txInfoMint := mintOne (ByteString.mk "MMM") (ByteString.mk "TOK") 3
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [ByteString.mk "OWNER"]
      , txInfoRedeemers :=
          p1RMintRedeemers (ByteString.mk "MMM") (ByteString.mk "GLOBAL")
            (ByteString.mk "TLS") 77 99 88 twoParamsRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := twoParamsRedeemer
  , scriptContextScriptInfo :=
      .RewardingScript (.ScriptCredential (ByteString.mk "GLOBAL")) }

/-- **THE HONEST DEPLOYMENT REJECTS THE FAKE-PARAMS REDIRECT.** The hypothesis
`paramsPublishedBy` names the ATTACKER's pair and the conclusion fails
(`0 ≥ 0 + 3`), but the HONEST program errors — so the honest `accept` is false
and the honest instance of `P1UnshapedForm` is not refuted by this context
either. `phasCSH` (ProgrammableLogicBase.hs:838-841) reads the second entry of
the params UTxO's value, and the attacker's carries `"ATTACKER"` there, so the
honest `ppCS` cannot authenticate it. -/
theorem F_honest_program_rejects_fake_params_redirect :
    validRewardingContext ctxTwoParams = true
    ∧ paramsPublishedBy ctxTwoParams
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential absent))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        ctxTwoParams.scriptContextTxInfo.txInfoReferenceInputs = false
    ∧ Model.outSum (.ScriptCredential absent) (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxTwoParams.scriptContextTxInfo.txInfoOutputs = 0
    ∧ Model.inSum (.ScriptCredential absent) (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxTwoParams.scriptContextTxInfo.txInfoInputs = 0
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxTwoParams.scriptContextTxInfo.txInfoMint = 3
    ∧ isHaltB (run honestPP ctxTwoParams 4400) = false
    ∧ isErrB (run honestPP ctxTwoParams 4400) = true := by
  native_decide

#print axioms WSC.Review.PpcsHole.A_ctxOk_accept_is_ppCS_dependent
#print axioms WSC.Review.PpcsHole.B_attacker_deployment_accepts
#print axioms WSC.Review.PpcsHole.C_hypotheses_hold
#print axioms WSC.Review.PpcsHole.C_conclusion_fails
#print axioms WSC.Review.PpcsHole.C_bytecode_rejects
#print axioms WSC.Review.PpcsHole.C_control_present_base_accepts
#print axioms WSC.Review.PpcsHole.D_absent_base_without_mint_accepts
#print axioms WSC.Review.PpcsHole.E_inputs_only_base_rejected
#print axioms WSC.Review.PpcsHole.E_control_accepts
#print axioms WSC.Review.PpcsHole.F_honest_program_rejects_fake_params_redirect

end PpcsHole
end Review
end WSC
