-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedIdx.lean — SHAPE G2 = SHAPE G1 with BOTH redeemer index
fields loosened to symbolic integers (task Z2, loosening rung).

SHAPE G1 fixes `paramsRefIdx = 0` and the `NonMember` node index `= 1`. SHAPE G2
frees both, so neither `pdropList` in `pparamsAtRefIdx`
(ProgrammableLogicBase.hs:830) nor the one in the mint walk's `PNonMember` branch
(:998) can be reduced at prep time. The postcondition proved against this prep is
correspondingly INDEX-FREE: `hasCoveringNode` (WSC/Props/P5_NonMember.lean:266),
which is ADDENDUM E3's ∃-form written as a decidable walk over the reference
inputs.

Everything else is byte-identical to SHAPE G1; read that module's header for the
full FIXED / SYMBOLIC split, including the fact that `nCS ≠ dirCS` and
`pCS ≠ ppCS` as variables, so no part of the postcondition is true by
construction.
-/
import WSC.Shaped.GlobalShaped
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE G2's redeemer: `TransferAct [] [] [] [NonMember nIdx] pIdx` with BOTH
indices symbolic. **PR #112: FIVE fields**, `ownerWdrlIdxs` third and `[]` for the
same reason as SHAPE G1 (pubkey-credential input, never reaches the script-owner
branch — see WSC/Shaped/GlobalShaped.lean's `globalShapedRedeemer`). -/
def globalShapedRedeemerIdx (pIdx nIdx : Integer) : Data :=
  IsData.toData (PLGRedeemer.TransferAct [] [] [] [MintProof.NonMember nIdx] pIdx)

/-- **SHAPE G2** — SHAPE G1 with symbolic redeemer indices. -/
def globalShapedCtxIdx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (pIdx nIdx : Integer)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaOnly inAda
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  let produced : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential dest, none⟩
    , txOutValue := adaPlusOne outAda cs tn qOut
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨⟨ByteString.mk "", 0⟩, resolved⟩]
      , txInfoReferenceInputs :=
          [ globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := [produced]
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := globalShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers :=
          [(.Rewarding (.ScriptCredential w0), globalShapedRedeemerIdx pIdx nIdx)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := globalShapedRedeemerIdx pIdx nIdx
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- **REDUCTION: SHAPE G2 AT `(pIdx, nIdx) = (0, 1)` *IS* SHAPE G1, DEFINITIONALLY.**

Added at the G stage (2026-07-25) to answer audit finding **F22**, which observed
that `ShapeBridge.bridge_GIdx` / `bridge_GNIdx` were the ONLY results over
`appliedGlobalShapedIdx1600` / `appliedGlobalShapedNIdx1600`, that this module
contained **defs only and no theorems**, and that an `↔` between two unsatisfiable
statements is true — so if the G2/G3 accept-classes were empty at budget 1600 both
bridges would hold vacuously and nothing in the build would say so.

This is the one line that closes that: SHAPE G1's redeemer is
`TransferAct [] [] [NonMember 1] 0` (`GlobalShaped.lean:100-101`) and SHAPE G2's is
the same term with the two indices as arguments, so substituting `0` and `1`
recovers G1 on the nose — `rfl`, kernel-checked, no solver, no axiom. Everything
else in the two builders is byte-identical.

Consumed by `ShapeBridge.G1NonVacuity.propIdx_accepts_1600` /
`propNIdx_accepts_1600`, which chain it through the bridges to inherit SHAPE G1's
concrete accepting witness and thereby exhibit both accept-classes as NON-EMPTY.
`rangeG1 ⊆ rangeGIdx` follows immediately, in the same sense
`localRCtxIdx_at_one` gives SHAPE L1R ⊆ SHAPE L2R. -/
theorem globalShapedCtxIdx_at_0_1
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
        0 1
      = globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee :=
  rfl

def globalShapedInputsIdx
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (pIdx nIdx : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
        pIdx nIdx)

#prep_uplc appliedGlobalShapedIdx1600 programmableLogicGlobal1600 globalShapedInputsIdx 1600

/-- **SHAPE G3** — SHAPE G1 with the `NonMember` node index SYMBOLIC but
`paramsRefIdx` still pinned to 0.

WHY G3 EXISTS AND G2 DOES NOT CLOSE (task Z2, measured): over SHAPE G2 the
index-free obligation `accept ⟹ hasCoveringNode dirCS cs refInputs` is
**FALSIFIED**, with the counterexample `pIdx = 1, nIdx = 1` (full assignment in
WSC/SHAPING-RESULTS.md). It is not a validator defect: with a free
`paramsRefIdx` the validator resolves its params UTxO at reference index 1 — the
directory node — and authenticates it by `phasCSH ppCS` (satisfied there because
`nCS = ppCS` in the counterexample), then reads position 0 of THAT datum as
`directoryNodeCS`. So the policy the validator actually authenticated against is
`key`, not the `dirCS` written in the params datum at reference index 0, which the
validator never read. The postcondition named the wrong object.

The lesson is exactly why `WSC/Props/P5_NonMember.lean` states P5 in INDEXED form,
with `paramsDatumDirCSRaw` read at the redeemer's own `paramsRefIdx`: `dirCS` must
be named through the validator's index, not through a chosen reference position.
An honest deployment additionally forbids the counterexample by `TS2` (params-NFT
uniqueness, WSC/Honest.lean), which is not available to the bytecode theorem.

G3 pins `paramsRefIdx = 0` so that the shape's reference input 0 IS the params
UTxO the validator reads, and then leaves the node index free — which is the
loosening that is sound to state index-free. -/
def globalShapedInputsNIdx
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer)
    : List Term :=
  globalShapedInputsIdx protocolParamsCS cs tn q owner inAda dest outAda qOut
    pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
    key next tlsH ilsH gsCS w0 w1 a0 a1 fee 0 nIdx

#prep_uplc appliedGlobalShapedNIdx1600 programmableLogicGlobal1600 globalShapedInputsNIdx 1600

end WSC
