/-
WSC/Shaped/MintingLocalShapedIdx.lean — **SHAPE L2**: SHAPE L1 with the
registration witness's REFERENCE-INPUT INDEX left SYMBOLIC, at CEK budget 2500
(task V3 loosening rung).

WHY. WSC/SHAPING-RESULTS.md §2.4 and §6.2 record that the two validators behave
DIFFERENTLY under index loosening: for the ISSUANCE policy the concrete redeemer
index is dispensable (SHAPE M2 closes in 2.1 s with the withdrawal index free),
while for the GLOBAL validator it is load-bearing (SHAPE G3 returns
`Undetermined` after 906 s even though its shape class is non-empty). This module
asks the same question of the `Local` arm's REGISTRATION index — the index that
selects which reference input is claimed to carry the directory NFT
(Issuance.hs:172-173).

DIFFERENCE FROM SHAPE L1 (WSC/Shaped/MintingLocalShaped.lean), which is otherwise
reproduced verbatim: the redeemer is
`Local 0 0 (RegisteredByReferenceInput regIdx)` with `regIdx` a FREE `Integer`
leaf instead of the constant 1. The constructor TAGS stay concrete (`Local` = 0,
`RegisteredByReferenceInput` = 0), as does `mrMintingLogicWdrlIdx = 0` and
`mrParamsRefIdx = 0`.

The postconditions proved against this prep must be INDEX-FREE, and both of the
interesting ones already are: `noEscape` never mentions an index at all, and
`anyRefInputHasNodeNFT` is the ∃-over-reference-inputs form. So — unlike SHAPE G2,
where an index-free postcondition NAMED THE WRONG OBJECT and was genuinely
falsified (WSC/SHAPING-RESULTS.md §6.1) — there is no naming hazard here: the
params record is still named through `mrParamsRefIdx`, which stays pinned to 0.

Note `pcheckedDrop` (Issuance.hs:126-130) explicitly rejects a NEGATIVE index
rather than clamping, so a symbolic `regIdx` genuinely ranges over the failing
cases too.
-/
import WSC.Shaped.MintingLocalShaped
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxInfo Withdrawals mintingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE L2's redeemer: `Local 0 0 (RegisteredByReferenceInput regIdx)`. -/
def localIdxShapedRedeemer (regIdx : Integer) : Data :=
  IsData.toData (MintRedeemer.Local 0 0 (RegWitness.RegisteredByReferenceInput regIdx))

/-- AUDIT: `Constr 0 [I 0, I 0, Constr 0 [I regIdx]]`. -/
theorem localIdxShapedRedeemer_eq (regIdx : Integer) :
    localIdxShapedRedeemer regIdx
      = Data.Constr 0 [Data.I 0, Data.I 0, Data.Constr 0 [Data.I regIdx]] := rfl

/-- **SHAPE L2.** SHAPE L1 with a symbolic registration index. -/
def localIdxShapedCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (regIdx : Integer)
    (fee : Integer)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaPlusOne inAda ownCS tn qIn
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨⟨ByteString.mk "", 0⟩, resolved⟩]
      , txInfoReferenceInputs :=
          [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1
      , txInfoFee := fee
      , txInfoMint := mintOne ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := localShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := [(.Minting ownCS, localIdxShapedRedeemer regIdx)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := localIdxShapedRedeemer regIdx
  , scriptContextScriptInfo := .MintingScript ownCS }

def localIdxShapedInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (regIdx : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee)

#prep_uplc appliedMintLocalIdxShaped2500 programmableTokenMinting900 localIdxShapedInputs 2500

end WSC
