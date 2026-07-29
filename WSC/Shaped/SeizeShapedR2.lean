/-
WSC/Shaped/SeizeShapedR2.lean — **SHAPE S1R2: SHAPE S1R with MULTI-TOKEN values.**

S1R2 differs from `WSC/Shaped/SeizeShapedR.lean`'s SHAPE S1R in exactly one
respect: every `Value` that P2's containment conjunct reads — mini-ledger input
0, continuing output 0, output 1 — and the MINT field carry a non-ada policy
with **TWO** token names instead of one, with independent symbolic quantities.
Everything else (addresses, datums, reference inputs, withdrawal map, redeemer
map, script info) is S1R's, re-used by name.

The point of the shape is to ask whether `P2b_R_containment` needed
one-token-name values or only ledger canonicity.
-/
import WSC.Shaped.SeizeShapedR

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol ScriptContext ScriptHash
                          StakingCredential TokenName TxInInfo TxOutRef TxInfo
                          Withdrawals rewardingInputs ScriptPurpose)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

namespace Shape

/-- Canonical `Value`: ada plus exactly one other policy carrying **TWO** token
names.  `validTxOutValue` forces `tn1 < tn2` and all three quantities `> 0`; the
shape fixes neither. -/
def adaPlusTwoTN (n : Integer) (cs : CurrencySymbol) (tn1 : TokenName) (q1 : Integer)
    (tn2 : TokenName) (q2 : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [ (Data.B adaCS, Data.Map [(Data.B adaTN, Data.I n)])
  , (Data.B cs, Data.Map [(Data.B tn1, Data.I q1), (Data.B tn2, Data.I q2)]) ]

/-- Mint field carrying one policy and **TWO** token names, both quantities
symbolic and of free sign. -/
def mintTwoTN (cs : CurrencySymbol) (tn1 : TokenName) (q1 : Integer)
    (tn2 : TokenName) (q2 : Integer) : CardanoLedgerApi.V3.MintValue :=
  [(Data.B cs, Data.Map [(Data.B tn1, Data.I q1), (Data.B tn2, Data.I q2)])]

end Shape

/-- SHAPE S1R2's mini-ledger input (input 0) — S1R's `seizeShapedIn0` with a
second token name under `mlCS`. -/
def seizeR2In0
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
    (i0Qty i0Qty2 : Integer) (dIn : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential mlH, some (.StakingHash (.PubKeyCredential inStk))⟩
   , txOutValue := Shape.adaPlusTwoTN i0Ada mlCS mlTn i0Qty mlTn2 i0Qty2
   , txOutDatum := .OutputDatum (Data.B dIn)
   , txOutReferenceScript := none }⟩

/-- SHAPE S1R2's continuing output (output 0).  Shares `mlH`, `mlCS`, `mlTn`,
`mlTn2` with input 0 (DEFECT D4, inherited); both quantities are free. -/
def seizeR2Out0
    (mlH oStk : ByteString) (o0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
    (o0Qty o0Qty2 : Integer) (dOut : ByteString) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential mlH, some (.StakingHash (.PubKeyCredential oStk))⟩
  , txOutValue := Shape.adaPlusTwoTN o0Ada mlCS mlTn o0Qty mlTn2 o0Qty2
  , txOutDatum := .OutputDatum (Data.B dOut)
  , txOutReferenceScript := none }

/-- SHAPE S1R2's second output (output 1), two token names under `o1CS`. -/
def seizeR2Out1
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
    (o1Qty o1Qty2 : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential escH, none⟩
  , txOutValue := Shape.adaPlusTwoTN o1Ada o1CS o1Tn o1Qty o1Tn2 o1Qty2
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- **SHAPE S1R2.** -/
def seizeR2Ctx
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ seizeR2In0 mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
          , seizeShapedIn1 wallet i1Ada i1CS i1Tn i1Qty ]
      , txInfoReferenceInputs :=
          [ seizeShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , seizeShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ seizeR2Out0 mlH oStk o0Ada mlCS mlTn mlTn2 o0Qty o0Qty2 dOut
          , seizeR2Out1 escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 ]
      , txInfoFee := fee
      , txInfoMint := Shape.mintTwoTN mCS mTn mQ mTn2 mQ2
      , txInfoTxCerts := []
      , txInfoWdrl := seizeShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := seizeShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def seizeR2Inputs
    (protocolParamsCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2
        mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 spRed mtRed ilRed fee)

#prep_uplc appliedSeizeR2Shaped3800 programmableSeize seizeR2Inputs 3800

end WSC
