/-
WSC/Shaped/MintingShapedIdx.lean — SHAPE M2 = SHAPE M1 with the redeemer's index
field LOOSENED to a symbolic integer (task Z2, loosening rung).

SHAPE M1 fixes `pboMintingLogicWdrlIdx = 0`. The task's shaping doctrine permits
that (the index is a self-validating hint: `pcheckedDrop` rejects a negative
index explicitly at Issuance.hs:126-130, then `phead` errors on an out-of-range
one, and the credential comparison at :150-151 re-checks the entry it points at).
SHAPE M2 exists to MEASURE whether fixing it was necessary: it is byte-identical
to M1 except that `wIdx` is a free `Integer`, so the symbolic `dropList` cannot be
reduced at prep time.
-/
import WSC.Shaped.MintingShaped
import WSC.Shaped.Shape
import WSC.Redeemer
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals mintingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE M2's redeemer: `BurnOnly wIdx` with `wIdx` SYMBOLIC. -/
def mintShapedRedeemerIdx (wIdx : Integer) : Data :=
  IsData.toData (MintRedeemer.BurnOnly wIdx)

/-- **SHAPE M2** — SHAPE M1 with a symbolic withdrawal index. -/
def mintShapedCtxIdx
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer)
    : ScriptContext :=
  let outRef : TxOutRef := ⟨txid, oidx⟩
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaPlusOne inAda ownCS tn qIn
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  let produced : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential dest, none⟩
    , txOutValue := adaPlusOne outAda ownCS tn qOut
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨outRef, resolved⟩]
      , txInfoReferenceInputs := []
      , txInfoOutputs := [produced]
      , txInfoFee := fee
      , txInfoMint := mintShapedMint ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := mintShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range lo hi
      , txInfoSignatories := []
      , txInfoRedeemers := [(.Minting ownCS, mintShapedRedeemerIdx wIdx)]
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := mintShapedRedeemerIdx wIdx
  , scriptContextScriptInfo := .MintingScript ownCS }

def mintShapedInputsIdx
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee
        txid oidx lo hi tid wIdx)

#prep_uplc appliedMintShapedIdx900 programmableTokenMinting900 mintShapedInputsIdx 900

end WSC
