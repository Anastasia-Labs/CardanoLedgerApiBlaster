/-
WSC/Shaped/MintingShapedRIdx.lean — **SHAPE M2R = SHAPE M1R with the `BurnOnly`
redeemer's withdrawal index LOOSENED to a symbolic integer** (task C2, the
re-cut of SHAPE M2).

SHAPE M2 (`WSC/Shaped/MintingShapedIdx.lean`) exists to MEASURE whether pinning
`pboMintingLogicWdrlIdx = 0` was necessary; it inherits SHAPE M1's unrealizable
withdrawal/redeemer maps, so `ShapeRealizability`'s emptiness argument applies to
it verbatim. SHAPE M2R is the same loosening over the REALIZABLE cut: byte-identical
to SHAPE M1R except that `wIdx` is a free `Integer`, so the symbolic `dropList`
cannot be reduced at prep time.

The loosening is sharper here than at SHAPE M2. With SHAPE M1's TWO-entry
withdrawal map a symbolic index has two in-range values to explore; with SHAPE
M1R's ONE-entry map, `pcheckedDrop wIdx` on a singleton means the theorem covers
`wIdx = 0` (the only in-range value), every out-of-range value (where `phead`
errors) and every NEGATIVE value (which Issuance.hs:126-130 rejects explicitly
rather than by budget exhaustion). So the theorem below says: *whatever index the
`BurnOnly` redeemer names, an accepted mint has the minting-logic credential in
the withdrawal map* — and at this shape that is the statement that the explicit
negative-index guard and the `phead` error are both doing their job.
-/
import WSC.Shaped.MintingShapedR
import WSC.Shaped.Shape
import WSC.Redeemer
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals ScriptPurpose mintingInputs findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE M2R's redeemer: `BurnOnly wIdx` with `wIdx` SYMBOLIC. -/
def mintRRedeemerIdx (wIdx : Integer) : Data :=
  IsData.toData (MintRedeemer.BurnOnly wIdx)

/-- SHAPE M2R's redeemer map — SHAPE M1R's, with the loosened own redeemer. -/
def mintRRedeemerMapIdx (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    (wIdx : Integer) : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, mintRRedeemerIdx wIdx)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed) ]

/-- **SHAPE M2R.** -/
def mintRCtxIdx
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
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
      , txInfoMint := mintRMint ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := mintRWdrl w0 a0
      , txInfoValidRange := range lo hi
      , txInfoSignatories := []
      , txInfoRedeemers := mintRRedeemerMapIdx ownCS w0 mlRed wIdx
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := mintRRedeemerIdx wIdx
  , scriptContextScriptInfo := .MintingScript ownCS }

theorem mintRCtxIdx_redeemers
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer) :
    (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
      lo hi tid wIdx).scriptContextTxInfo.txInfoRedeemers
      = mintRRedeemerMapIdx ownCS w0 mlRed wIdx := rfl

/-! ### Coverage at SHAPE M2R — the loosened index does not touch it -/

theorem mintRIdx_findRewarding (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    (wIdx : Integer) :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (mintRRedeemerMapIdx ownCS w0 mlRed wIdx)
      = some (Data.B mlRed) := by
  rw [mintRRedeemerMapIdx,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

theorem mintRIdx_findMinting (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    (wIdx : Integer) :
    findRedeemer (.Minting ownCS) (mintRRedeemerMapIdx ownCS w0 mlRed wIdx)
      = some (mintRRedeemerIdx wIdx) := by
  rw [mintRRedeemerMapIdx, Realizability.findRedeemer_cons_hit]

section Cover
variable (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (dest : ByteString) (outAda qOut : Integer)
         (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
         (fee : Integer) (txid : ByteString) (oidx : Integer)
         (lo hi : Integer) (tid : ByteString) (wIdx : Integer)

theorem mintRIdx_wdrl_covered :
    Realizability.WdrlCovered
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) := by
  intro h n hmem
  simp [mintRCtxIdx, mintRWdrl] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [mintRCtxIdx_redeemers, mintRIdx_findRewarding]
  exact Option.noConfusion

theorem mintRIdx_spend_covered :
    Realizability.SpendCovered
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) := by
  intro i hin hscript
  simp [mintRCtxIdx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

theorem mintRIdx_mint_covered :
    Realizability.MintCovered
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx) := by
  intro cs m hmem
  simp [mintRCtxIdx, mintRMint, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [mintRCtxIdx_redeemers, mintRIdx_findMinting]
  exact Option.noConfusion

end Cover

def mintRInputsIdx
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee
        txid oidx lo hi tid wIdx)

#prep_uplc appliedMintRShapedIdx900 programmableTokenMinting900 mintRInputsIdx 900

end WSC
