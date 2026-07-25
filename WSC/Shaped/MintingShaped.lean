/-
WSC/Shaped/MintingShaped.lean — SHAPED prep of the production issuance policy
`programmableTokenMinting` at CEK step budget **900** (task Z2 rung 2).

Mechanism (i) (see WSC/Shaped/Shape.lean): the shape is baked into the
`#prep_uplc` inputs function, so the term the SOLVER sees has a closed `Data`
skeleton and only scalar leaves are symbolic. Same flat, same budget, same
imported program object as WSC/Prep/Minting900.lean — the ONLY difference from
`appliedMinting900` is that the context argument is a shape instead of a
universally quantified `ScriptContext`.

WHY THIS SHAPE (SHAPE M1). It is the `mint-burnonly` golden's shape
(WSC/goldens/programmableTokenMinting.mint-burnonly.json, K = 784 CEK steps,
WSC/goldens/K-MEASUREMENTS.md §3) and the hand-built `P4Witness.ctx`'s shape
(WSC/Props/P4_Minting.lean:444-463), generalised in three directions so that the
theorems below are not trivial:

* the withdrawal map has TWO entries, not one, and BOTH credentials are
  symbolic — P4a's conclusion is a statement about exactly those, so shaping them
  concretely would have smuggled in the postcondition;
* there is ONE OUTPUT carrying ada plus the policy's own token, so the ledger
  balance rule does NOT force the minted quantity negative: `q = qOut - qIn` can
  be positive. That is what makes "accept ⟹ q ≤ 0" (the `BurnOnly` scan,
  Issuance.hs:251-254) something the BYTECODE has to earn rather than something
  the hypothesis hands over;
* every byte string and every integer in the context is a free variable.

WHAT IS FIXED (the published scope — quote this with any theorem below):
1 input; 1 output; 0 reference inputs; empty certificate / signatory / datum /
vote / proposal lists; a mint field with exactly one policy (the policy's own)
carrying exactly one token name; a withdrawal map of exactly 2 entries, both
SCRIPT credentials; exactly 1 redeemer entry, for the `Minting ownCS` purpose;
the input and the output are both at PUBKEY addresses with no datum and no
reference script and carry canonical ada-plus-one-token values; a finite closed
validity interval; `txInfoCurrentTreasuryAmount = txInfoTreasuryDonation = 1`;
and the redeemer is `BurnOnly` (constructor tag 3, Issuance.hs:88-90, :118-120)
with its single index field `pboMintingLogicWdrlIdx = 0`.

ARM SCOPE. Fixing the redeemer tag to 3 restricts the shape to the `BurnOnly`
arm. That is not a loss at this budget: K-MEASUREMENTS §3 measures the other
three arms' cheapest accepting goldens at 1,257 and 1,681 steps, so at 900 they
cannot accept at all (WSC/Props/P4_Minting.lean "ARM SCOPE").
`WSC/Shaped/MintingShapedIdx.lean` loosens the index field to a symbolic
integer; the tag stays 3.
-/
import WSC.Prep.Minting900
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

/-- SHAPE M1's withdrawal map: two entries, both script credentials, symbolic
hashes and amounts. -/
def mintShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- SHAPE M1's mint field: exactly one policy (the policy's own `ownCS`)
carrying exactly one token name, symbolic signed quantity. -/
def mintShapedMint (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer) : MintValue :=
  mintOne ownCS tn q

/-- SHAPE M1's redeemer: `BurnOnly { pboMintingLogicWdrlIdx = 0 }`. Constructor
tag 3 is frozen by `makeIsDataIndexed` at Issuance.hs:88-90; the single
`Integer` field is at Issuance.hs:118-120. Written through WSC/Redeemer.lean's
audited mirror rather than as a raw `Data` literal, and `mintShapedRedeemer_eq`
below pins the encoding. -/
def mintShapedRedeemer : Data := IsData.toData (MintRedeemer.BurnOnly 0)

/-- AUDIT: the shaped redeemer really is `Data.Constr 3 [Data.I 0]`. -/
theorem mintShapedRedeemer_eq : mintShapedRedeemer = Data.Constr 3 [Data.I 0] := by
  native_decide

/-- **SHAPE M1.** See the module header for the full FIXED / SYMBOLIC split. -/
def mintShapedCtx
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString)
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
      , txInfoRedeemers := [(.Minting ownCS, mintShapedRedeemer)]
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := mintShapedRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

/-! ### AUDIT LINKS — the named projections ARE the shaped context's fields.

The theorems in WSC/Shaped/P4Shaped.lean quote `mintShapedWdrl` /
`mintShapedMint` instead of writing out `(mintShapedCtx …).scriptContextTxInfo.…`,
purely for readability. These two `rfl`s are what makes that substitution
audited rather than assumed. -/

theorem mintShapedCtx_wdrl
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid).scriptContextTxInfo.txInfoWdrl
      = mintShapedWdrl w0 w1 a0 a1 := rfl

theorem mintShapedCtx_mint
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid).scriptContextTxInfo.txInfoMint
      = mintShapedMint ownCS tn q := rfl

/-- Parameter evidence is unchanged from WSC/Prep/Minting900.lean (2 parameters,
`protocolParamsCS` then `mintingLogicHash`, the latter LAST — Issuance.hs:132-133,
offchain Scripts.hs:135-140). Only the third argument is shaped. -/
def mintShapedInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)

#prep_uplc appliedMintShaped900 programmableTokenMinting900 mintShapedInputs 900

end WSC
