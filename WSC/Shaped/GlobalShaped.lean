/-
WSC/Shaped/GlobalShaped.lean — SHAPED prep of the production transfer validator
`programmableLogicGlobal` at CEK step budget **1600** (task Z2 rung 4).

⚠ NODE-REALIZABILITY (task C1): SHAPE G1 below is EMPTY as a class of ledger
transactions (two script withdrawals, one redeemer entry). The re-cut,
redeemer-covered version is SHAPE G1R in WSC/Shaped/GlobalShapedR.lean; this
shape is kept because the emptiness proof and the historical P5 theorems are
stated over it.

Mechanism (i) (WSC/Shaped/Shape.lean): the shape is baked into the `#prep_uplc`
inputs function. Same flat and same budget as WSC/Prep/Global1600.lean; the only
difference from `appliedGlobal1600` is that the context argument is a shape
instead of a universally quantified `ScriptContext`.

════════════════════════════════════════════════════════════════════════════
SHAPE G1 — "a mint-side NonMember claim with a params node and one candidate
directory node".
════════════════════════════════════════════════════════════════════════════
This is the shape P5 (ADDENDUM E3) is actually about, and it is NOT the shape of
the `transfer-nonmember-covering-node` golden. FINDING (task Z2, recorded in
WSC/SHAPING-RESULTS.md): that golden's redeemer is
`d8799f9f01ff9f01ff8000ff` = `TransferAct [1] [1] [] 0`, i.e. **`mintProofs = []`**
— its covering-node check happens in the INPUT-side transfer walk
(`pcheckTransferLogicAndGetProgrammableValue`'s negative-proof branch,
ProgrammableLogicBase.hs:889-900), not in the mint walk
(`pcheckMintLogicAndGetProgrammableValue`, :996-1015) that
`WSC/Props/P5_NonMember.lean`'s `nonMemberNodeIdxOf` mirrors. With an empty mint
the validator does not even call the mint walk
(`pif (pnull # pto (pto mintValueNoGuarantees)) …`, :1219-1222). So that golden
witnesses "accepts within 1600 steps", but NOT "P5's hypotheses are
satisfiable"; SHAPE G1 is built to be the latter.

FIXED (the published scope — quote this with any theorem stated against this
prep):
* purpose REWARDING, own credential = `ScriptCredential w0`;
* 1 input, at a PUBKEY address, ada-only — so it does not sit at the
  mini-ledger credential and `pvalueFromCred` (:406-443) contributes nothing,
  which is why `transferProofs = transferWdrlIdxs = []` is the aligned choice;
* exactly 2 reference inputs: index 0 the protocol-params node, index 1 the
  candidate directory node; both at SCRIPT addresses, both with INLINE datums,
  both with ada plus exactly one other policy carrying exactly one token name;
* 1 output, at a PUBKEY address, ada plus exactly one token of the minted
  policy (it exists only so the ledger balance rule can be satisfied with a
  positive mint; it is not at the mini-ledger credential, so it plays no part in
  the containment check);
* mint field: exactly one policy `cs` with exactly one token name;
* withdrawal map: exactly 2 entries, both SCRIPT credentials;
* exactly 1 redeemer-map entry, for the own `Rewarding` purpose;
* empty certificate / signatory / datum / vote / proposal lists;
* redeemer = `TransferAct [] [] [NonMember 1] 0` — the two list-index fields of
  the redeemer are CONCRETE (`paramsRefIdx = 0`, the `NonMember` node index
  `= 1`): these are self-validating hints, re-checked by `pcheckedDrop`/`phead`
  plus the branch conditions, and they are exactly the fields the task's shaping
  doctrine permits to fix;
* the three `TxOutRef`s are `⟨"",0⟩` (input), `⟨"",1⟩` and `⟨"",2⟩` (reference
  inputs, in that order), the transaction id is `""`, and the validity interval
  is the finite closed `[0,1]`. None of these is read by this validator.

SYMBOLIC — in particular BOTH halves of P5's postcondition are free:
* `key` and `next` of the directory node's datum (so `coversCS cs node`
  = `key < cs && cs < next` must be EARNED from the bytecode);
* `nCS`, the policy of the directory node's first non-ada value entry, which is
  a DIFFERENT variable from `dirCS`, the directory policy published by the params
  datum (so `dirNodeAuthH dirCS node` = `nCS == dirCS` must also be EARNED —
  had the shape reused one variable for both, half the postcondition would have
  been true by construction);
* `pCS`, the params node's first non-ada policy, likewise a different variable
  from the script parameter `ppCS` (so `pparamsAtRefIdx`'s own `phasCSH` gate at
  :832 is not pre-satisfied either);
* `cs` (the policy claimed exempt), its token name and minted quantity;
* the params datum's three credentials, the node datum's two credentials and its
  `globalStateCS`; every address hash; every ada amount, token quantity,
  withdrawal amount and the fee.
-/
import WSC.Prep.Global1600
import WSC.Shaped.Shape
import WSC.Redeemer
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE G1's redeemer: `TransferAct [] [] [NonMember 1] 0`, built through
WSC/Redeemer.lean's audited `IsData PLGRedeemer` mirror
(ProgrammableLogicBase.hs:1135-1160 for the field order, :948-953 for
`MintProof`'s `Member = 0` / `NonMember = 1`). -/
def globalShapedRedeemer : Data :=
  IsData.toData (PLGRedeemer.TransferAct [] [] [MintProof.NonMember 1] 0)

/-- AUDIT: the shaped redeemer's `Data` encoding, spelled out. -/
theorem globalShapedRedeemer_eq :
    globalShapedRedeemer =
      Data.Constr 0 [Data.List [], Data.List [], Data.List [Data.Constr 1 [Data.I 1]], Data.I 0] := by
  native_decide

/-- SHAPE G1's protocol-params reference input (reference index 0). -/
def globalShapedParamsIn
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.ScriptCredential pHash, none⟩
   , txOutValue := adaPlusOne pAda pCS pTn pQty
   , txOutDatum := .OutputDatum
       (IsData.toData
         (GlobalParams.mk dirCS (.ScriptCredential plc) (.ScriptCredential glc)
                          (.ScriptCredential slc)))
   , txOutReferenceScript := none }⟩

/-- SHAPE G1's candidate directory node (reference index 1) — the object P5's
postcondition talks about. `nCS` (its first non-ada policy) and `key`/`next` are
free variables, so neither `dirNodeAuthH` nor `coversCS` is true by
construction. -/
def globalShapedNode
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 2⟩,
   { txOutAddress := ⟨.ScriptCredential nHash, none⟩
   , txOutValue := adaPlusOne nAda nCS nTn nQty
   , txOutDatum := .OutputDatum
       (IsData.toData
         (DirectorySetNode.mk key next (.ScriptCredential tlsH)
                              (.ScriptCredential ilsH) gsCS))
   , txOutReferenceScript := none }⟩

/-- SHAPE G1's withdrawal map. -/
def globalShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- **SHAPE G1.** See the module header for the full FIXED / SYMBOLIC split. -/
def globalShapedCtx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
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
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), globalShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := globalShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- Parameter evidence unchanged from WSC/Prep/Global1600.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1176-1177). -/
def globalShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#prep_uplc appliedGlobalShaped1600 programmableLogicGlobal1600 globalShapedInputs 1600

end WSC
