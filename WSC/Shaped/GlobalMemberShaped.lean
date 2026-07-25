/-
WSC/Shaped/GlobalMemberShaped.lean — SHAPED prep of the production transfer
validator `programmableLogicGlobal` on a **`Member` mint classification**, at CEK
step budget **3300** (task V3 rung 4 — the P6 shape).

Mechanism (i) (WSC/Shaped/Shape.lean): the shape is baked into the `#prep_uplc`
inputs function. Same flat and same imported program object as
WSC/Prep/Global1600.lean (`programmableLogicGlobal1600`); only the budget and the
context argument differ. Shaped prep is essentially budget-independent
(WSC/SHAPING-RESULTS.md §2.5), so 3300 costs the same as 1600.

════════════════════════════════════════════════════════════════════════════
SHAPE G6 — "a transfer whose only programmable value is a NONZERO MINT that the
redeemer classifies `Member`, with TWO candidate mini-ledger outputs".
════════════════════════════════════════════════════════════════════════════
This is the shape P6 is about, and it is the mirror image of SHAPE G1 (which is
P5's, the `NonMember` side). The two differ in exactly one leaf-free position —
the mint proof — which is what makes the pair a genuine demonstration of P6's
plain-English content: *a `Member` claim ADDS the minted amount to what must
remain inside the mini-ledger, whereas a `NonMember` claim removes it.*

FIXED (the published scope — quote this with any theorem stated against this
prep):
* purpose REWARDING, own credential = `ScriptCredential w0`;
* redeemer = `TransferAct [] [] [Member] 0`, i.e. NO transfer proofs, NO transfer
  withdrawal indices, exactly ONE mint proof and it is `Member` (constructor tag
  0 — ProgrammableLogicBase.hs:1041-1043), and `paramsRefIdx = 0` (a
  self-validating hint re-checked by `pparamsAtRefIdx`'s `phasCSH` gate at :832);
* exactly 1 input, at a PUBKEY address, ADA-ONLY — so it does not sit at the
  mini-ledger credential and `pvalueFromCred` (:406-443) contributes nothing.
  That is what makes `transferProofs = transferWdrlIdxs = []` the aligned choice,
  and it is also what isolates P6: the ENTIRE programmable requirement in this
  shape comes from the mint side, which is the side P6 is about;
* exactly 1 reference input, at index 0: the protocol-params node, at a SCRIPT
  address with an INLINE `GlobalParams` datum and ada plus one other policy. A
  `Member` proof touches NO directory node (ProgrammableLogicBase.hs:989-991 and
  the source comment at :966-969), which is exactly why no directory node is in
  this shape — its absence is part of the statement, not an omission;
* exactly 2 OUTPUTS, both at SCRIPT addresses with no staking credential, no
  datum and no reference script, each carrying ada plus the minted policy `cs`
  with token name `tn`:
  - output 0 at `ScriptCredential ob0` holding `qq0` of `cs.tn`,
  - output 1 at `ScriptCredential ob1` holding `qq1` of `cs.tn`;
* mint field: exactly one policy `cs` with exactly one token name `tn` and a
  symbolic SIGNED quantity `q`;
* withdrawal map: exactly 2 entries, both SCRIPT credentials;
* exactly 1 redeemer-map entry, for the own `Rewarding` purpose;
* empty certificate / signatory / datum / vote / proposal lists;
* `TxOutRef`s `⟨"",0⟩` (input) and `⟨"",1⟩` (reference input); transaction id
  `""`; validity interval the finite closed `[0,1]`; treasury amount and donation
  `1`. None of these is read by this validator.

SYMBOLIC: every byte string and every integer above — in particular BOTH output
payment-credential hashes `ob0`, `ob1`, BOTH output quantities `qq0`, `qq1`, the
minted quantity `q`, the params datum's four fields (so `plc`, the mini-ledger
base credential, is a free variable), the params node's own value policy `pCS`
(a DIFFERENT variable from the script parameter `ppCS`, so `pparamsAtRefIdx`'s
`phasCSH` gate is not pre-satisfied), both withdrawal script hashes, and the fee.

════════════════════════════════════════════════════════════════════════════
WHY TWO OUTPUTS — AND WHY THE POSTCONDITION IS NOT IMPLIED BY THE LEDGER
════════════════════════════════════════════════════════════════════════════
This is the design point of SHAPE G6 and the reason it has two outputs rather
than one.

`isBalanced` (CardanoLedgerApi/V3/Contexts.lean:1185-1189) forces, on the non-ada
axis, `{cs ↦ {tn ↦ q}} = {cs ↦ {tn ↦ qq0 + qq1}}`, i.e. **`qq0 + qq1 = q`**: the
ledger guarantees the minted tokens are SOMEWHERE among the outputs. It says
NOTHING about which outputs. The postcondition is about the sum over outputs AT
THE BASE CREDENTIAL only:

    outAtBaseQty (ScriptCredential plc) cs tn outputs  ≥  mintOf cs tn mint

With ONE output the ledger would already force that output to hold all of `q`, and
the only remaining content would be a single credential comparison. With TWO the
split `(qq0, qq1)` is free and `ob0`, `ob1` are independent free variables, so the
inequality genuinely quantifies: the validator has to force ENOUGH of the split to
land at `plc`, and it cannot be satisfied by the ledger's global conservation
alone.

Neither `ob0 = plc` nor `ob1 = plc` is baked in: `ob0`, `ob1` and `plc` are three
different free variables. Had the shape written the outputs at
`ScriptCredential plc`, the postcondition would have been ledger-implied and P6
would have been vacuous at this shape.
-/
import WSC.Prep.Global1600
import WSC.Shaped.GlobalShaped
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

/-- SHAPE G6's redeemer: `TransferAct [] [] [Member] 0`, built through
WSC/Redeemer.lean's audited `IsData PLGRedeemer` mirror
(ProgrammableLogicBase.hs:1046-1054 for the field order, :1041-1043 for
`MintProof`'s `Member = 0`). -/
def memberShapedRedeemer : Data :=
  IsData.toData (PLGRedeemer.TransferAct [] [] [MintProof.Member] 0)

/-- AUDIT: the shaped redeemer's `Data` encoding, spelled out. Note the mint proof
is `Constr 0 []` — a `Member` claim carries NO node index, which is the encoding
fact P6's plain-English statement rests on. -/
theorem memberShapedRedeemer_eq :
    memberShapedRedeemer =
      Data.Constr 0 [Data.List [], Data.List [], Data.List [Data.Constr 0 []], Data.I 0] := by
  native_decide

/-- SHAPE G6's output `i`: a SCRIPT address with free hash `obh`, carrying ada plus
`qq` of the minted asset `cs.tn`. -/
def memberShapedOut (obh : ByteString) (outAda : Integer)
    (cs tn : ByteString) (qq : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential obh, none⟩
  , txOutValue := adaPlusOne outAda cs tn qq
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- SHAPE G6's output list, named so the theorems can quote it. -/
def memberShapedOutputs (cs tn : ByteString)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer) : List TxOut :=
  [memberShapedOut ob0 outAda0 cs tn qq0, memberShapedOut ob1 outAda1 cs tn qq1]

/-- SHAPE G6's single input: a PUBKEY address, ada-only — deliberately NOT at the
mini-ledger credential, so `pvalueFromCred` contributes nothing and the whole
programmable requirement comes from the mint. -/
def memberShapedInput (owner : ByteString) (inAda : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.PubKeyCredential owner, none⟩
   , txOutValue := adaOnly inAda
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- **SHAPE G6.** See the module header for the full FIXED / SYMBOLIC split. The
protocol-params reference input is SHAPE G1's `globalShapedParamsIn`
(WSC/Shaped/GlobalShaped.lean) verbatim, so the two shapes' params views are
literally the same object. -/
def memberShapedCtx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := [memberShapedInput owner inAda]
      , txInfoReferenceInputs :=
          [ globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc ]
      , txInfoOutputs := memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := globalShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), memberShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := memberShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-! ### AUDIT LINKS -/

section Audit
variable (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
         (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
         (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer) (fee : Integer)

private abbrev mCtx : ScriptContext :=
  memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
    pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee

theorem memberShapedCtx_outputs :
    (mCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
      pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
      = memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1 := rfl

theorem memberShapedCtx_inputs :
    (mCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
      pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
      = [memberShapedInput owner inAda] := rfl

theorem memberShapedCtx_mint :
    (mCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
      pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint
      = mintOne cs tn q := rfl

theorem memberShapedCtx_refInputs :
    (mCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
      pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1
      fee).scriptContextTxInfo.txInfoReferenceInputs
      = [globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc] := rfl

end Audit

/-- Parameter evidence unchanged from WSC/Prep/Global1600.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1176-1177). -/
def memberShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)

#prep_uplc appliedGlobalMemberShaped3300 programmableLogicGlobal1600 memberShapedInputs 3300

/-! ## SHAPE G6N — the NONMEMBER sibling of SHAPE G6, for the P6 contrast

SHAPE G6 with exactly two changes: the mint proof becomes `NonMember 1`
(`globalShapedRedeemer`, WSC/Shaped/GlobalShaped.lean) and a candidate directory
node is added as reference input 1 (`globalShapedNode`, ibid.) so that the
`PNonMember` branch has a node to authenticate. Everything else — the ada-only
pubkey input, the two script-address outputs holding the minted asset, the mint
field, the withdrawal map, the params reference input — is byte-for-byte SHAPE
G6's.

WHY IT EXISTS. It is not used for a theorem of its own (P5 already covers the
`NonMember` side, over SHAPE G1). Its purpose is to make P6's plain-English
claim — *"claiming `Member` can only make the containment obligation HARDER"* —
into an executable measurement rather than a reading of the source: the SAME
escaping transaction is REJECTED under `Member` and ACCEPTED under `NonMember`.
See `WSC/Props/Shaped/P6Shaped.lean`'s `§ SELF-PENALIZATION, MEASURED` section. -/

def nonMemberSiblingCtx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := [memberShapedInput owner inAda]
      , txInfoReferenceInputs :=
          [ globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1
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

end WSC
