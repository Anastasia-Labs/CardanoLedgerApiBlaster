/-
WSC/Shaped/MintingLocalShaped.lean — SHAPED prep of the production issuance
policy `programmableTokenMinting` on its **`Local` custody arm**, at CEK step
budget **2500** (task V3 rung 1).

Mechanism (i) (WSC/Shaped/Shape.lean): the shape is baked into the `#prep_uplc`
inputs function. Same flat and same imported program object as
WSC/Prep/Minting900.lean (`programmableTokenMinting900`); only the budget and the
context argument differ. The budget is raised because the `Local` arm's cheapest
accepting golden, `mint-local-registered-by-ref`, needs **1,681** CEK steps
(WSC/goldens/K-MEASUREMENTS.md §3) — far above the 900 that SHAPE M1/M2 use — and
shaped prep is essentially budget-independent (WSC/SHAPING-RESULTS.md §2.5:
1.2–1.3 s at 900/1600/1700/2500/4000), so the budget is free to raise.

════════════════════════════════════════════════════════════════════════════
SHAPE L1 — "a Local-arm mint with a params reference input, a registration
reference input, and TWO outputs".
════════════════════════════════════════════════════════════════════════════
This is the shape that carries the real custody weight of the issuance policy:
`Local` is the arm in which the policy does its OWN no-escape scan over every
output (Issuance.hs:179-193) instead of delegating to the global transfer
validator or to the seize validator.

FIXED (the published scope — quote this with any theorem stated against this
prep):
* purpose MINTING, own currency symbol `ownCS`;
* redeemer = `Local { mrMintingLogicWdrlIdx = 0, mrParamsRefIdx = 0,
  mrRegistration = RegisteredByReferenceInput 1 }` — constructor tag 0
  (Issuance.hs:88-90), registration-witness tag 0 (Issuance.hs:57-59). The three
  index fields are CONCRETE; they are self-validating hints, re-checked by
  `pcheckedDrop`/`phead` plus the per-branch conditions
  (Issuance.hs:126-130, :150-151, :172-173), which is exactly the class of field
  the shaping doctrine permits to fix;
* exactly 2 reference inputs: index 0 the protocol-params node, index 1 the
  claimed registration node; both at SCRIPT addresses, both with INLINE datums,
  both carrying ada plus exactly one other policy with exactly one token name;
* exactly 1 input, at a PUBKEY address, ada plus one token of `ownCS`;
* exactly 2 OUTPUTS, both at SCRIPT addresses with no staking credential, no
  datum and no reference script:
  - output 0 carries ada plus exactly one other policy `c0` with token name
    `tn0` and quantity `qq0` — **`c0` is a FREE variable, deliberately NOT fixed
    to `ownCS`** (see "NOT TRUE BY CONSTRUCTION" below);
  - output 1 is ada-only;
* mint field: exactly one policy (the policy's own `ownCS`) with exactly one
  token name and a symbolic SIGNED quantity;
* withdrawal map: exactly 2 entries, both SCRIPT credentials;
* exactly 1 redeemer-map entry, for the own `Minting ownCS` purpose;
* empty certificate / signatory / datum / vote / proposal lists;
* the `TxOutRef`s are `⟨"",0⟩` (input), `⟨"",1⟩` / `⟨"",2⟩` (reference inputs);
  transaction id `""`; validity interval the finite closed `[0,1]`;
  `txInfoCurrentTreasuryAmount = txInfoTreasuryDonation = 1`. None of these is
  read by this validator.

SYMBOLIC: every byte string and every integer above — in particular the two
output payment-credential hashes `o0h`, `o1h`, the output policy `c0`, the
params datum's four fields (`dirCS`, `plc`, `glc`, `slc`), the registration
node's value policy `nCS` / token name `nTn` / quantity `nQty`, both withdrawal
script hashes, the signed minted quantity `q`, and both script parameters
`ppCS`, `mlh`.

════════════════════════════════════════════════════════════════════════════
NOT TRUE BY CONSTRUCTION — the three places a lazy shape would have cheated
════════════════════════════════════════════════════════════════════════════
The postcondition is `WSC/Spec.lean`'s `LocalCustodyOk`, whose three conjuncts
are C1 (minting-logic withdrawal), registration, and `noEscape`. Each one is a
statement about objects the shape leaves FREE:

1. **C1.** Both withdrawal credentials `w0`, `w1` are free; `validMintingContext`
   constrains them only to be sorted (`validWithdrawals`). "The minting-logic
   credential is in the map" is therefore earned from the bytecode.
2. **Registration.** The registration node's value policy `nCS`, token name `nTn`
   and quantity `nQty` are three free variables, and `dirCS` — the directory
   policy the params datum publishes — is a FOURTH, DIFFERENT one. So
   `hasNodeNFT dirCS ownCS` (= `valueOf dirCS ownCS value == 1`,
   Issuance.hs:156-157) is not pre-satisfied. Likewise the params node's own
   value policy `pCS` is a different variable from the script parameter `ppCS`,
   so `pparamsAtRefIdx`'s `phasCSH` gate (ProgrammableLogicBase.hs:832) has to be
   cleared by the accept path.
3. **`noEscape`.** Its per-output disjunction is
   `payCred o == progLogicCred || ¬ hasCurrencySymbol ownCS o.value`, and BOTH
   disjuncts are live at the shape:
   - `payCred out0 = ScriptCredential o0h` versus `progLogicCred =
     ScriptCredential plc`, two DIFFERENT free variables — had the shape reused
     one, the first disjunct would have been `rfl`-true and the theorem empty;
   - `hasCurrencySymbol ownCS out0.txOutValue` reduces to `c0 == ownCS`, again
     two different free variables.
   Output 1 (ada-only) discharges the scan through the SECOND disjunct and
   output 0 through the FIRST, so the two-output scan genuinely exercises both
   halves of the disjunction rather than repeating one of them.

WHY TWO OUTPUTS AND NOT ONE. With a single output the ledger balance rule forces
that output to carry `ownCS` (there is nowhere else for the minted tokens to go),
so `noEscape` collapses to a single credential comparison and the ∀-scan is
degenerate. With two, the scan must traverse a list whose two elements take
DIFFERENT branches of the disjunction, which is what makes it a scan.

BALANCE NOTE (why `c0` may be left free even though the balance rule pins it).
`isBalanced` (CardanoLedgerApi/V3/Contexts.lean:1185-1189) forces
`{ownCS ↦ {tn ↦ qIn + q}} = {c0 ↦ {tn0 ↦ qq0}}` on the non-ada axis, i.e.
`c0 = ownCS`, `tn0 = tn`, `qq0 = qIn + q`, for every LEDGER-VALID instance. The
shape does not encode that; the solver has to derive it from the hypothesis. Two
consequences: (a) the theorem's `¬hasCurrencySymbol` disjunct is genuinely
reachable syntactically and closed only by ledger reasoning, and (b) a positive
mint (`q > 0`) IS ledger-legal at this shape — which is what makes the no-escape
scan a statement about token CREATION rather than an empty one.
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

/-- SHAPE L1's redeemer: `Local 0 0 (RegisteredByReferenceInput 1)`, written
through WSC/Redeemer.lean's audited mirror (tags: Issuance.hs:88-90 for
`Local = 0`, :57-59 for `RegisteredByReferenceInput = 0`; field order
Issuance.hs:66-70). -/
def localShapedRedeemer : Data :=
  IsData.toData (MintRedeemer.Local 0 0 (RegWitness.RegisteredByReferenceInput 1))

/-- AUDIT: the shaped redeemer really is `Constr 0 [I 0, I 0, Constr 0 [I 1]]`. -/
theorem localShapedRedeemer_eq :
    localShapedRedeemer = Data.Constr 0 [Data.I 0, Data.I 0, Data.Constr 0 [Data.I 1]] := by
  native_decide

/-- SHAPE L1's protocol-params reference input (reference index 0). Same layout
as WSC/Shaped/GlobalShaped.lean's `globalShapedParamsIn`; the datum is the
4-field `Data.List` of ProtocolParams.hs:84-96. -/
def localShapedParamsIn
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

/-- SHAPE L1's claimed registration node (reference index 1) — the object the
`RegisteredByReferenceInput 1` witness points at. Its value policy `nCS`, token
name `nTn` and quantity `nQty` are all free, so `hasNodeNFT dirCS ownCS`
(Issuance.hs:156-157) is not pre-satisfied. A `DirectorySetNode`-shaped inline
datum is carried for realism; the `Local` arm never decodes it (Issuance.hs:154-155
— "No datum decode (§7)"). -/
def localShapedNode
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

/-- SHAPE L1's output 0: a SCRIPT address with free hash `o0h`, carrying ada plus
one free policy `c0`. -/
def localShapedOut0 (o0h : ByteString) (outAda0 : Integer)
    (c0 tn0 : ByteString) (qq0 : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential o0h, none⟩
  , txOutValue := adaPlusOne outAda0 c0 tn0 qq0
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- SHAPE L1's output 1: a SCRIPT address with free hash `o1h`, ada-only — the
output that discharges the no-escape scan through its SECOND disjunct. -/
def localShapedOut1 (o1h : ByteString) (outAda1 : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential o1h, none⟩
  , txOutValue := adaOnly outAda1
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- SHAPE L1's withdrawal map: two entries, both script credentials, free
hashes. -/
def localShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- SHAPE L1's output list, named so the theorems can quote it. -/
def localShapedOutputs (o0h : ByteString) (outAda0 : Integer)
    (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer) : List TxOut :=
  [localShapedOut0 o0h outAda0 c0 tn0 qq0, localShapedOut1 o1h outAda1]

/-- **SHAPE L1.** See the module header for the full FIXED / SYMBOLIC split. -/
def localShapedCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
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
      , txInfoRedeemers := [(.Minting ownCS, localShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := localShapedRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

/-! ### AUDIT LINKS — the named projections ARE the shaped context's fields. -/

section Audit
variable (ownCS tn : ByteString) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
         (o1h : ByteString) (outAda1 : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer) (fee : Integer)

private abbrev lCtx : ScriptContext :=
  localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
    pHash pCS pTn pAda pQty dirCS plc glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee

theorem localShapedCtx_outputs :
    (lCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
      = localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1 := rfl

theorem localShapedCtx_wdrl :
    (lCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoWdrl
      = localShapedWdrl w0 w1 a0 a1 := rfl

theorem localShapedCtx_refInputs :
    (lCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs
      = [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
        , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] := rfl

theorem localShapedCtx_mint :
    (lCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint
      = mintOne ownCS tn q := rfl

end Audit

/-- The params datum SHAPE L1 publishes at reference index 0 — the `GlobalParams`
record whose `progLogicCred` the no-escape scan compares against and whose
`directoryNodeCS` the registration check uses. Naming it here (rather than in the
theorem) keeps the postcondition readable; `localShapedParams_isDatum` pins the
link. -/
def localShapedParams (dirCS plc glc slc : ByteString) : GlobalParams :=
  GlobalParams.mk dirCS (.ScriptCredential plc) (.ScriptCredential glc)
                  (.ScriptCredential slc)

/-- AUDIT: `localShapedParams` really is the inline datum of reference input 0.
This is the analogue of SHAPE G2's lesson (WSC/SHAPING-RESULTS.md §6.1): the
params record the postcondition names must be the one the validator reads
through the redeemer's own `mrParamsRefIdx`, which SHAPE L1 pins to 0. -/
theorem localShapedParams_isDatum
    (pHash pCS pTn : ByteString) (pAda pQty : Integer) (dirCS plc glc slc : ByteString) :
    (localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc).txInInfoResolved.txOutDatum
      = .OutputDatum (IsData.toData (localShapedParams dirCS plc glc slc)) := rfl

/-- Parameter evidence is unchanged from WSC/Prep/Minting900.lean (2 parameters,
`protocolParamsCS` then `mintingLogicHash`, the latter LAST — Issuance.hs:132-133,
offchain Scripts.hs:135-140). Only the third argument is shaped. -/
def localShapedInputs
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
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#prep_uplc appliedMintLocalShaped2500 programmableTokenMinting900 localShapedInputs 2500

end WSC
