/-
WSC/Shaped/MintingDelegateShaped.lean — SHAPED preps of the production issuance
policy on its two DELEGATING custody arms, at CEK step budget **2500** (task V3
rungs 2 and 3):

* **SHAPE DT1** — the `DelegateTransfer` arm (Issuance.hs:200-219);
* **SHAPE DS1** — the `DelegateSeize` arm (Issuance.hs:221-245).

Both are SHAPE L1's skeleton (WSC/Shaped/MintingLocalShaped.lean) with the
redeemer replaced, and both reuse L1's reference inputs, outputs and withdrawal
map verbatim. That is deliberate: the three arms then differ in exactly ONE
dimension — the redeemer constructor — so the four-way-disjunction story reads as
"same transaction skeleton, four different custody claims", and the arm-by-arm
theorems are directly comparable.

════════════════════════════════════════════════════════════════════════════
SHAPE DT1 — `DelegateTransfer 0 0 1 1`
════════════════════════════════════════════════════════════════════════════
FIXED, beyond everything SHAPE L1 fixes (see that module's header — the
skeleton is identical): the redeemer is `DelegateTransfer
{ mrMintingLogicWdrlIdx = 0, mrParamsRefIdx = 0, mrNodeRefIdx = 1,
  mrGlobalWdrlIdx = 1 }`, constructor tag 1 (Issuance.hs:88-90), field order
Issuance.hs:71-76.

WHAT THE ARM CHECKS (Issuance.hs:213-219): C1 at withdrawal index 0,
`regByRefOk` — the directory NFT named `ownCS` on the reference input at index 1,
by REFERENCE INPUT ONLY (F-1, Issuance.hs:204-206) — and `globalInvoked`, the
credential of withdrawal entry 1 equalling the params datum's `globalLogicCred`.

NOT TRUE BY CONSTRUCTION. The withdrawal map's two script hashes `w0`, `w1` are
free and `validMintingContext` constrains them only to be sorted, while the
params datum's `glc` is a THIRD free variable; so both "the minting-logic
credential is at index 0" and "the GLOBAL credential is at index 1" have to be
earned. The registration node's `nCS`/`nTn`/`nQty` are free and different from
`dirCS`/`ownCS`, and the params node's `pCS` is different from the script
parameter `ppCS`, exactly as in SHAPE L1.

WHAT DT1 DOES *NOT* GIVE YOU. `DelegateTransferOk` proves the global transfer
validator RUNS; it does not prove what that validator then enforces. The custody
content of this arm is therefore exactly the strength of P1, which is NOT proved
at UPLC (WSC/Props/P1_Transfer.lean OBLIGATION STATUS). This is why the `Local`
arm, not this one, is where the no-escape guarantee actually becomes a theorem.

════════════════════════════════════════════════════════════════════════════
SHAPE DS1 — `DelegateSeize 0 0 1 1`, with a TWO-ENTRY redeemer map
════════════════════════════════════════════════════════════════════════════
FIXED, beyond SHAPE L1's skeleton: the redeemer is `DelegateSeize
{ mrMintingLogicWdrlIdx = 0, mrParamsRefIdx = 0, mrNodeRefIdx = 1,
  mrSeizeRedeemerIdx = 1 }`, constructor tag 2 (Issuance.hs:88-90); and the
redeemer map has TWO entries — `(Minting ownCS, <this redeemer>)` at index 0 and
`(Rewarding (ScriptCredential sCred), SeizeAct sIdx [] 0 0 0 0)` at index 1.

`sCred` (the seize script hash the transaction claims) and **`sIdx` (the
`SeizeAct`'s own `plgrDirectoryNodeIdx`) are FREE variables.** Freeing `sIdx` is
the point of this shape: the arm's whole job is to bind the seize's scope to
`ownCS`'s directory node by requiring `pdirectoryNodeIdx #== pfromData
nodeRefIdx` (Issuance.hs:238), and had the shape pinned `sIdx = 1` that conjunct
would have been `rfl`-true and the theorem would have certified nothing about
scope binding.

**THIS IS THE FIRST SHAPED THEOREM IN THE TREE WITH A MULTI-ENTRY REDEEMER MAP,
and it is a live test of the D1 fix.** WSC/Props/Shaped/P4Shaped.lean's header
says "DEFECT D1 STILL APPLIES … a shaped theorem over a 2-entry redeemer map
would hit D1 head on". That note is now STALE: CLAB's `ltScriptPurpose`
(CardanoLedgerApi/V3/Contexts.lean:66-120) has since been corrected to the
ledger's emitted order `Spending < Minting < Certifying < Rewarding < Voting <
Proposing`, so `[Minting …, Rewarding …]` is sorted and `validRedeemerMap`
accepts it. SHAPE DS1 exercises that fix; under the pre-fix order this shape
would have been ledger-UNSATISFIABLE and every theorem over it vacuous — which is
exactly why its vacuity probe and concrete witness are load-bearing here and not
a formality.
-/
import WSC.Shaped.MintingLocalShaped
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

/-! ## SHAPE DT1 — the `DelegateTransfer` arm -/

/-- SHAPE DT1's redeemer: `DelegateTransfer 0 0 1 1`. -/
def dtShapedRedeemer : Data :=
  IsData.toData (MintRedeemer.DelegateTransfer 0 0 1 1)

/-- AUDIT: the shaped redeemer really is `Constr 1 [I 0, I 0, I 1, I 1]`. -/
theorem dtShapedRedeemer_eq :
    dtShapedRedeemer = Data.Constr 1 [Data.I 0, Data.I 0, Data.I 1, Data.I 1] := by
  native_decide

/-- **SHAPE DT1.** SHAPE L1's skeleton with the `DelegateTransfer` redeemer. -/
def dtShapedCtx
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
      , txInfoRedeemers := [(.Minting ownCS, dtShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := dtShapedRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

def dtShapedInputs
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
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#prep_uplc appliedMintDTShaped2500 programmableTokenMinting900 dtShapedInputs 2500

/-! ## SHAPE DS1 — the `DelegateSeize` arm, with a two-entry redeemer map -/

/-- SHAPE DS1's minting redeemer: `DelegateSeize 0 0 1 1`. -/
def dsShapedRedeemer : Data :=
  IsData.toData (MintRedeemer.DelegateSeize 0 0 1 1)

/-- AUDIT: `Constr 2 [I 0, I 0, I 1, I 1]`. -/
theorem dsShapedRedeemer_eq :
    dsShapedRedeemer = Data.Constr 2 [Data.I 0, Data.I 0, Data.I 1, Data.I 1] := by
  native_decide

/-- The `SeizeAct` redeemer carried by the second redeemer-map entry. Its
`plgrDirectoryNodeIdx` is the FREE leaf `sIdx`; the five remaining fields are
fixed to 0 (the seize validator's `pinputIdxs`/`plengthInputIdxs` are no longer
read — WSC/Redeemer.lean's fidelity note — and none of the others is read by the
ISSUANCE policy, which only matches the constructor and reads field 0). -/
def dsSeizeRedeemer (sIdx : Integer) : Data :=
  IsData.toData (PLGRedeemer.SeizeAct sIdx [] 0 0 0 0)

/-- AUDIT: `Constr 1 [I sIdx, List [], I 0, I 0, I 0, I 0]`. -/
theorem dsSeizeRedeemer_eq (sIdx : Integer) :
    dsSeizeRedeemer sIdx
      = Data.Constr 1 [Data.I sIdx, Data.List [], Data.I 0, Data.I 0, Data.I 0, Data.I 0] := rfl

/-- SHAPE DS1's redeemer map: the own `Minting` entry then a `Rewarding` entry
carrying the `SeizeAct`. Sorted because `Minting < Rewarding` in CLAB's corrected
`ltScriptPurpose` (CardanoLedgerApi/V3/Contexts.lean:101-120). -/
def dsShapedRedeemerMap (ownCS sCred : ByteString) (sIdx : Integer)
    : List (CardanoLedgerApi.V3.ScriptPurpose × Data) :=
  [ (.Minting ownCS, dsShapedRedeemer)
  , (.Rewarding (.ScriptCredential sCred), dsSeizeRedeemer sIdx) ]

/-- **SHAPE DS1.** SHAPE L1's skeleton with the `DelegateSeize` redeemer and a
two-entry redeemer map. -/
def dsShapedCtx
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
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
      , txInfoRedeemers := dsShapedRedeemerMap ownCS sCred sIdx
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := dsShapedRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

def dsShapedInputs
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
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)

#prep_uplc appliedMintDSShaped2500 programmableTokenMinting900 dsShapedInputs 2500

end WSC
