-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Shaped/GlobalShapedP1Out.lean — **SHAPE T6 / T7**: SHAPE T1 / T2 grown along
the OUTPUT-side aggregation dimension — TWO mini-ledger outputs, so containment
must AGGREGATE across them (task V1 step 4).

WHY THIS DIMENSION, AND NOT THE INPUT SIDE. The task's preferred growth step was
two mini-ledger INPUTS. That is UNREACHABLE with the current substrate: two
contributing inputs put `pvalueFromCred` into its PHASE 3 `goBuiltin`
(ProgrammableLogicBase.hs:446-458), whose accumulator is the CIP-153 builtin
`punionValue`, and `#prep_uplc` then emits a KERNEL-ILL-TYPED term. Measured,
reproducible, and recorded in full in WSC/status-fragments/V1-P1-shaped.md
(`WSC/Shaped/Probe/T4PrepFAILS.lean` is kept as the failing probe). Note that
`punionValue` always sums the LOVELACE entry of two canonical values, so the
overflow guard that triggers the defect fires for EVERY two-contributing-input
shape, not just for shapes that aggregate one policy.

The output side aggregates with plain Integer addition inside PATH A's
`hasAtLeastAssetInProgOutputs` (:604-618) — `currentQty + passetQtyInValue …`, no
builtin — so it preps, and it tests exactly the property that matters: that the
validator adds up ALL mini-ledger outputs rather than accepting on the strength of
one of them, and that its EARLY EXIT (`currentQty #>= requiredQty` tested before
the list is destructured, :605-607) cannot under-count.

FIXED — as SHAPE T1 (WSC/Shaped/GlobalShapedP1.lean) except:
* exactly 3 outputs: index 0 AND index 1 both at the mini-ledger base credential
  `ScriptCredential plc`, index 2 at `PubKeyCredential dest` (the escape route);
* still exactly 2 inputs (one mini-ledger, one external) and one policy/token.

SYMBOLIC — additionally `qOut0` and `qOut1` INDEPENDENTLY, plus their ada
amounts. The postcondition's `outAtBase` is their SUM.

SHAPE T7 = SHAPE T6 with the nonzero symbolic mint of SHAPE T2.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.GlobalImport
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

/-- **SHAPE T6** — two mini-ledger outputs, empty mint. -/
def p1ShapedOutCtx
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn plc owner inAda cs tn qIn
          , p1ShapedExtIn ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda0 cs tn qOut0
          , p1ShapedBaseOut plc outAda1 cs tn qOut1
          , p1ShapedEscOut dest escAda cs tn qEsc ]
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), p1ShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1ShapedOutInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

/-- **SHAPE T7** — SHAPE T6 plus the nonzero symbolic mint of SHAPE T2. -/
def p1ShapedOutMintCtx
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn plc owner inAda cs tn qIn
          , p1ShapedExtIn ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda0 cs tn qOut0
          , p1ShapedBaseOut plc outAda1 cs tn qOut1
          , p1ShapedEscOut dest escAda cs tn qEsc ]
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), p1ShapedRedeemerMint)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemerMint
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1ShapedOutMintInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

end WSC
