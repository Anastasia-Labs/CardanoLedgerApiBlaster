-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/GlobalShapedP1Agg.lean — **SHAPE T4 / T5**: SHAPE T1 grown along the
dimension that matters most for P1's MEANING — TWO mini-ledger inputs, so
containment must AGGREGATE (task V1 step 4).

WHY THIS SHAPE IS THE INTERESTING GROWTH STEP. With one contributing input,
`pvalueFromCred` (ProgrammableLogicBase.hs:392-484) finishes in its PHASE 2
`goRest` and produces the input value by `ptail # (pasMap # firstVd)` — a
positional drop of the ada entry, no arithmetic at all. With TWO contributing
inputs it enters PHASE 3 `goBuiltin` (:446-458), which

  * converts each input value with the CIP-153 builtin `punValueData`,
  * merges them with the builtin `punionValue`, and
  * bridges back to raw pairs with
    `pasMap # (pvalueData # (pinsertCoin # "" # "" # 0 # acc))`

so the mini-ledger input total is now the output of REAL builtin ADDITION on
symbolic quantities. That is exactly the content of ARCHITECTURE.md §3-P1's lemma
L1.3 (`valueFromCred` counts EVERY base input), which
`WSC/Props/P1_Transfer.lean` records as STATED-NOT-PROVED and calls "the largest
single item". SHAPE T4 makes the bytecode discharge it on this shape.

FIXED — as SHAPE T1 (WSC/Shaped/GlobalShapedP1.lean) except:
* exactly 3 inputs: index 0 AND index 1 both at the mini-ledger base credential
  `ScriptCredential plc`, each with staking credential
  `StakingHash (PubKeyCredential owner)` (`owner` = the sole signatory), index 2
  at `PubKeyCredential ext` (the external source);
* still exactly 2 outputs (base, then the escape route) and one policy/token.

SYMBOLIC — additionally `qIn0` and `qIn1` INDEPENDENTLY, plus their ada amounts.
The postcondition's `inAtBase` is their SUM, so a shape that reused one variable
for both would not test aggregation.

SHAPE T5 = SHAPE T4 with the nonzero symbolic mint of SHAPE T2 (redeemer carries
one `Member` mint proof).
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

/-- The SECOND mini-ledger input (`TxOutRef ⟨"",1⟩`), at the same base
credential as the first. -/
def p1ShapedBaseIn2 (plc owner : ByteString) (inAda : Integer)
    (cs tn : ByteString) (qIn : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.ScriptCredential plc, some (.StakingHash (.PubKeyCredential owner))⟩
   , txOutValue := adaPlusOne inAda cs tn qIn
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- The external input, moved to `TxOutRef ⟨"",2⟩` for SHAPE T4/T5. -/
def p1ShapedExtIn2 (ext : ByteString) (in2Ada : Integer)
    (cs tn : ByteString) (qIn2 : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 2⟩,
   { txOutAddress := ⟨.PubKeyCredential ext, none⟩
   , txOutValue := adaPlusOne in2Ada cs tn qIn2
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- **SHAPE T4** — two mini-ledger inputs, empty mint. -/
def p1ShapedAggCtx
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
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
          [ p1ShapedBaseIn plc owner inAda0 cs tn qIn0
          , p1ShapedBaseIn2 plc owner inAda1 cs tn qIn1
          , p1ShapedExtIn2 ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda cs tn qOut
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

def p1ShapedAggInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
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
      (p1ShapedAggCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

/-- **SHAPE T5** — SHAPE T4 plus the nonzero symbolic mint of SHAPE T2. -/
def p1ShapedAggMintCtx
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
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
          [ p1ShapedBaseIn plc owner inAda0 cs tn qIn0
          , p1ShapedBaseIn2 plc owner inAda1 cs tn qIn1
          , p1ShapedExtIn2 ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda cs tn qOut
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

def p1ShapedAggMintInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
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
      (p1ShapedAggMintCtx cs tn q plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

end WSC
