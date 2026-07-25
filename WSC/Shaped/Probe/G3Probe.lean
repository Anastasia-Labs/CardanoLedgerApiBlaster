/- Z2 loosening rung: index-free P5 at SHAPE G3 (node index symbolic, params index pinned). -/
import WSC.Shaped.GlobalShapedIdx
import WSC.Props.P5_NonMember
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Probe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC.P5 (hasCoveringNode)

def P5_G3 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer),
    validRewardingContext
      (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee 0 nIdx) →
    isSuccessful
      (appliedGlobalShapedNIdx1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee nIdx) →
      hasCoveringNode dirCS cs
        (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
          dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
          0 nIdx).scriptContextTxInfo.txInfoReferenceInputs = true

#blaster (timeout: 900) (gen-cex: 1) (solve-result: 0) [P5_G3]

def vac_G3 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer),
    validRewardingContext
      (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee 0 nIdx) →
    ¬ isSuccessful
      (appliedGlobalShapedNIdx1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee nIdx)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [vac_G3]

end WSC.Z2Probe
