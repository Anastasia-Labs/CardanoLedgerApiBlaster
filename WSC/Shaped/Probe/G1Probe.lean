/- Z2 exploration probe: P5 + vacuity at SHAPE G1, Z3 capped. Not a deliverable. -/
import WSC.Shaped.GlobalShaped
import WSC.Props.P5_NonMember
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Probe

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC.P5 (dirNodeAuthH coversCS)

def P5_G1 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      dirNodeAuthH dirCS
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 0) [P5_G1]

def vac_G1 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 600) (gen-cex: 0) (solve-result: 1) [vac_G1]

end WSC.Z2Probe
