/- Task V3 probe: the SHAPE DT1 and SHAPE DS1 arm obligations + vacuity probes. -/
import WSC.Shaped.MintingDelegateShaped
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

theorem DT1_arm :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = true := by blaster

def DT1_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (gen-cex: 0) (solve-result: 1) [DT1_vacuity]

theorem DS1_arm :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
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
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
      DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) = true
      := by blaster

def DS1_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
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
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    ¬ isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)

#blaster (gen-cex: 0) (solve-result: 1) [DS1_vacuity]

end WSC
