/- Task V3: attribution probe.  Which SHAPE L2 stanza is expensive? -/
import WSC.Shaped.MintingLocalShapedIdx
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- The INDEX-FREE registration postcondition at SHAPE L2: some reference input
carries `ownCS`'s directory NFT, with the registration index symbolic. -/
def L2_registration : Prop :=
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
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) →
    isSuccessful
      (appliedMintLocalIdxShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) →
    anyRefInputHasNodeNFT dirCS ownCS
      [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
      , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] = true

#blaster (timeout: 300) (gen-cex: 1) (solve-result: 0) [L2_registration]

end WSC
