/-
WSC/Shaped/Probe/L2RProbe.lean — the SHAPE L2R measurement pass (audit **F19**).

SHAPE L2R (`WSC/Shaped/MintingLocalShapedRIdx.lean`) is SHAPE L1R with the `Local`
arm's REGISTRATION reference-input index left SYMBOLIC — i.e. SHAPE L2's loosening
over the NODE-REALIZABLE cut.

Stated in `WSC/Shaped/Probe/L2Probe.lean`'s style — `def : Prop` plus a `#blaster`
COMMAND with an EXPLICIT Z3 cap — so that a no-verdict outcome is RECORDED rather
than hanging the build. Blaster's default timeout is ∞
(`.lake/packages/Blaster/Blaster/Command/Syntax.lean:15`), which is exactly how a
loosening rung turns into an unbounded build.

`solve-result: 0` = "expected Valid", `solve-result: 1` = "expected Falsified"; an
`⚠️ Undetermined` is reported as such.
-/
import WSC.Shaped.MintingLocalShapedRIdx
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- **THE HEADLINE OBLIGATION.** `noEscape` at SHAPE L2R (index-free postcondition,
so there is no SHAPE-G2-style naming hazard). -/
def L2R_noEscape : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    noEscape (Credential.ScriptCredential plc) ownCS
      (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true

#blaster (timeout: 300) (gen-cex: 1) (solve-result: 0) [L2R_noEscape]

/-- MANDATORY vacuity probe at SHAPE L2R — the stanza that says whether a
no-verdict above is a solver limit or an EMPTY class. -/
def L2R_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [L2R_vacuity]

/-- Tightness stanza at SHAPE L2R. Expected: `Falsified`. -/
def L2R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [L2R_tightness]

/-- C1 at SHAPE L2R — the minting-logic withdrawal conjunct (Issuance.hs:150-151,
listed at :195). Measured separately because it is a DIFFERENT query from the
headline one. -/
def L2R_C1 : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    credentialInWithdrawals (Credential.ScriptCredential mlh) (localRWdrl w0 a0)

#blaster (timeout: 300) (gen-cex: 1) (solve-result: 0) [L2R_C1]

/-- Negative control at SHAPE L2R (≡ the contrapositive of the headline). -/
def L2R_negative_control : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true) →
    isUnsuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee)

#blaster (timeout: 300) (gen-cex: 1) (solve-result: 0) [L2R_negative_control]

end WSC
