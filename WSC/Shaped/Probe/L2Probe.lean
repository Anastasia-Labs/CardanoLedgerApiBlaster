/-
WSC/Shaped/Probe/L2Probe.lean — task V3 LOOSENING RUNG, with its measured
outcome.  SHAPE L2 (WSC/Shaped/MintingLocalShapedIdx.lean) is SHAPE L1 with the
`Local` arm's REGISTRATION reference-input index left SYMBOLIC.

Question: does the ISSUANCE policy tolerate a symbolic index here, the way it
tolerates a symbolic WITHDRAWAL index (SHAPE M2, closes in 2.1 s —
WSC/SHAPING-RESULTS.md §2.4), or is the index load-bearing the way it is for the
GLOBAL validator (SHAPE G3, `Undetermined` after 906 s on a non-empty class —
ibid. §6.2)?

Stated in G3Probe's style — `def : Prop` plus a `#blaster` COMMAND with an
explicit Z3 cap — so that a no-verdict outcome is RECORDED rather than hanging the
build.  `solve-result: 0` = "expected Valid", `solve-result: 1` = "expected
Falsified"; an `Undetermined` is reported as such.

MEASURED OUTCOME (2026-07-25, `lake build`, Z3 capped at 300 s per query):
* `noEscape` at SHAPE L2 — **`✅ Valid`**, whole module **2.2 s**;
* vacuity probe at SHAPE L2 — **`✅ Falsified`** (class non-empty);
* the REGISTRATION conjunct at the same shape — **`⚠️ Undetermined`**, cap fired,
  module wall 4 m 53 s (measured separately in `WSC/Shaped/Probe/L2Reg.lean`,
  which is why it is not in this file).

So the answer is SPLIT: for the `Local` arm the registration index is dispensable
for the NO-ESCAPE property (which is what the arm is for) and load-bearing for the
REGISTRATION property. `noEscape` at SHAPE L2 is promoted to a theorem in
WSC/Props/Shaped/P4LocalShaped.lean (`P4_local_noEscape_shapedIdx`); this file is
kept as the exploratory record.
-/
import WSC.Shaped.MintingLocalShapedIdx
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- The no-escape obligation at SHAPE L2 (index-free postcondition, so there is no
SHAPE-G2-style naming hazard). -/
def L2_noEscape : Prop :=
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
    noEscape (Credential.ScriptCredential plc) ownCS
      (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true

#blaster (timeout: 300) (gen-cex: 1) (solve-result: 0) [L2_noEscape]

/-- MANDATORY vacuity probe at SHAPE L2 — the stanza that says whether a
no-verdict above is a solver limit or an empty class. -/
def L2_vacuity : Prop :=
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
    ¬ isSuccessful
      (appliedMintLocalIdxShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [L2_vacuity]

end WSC
