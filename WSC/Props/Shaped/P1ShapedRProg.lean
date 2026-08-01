/-
WSC/Props/Shaped/P1ShapedRProg.lean — **INTERFACE, NOT A NEW RESULT.**

The four PUBLISHED shaped P1 theorems `WSC.P1R_T1` / `P1R_T2` / `P1R_T6` /
`P1R_T7` (`WSC/Props/Shaped/P1ShapedR.lean:140,:185,:233,:282`) state their
exemption hypothesis as `Model.coveringNodeExists … = false` — the OLD 3-field
node reader, which is DEFECT 2's predicate. This module restates each of them over
the SHARED, REPAIRED guard `WSC.Model.isProgrammable` (`WSC/Model/Registry.lean`),
so that a caller working in the new vocabulary never has to touch the old one.

**NOTHING IS RE-PROVED AND NO SOLVER RUNS HERE.** Each wrapper is a KERNEL step on
top of the existing theorem, via
`WSC.Model.coveringNodeExists_false_of_exemptible_false`. That is the migration
plan's governing rule: the four `by blaster (timeout: 1500)` proofs are NOT re-run
at any stage, because this family has a MEASURED 16x solver variance and re-running
it would risk turning a `✅ Valid` into a `⚠️ Undetermined` for no gain.

**THESE ARE STRICTLY WEAKER THEOREMS AND MUST BE LABELLED AS SUCH.**
`isProgrammable = true` is a STRONGER hypothesis than `coveringNodeExists = false`
(it also excludes ada, and it excludes the truncated covering nodes the bytecode
accepts), so each `*_prog` theorem says LESS than its `P1R_*` original. The
originals remain the published results. Quote `WSC.P1R_T1`, not `P1R_T1_prog`,
when stating what was proved against the bytecode.

WHY THE ORIGINALS ARE STILL TRUE AND STILL UNTOUCHED by the unshaped repair: at
all four shapes the two predicates COINCIDE by `rfl` for all ~40 leaves
(`WSC.Benchmark.exemptible_eq_covering_T{1,2,6,7}R`), because `p1ShapedNode`
(`WSC/Shaped/GlobalShapedP1.lean:233`) builds the node datum as
`IsData.toData (DirectorySetNode.mk …)` — FIVE FIELDS BY CONSTRUCTION. So over
these shapes the wrappers lose nothing except the ada slot, where the shaped
statements are vacuous anyway (`Shape.adaPlusOne` is ledger-invalid at
`cs = adaSymbol`, `WSC.Benchmark.shaped_invalid_at_ada_T*R`).

AXIOM PROFILE — `[propext, sorryAx, Classical.choice, Quot.sound]`, IDENTICAL to
the originals'. The `sorryAx` is `blaster`'s own `admit` and is INHERITED, not
introduced here; measured on the unmodified tree,
`#print axioms WSC.P1R_T1` reports exactly the same four. No wrapper adds an axiom.
-/
import WSC.Props.Shaped.P1ShapedR
import WSC.Model.Registry

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (CurrencySymbol validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- SHAPE T1R, restated over the SHARED `Model.isProgrammable` guard.
STRICTLY WEAKER than `WSC.P1R_T1` (stronger hypothesis). Interface, not a result. -/
def P1R_T1_prog_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
    Model.isProgrammable dirCS cs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = true →
    isSuccessful
      (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
            fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
              fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
              fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER THE REALIZABLE SHAPE T1R — PROVED AT UPLC AGAINST THE PRODUCTION
BYTECODE.** Identical statement to `WSC.P1_T1`, over a shape class that is
inhabited by transactions a node would accept (`WSC.t1R_realizable`) rather than
by the empty class `t1_class_is_empty` exhibits. Over SHAPE T1R the mint is
empty, so this is the pure-transfer case `outAtBase ≥ inAtBase`. -/
theorem P1R_T1_prog : P1R_T1_prog_stmt := by
  intro ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash
        nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0
        a1 rBase rTls fee
        hv hprog hacc
  exact P1R_T1 ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
    dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash
    nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0
    a1 rBase rTls fee
    hv (Model.coveringNodeExists_false_of_exemptible_false
      (Model.exemptible_false_of_isProgrammable hprog)) hacc

/-- SHAPE T2R, restated over the SHARED `Model.isProgrammable` guard.
STRICTLY WEAKER than `WSC.P1R_T2` (stronger hypothesis). Interface, not a result. -/
def P1R_T2_prog_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer),
    validRewardingContext
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) →
    Model.isProgrammable dirCS cs
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = true →
    isSuccessful
      (appliedGlobalShapedT2R.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
            fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
              fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
              fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER THE REALIZABLE SHAPE T2R — PROVED AT UPLC.** `q` is free and its
SIGN is unconstrained, so mint and burn are covered at once. -/
theorem P1R_T2_prog : P1R_T2_prog_stmt := by
  intro ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda
        qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1
        a0 a1 rBase rMint rTls fee
        hv hprog hacc
  exact P1R_T2 ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda
    qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1
    a0 a1 rBase rMint rTls fee
    hv (Model.coveringNodeExists_false_of_exemptible_false
      (Model.exemptible_false_of_isProgrammable hprog)) hacc

/-- SHAPE T6R, restated over the SHARED `Model.isProgrammable` guard.
STRICTLY WEAKER than `WSC.P1R_T6` (stronger hypothesis). Interface, not a result. -/
def P1R_T6_prog_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
    Model.isProgrammable dirCS cs
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = true →
    isSuccessful
      (appliedGlobalShapedT6R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
            fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
              fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
              fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER THE REALIZABLE SHAPE T6R — PROVED AT UPLC.** The mini-ledger
requirement is met by the SUM of two independently symbolic mini-ledger outputs,
so PATH A's accumulate-scan (including its early exit at
ProgrammableLogicBase.hs:605-607) has to add them up. -/
theorem P1R_T6_prog : P1R_T6_prog_stmt := by
  intro ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0
        outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc
        slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0
        w1 a0 a1 rBase rTls fee
        hv hprog hacc
  exact P1R_T6 ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0
    outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc
    slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0
    w1 a0 a1 rBase rTls fee
    hv (Model.coveringNodeExists_false_of_exemptible_false
      (Model.exemptible_false_of_isProgrammable hprog)) hacc

/-- SHAPE T7R, restated over the SHARED `Model.isProgrammable` guard.
STRICTLY WEAKER than `WSC.P1R_T7` (stronger hypothesis). Interface, not a result. -/
def P1R_T7_prog_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer),
    validRewardingContext
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) →
    Model.isProgrammable dirCS cs
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = true →
    isSuccessful
      (appliedGlobalShapedT7R.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rMint rTls fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
            fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
              fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
              fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER THE REALIZABLE SHAPE T7R — PROVED AT UPLC.** Two mini-ledger
outputs with independent free quantities AND a nonzero mint of unconstrained
sign: the strongest single P1 statement in the library, now over a class proved
non-empty (`WSC.t7R_realizable`). -/
theorem P1R_T7_prog : P1R_T7_prog_stmt := by
  intro ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0
        qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS
        glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rMint rTls fee
        hv hprog hacc
  exact P1R_T7 ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0
    qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS
    glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
    w0 w1 a0 a1 rBase rMint rTls fee
    hv (Model.coveringNodeExists_false_of_exemptible_false
      (Model.exemptible_false_of_isProgrammable hprog)) hacc

#print axioms WSC.P1R_T1_prog
#print axioms WSC.P1R_T2_prog
#print axioms WSC.P1R_T6_prog
#print axioms WSC.P1R_T7_prog

end WSC
