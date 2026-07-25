/-
WSC/Props/Shaped/P1ShapedR.lean — **P1 (containment) re-proved over the
NODE-REALIZABLE re-cut SHAPES T1R / T2R / T6R / T7R** (task C1).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P1Shaped.lean` proves P1 over SHAPES T1/T2/T6/T7. Those
theorems are TRUE and unchanged — but `WSC/Props/Shaped/ShapeRealizability.lean`
proves SHAPE T1's class is **EMPTY UNCONDITIONALLY** (`t1_class_is_empty`): the
shape SPENDS an input at `ScriptCredential plc`, so `LR_SPEND_RUNS_VALIDATOR`
plus `LR_CTX` demand a `Spending` entry in a redeemer map that holds exactly one
`Rewarding` entry. T2/T6/T7 share that skeleton and are empty for the same reason
(and, like T1, a second time by the withdrawal route under `RedeemerCoverageAllPlutus`).

This module re-states and re-proves the same four P1 obligations over the re-cut
shapes of `WSC/Shaped/GlobalShapedR.lean` §3-§6, whose redeemer maps cover every
script witness the transaction needs, and whose classes are proved NON-EMPTY in
`WSC/Props/Shaped/GlobalRealizability.lean`.

WHAT CHANGED, EXHAUSTIVELY — the redeemer map, and nothing else:
* **T1R** = T1 with `txInfoRedeemers` = `[(Spending ⟨"",0⟩, I rBase),
  (Rewarding w0, TransferAct [1] [1] [] 0), (Rewarding w1, I rTls)]` (3 entries,
  the measured size of the real `base-spend-transfer-tx` golden);
* **T2R** = T2 with the same three plus `(Minting cs, I rMint)` in second
  position (4 entries — a nonzero mint field is a needed script, and
  `validMintValue` forces every mint quantity ≠ 0 so that entry is never an
  EXTRA redeemer);
* **T6R** = T6 with T1R's map, and **T7R** = T7 with T2R's map.
The inputs (incl. the external pubkey input), the reference inputs, the outputs
(incl. the pubkey ESCAPE output), the mint, the two-script withdrawal map, the
signatory, the redeemer CONTENT and the budget (4400) are untouched. In
particular the two design properties P1's own header insists on are preserved:
**a non-base input and a non-base output**, so `isBalanced` alone gives only
`qIn + qIn2 + mint = qOut + qEsc` and the inequality still has to be earned from
the bytecode.

WHY THE WITHDRAWAL MAP STAYS TWO-SCRIPT (lever (i) does not apply here). SHAPE
T1's redeemer has `transferWdrlIdxs = [1]`, and the transfer walk's positive-proof
branch requires `directoryNodeDatumFTransferLogicScript #== pfstBuiltin # (phead #
(pdropList # 1 # withdrawalEntries))` (ProgrammableLogicBase.hs:913-915). The
node datum's `transferLogicScript` is a `ScriptCredential`, so withdrawal entry 1
MUST be a script credential — making it a pubkey entry would make the accepting
branch of this very shape unreachable. Both script withdrawals therefore get
`Rewarding` redeemer entries.

SCOPE. Every bound of `WSC/Props/Shaped/P1Shaped.lean` (budget 4400 via
`LR_BUDGET_global`; the SHAPE T1/T2 FIXED/SYMBOLIC split; PATH A only — Bound 2b,
with SHAPE T3's prep still blocked by Blaster defect D6; one proof index —
Bound 2c; and the non-exemption hypothesis `coveringNodeExists … = false` —
Bound 3, whose trust surface is DirWF's missing partition conjunct) applies here
word for word. This module changes the CLASS, not the strength.

MEASURED (this task): all four `✅ Valid`; witness K unchanged at 2603 (T1R),
3572 (T2R), 3150 (T6R), 3572 (T7R) — the transfer path never dereferences
`txInfoRedeemers`, so redeemer coverage costs zero CEK steps.
-/
import WSC.Shaped.GlobalShapedP1RPrep
import WSC.Shaped.GlobalShapedP1RMintPrep
import WSC.Shaped.GlobalShapedP1ROutPrep
import WSC.Shaped.GlobalShapedP1ROutMintPrep
import WSC.Props.Shaped.P1Shaped
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): expected `sorry`s.
set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## §1 — P1 over SHAPE T1R (pure transfer, PATH A) -/

/-- **P1 (containment), SIGNED form, over the REALIZABLE SHAPE T1R.** -/
def P1R_T1_stmt : Prop :=
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
    Model.coveringNodeExists dirCS cs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = false →
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
theorem P1R_T1 : P1R_T1_stmt := by blaster

/-! ## §2 — P1 over SHAPE T2R (nonzero symbolic mint — the SIGNED form bites) -/

def P1R_T2_stmt : Prop :=
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
    Model.coveringNodeExists dirCS cs
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = false →
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
theorem P1R_T2 : P1R_T2_stmt := by blaster

/-! ## §3 — P1 over SHAPE T6R (containment must AGGREGATE over outputs) -/

def P1R_T6_stmt : Prop :=
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
    Model.coveringNodeExists dirCS cs
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = false →
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
theorem P1R_T6 : P1R_T6_stmt := by blaster

/-! ## §3b — P1 over SHAPE T7R (aggregation AND mint: the strongest P1 form) -/

def P1R_T7_stmt : Prop :=
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
    Model.coveringNodeExists dirCS cs
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = false →
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
theorem P1R_T7 : P1R_T7_stmt := by blaster

/-- **MANDATORY VACUITY PROBE AT SHAPE T7R.** Expected: `Falsified`. -/
def P1R_T7_vacuity_probe : Prop :=
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
    ¬ isSuccessful
      (appliedGlobalShapedT7R.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rMint rTls fee)

#blaster (gen-cex: 0) (solve-result: 1) [P1R_T7_vacuity_probe]

/-! ## §4 — Polarity controls (ADDENDUM E9): the full control set, re-run -/

/-- Negative control over SHAPE T1R (≡ the contrapositive at this shape; the
INDEPENDENT evidence is `P1RShapedWitness.exec_rejects_escape`). -/
def P1R_T1_negative_control_stmt : Prop :=
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
    Model.coveringNodeExists dirCS cs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls
        fee).scriptContextTxInfo.txInfoReferenceInputs = false →
    ¬ (Model.outSum (.ScriptCredential plc) cs tn
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
              fee).scriptContextTxInfo.txInfoMint) →
    isUnsuccessful
      (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

theorem P1R_T1_negative_control : P1R_T1_negative_control_stmt := by blaster

/-- Tightness stanza at SHAPE T1R. Expected: `Falsified`. -/
def P1R_T1_tightness : Prop :=
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
    isSuccessful
      (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
    ¬ (Model.outSum (.ScriptCredential plc) cs tn
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
              fee).scriptContextTxInfo.txInfoMint)

#blaster (gen-cex: 0) (solve-result: 1) [P1R_T1_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE T1R AND ITS OWN TERM.** Expected:
`Falsified`. -/
def P1R_T1_vacuity_probe : Prop :=
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
    ¬ isSuccessful
      (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

#blaster (gen-cex: 0) (solve-result: 1) [P1R_T1_vacuity_probe]

/-- **MANDATORY VACUITY PROBE AT SHAPE T2R.** Expected: `Falsified`. -/
def P1R_T2_vacuity_probe : Prop :=
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
    ¬ isSuccessful
      (appliedGlobalShapedT2R.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee)

#blaster (gen-cex: 0) (solve-result: 1) [P1R_T2_vacuity_probe]

/-- **MANDATORY VACUITY PROBE AT SHAPE T6R.** Expected: `Falsified`. -/
def P1R_T6_vacuity_probe : Prop :=
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
    ¬ isSuccessful
      (appliedGlobalShapedT6R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee)

#blaster (gen-cex: 0) (solve-result: 1) [P1R_T6_vacuity_probe]

/-! ## §5 — CONCRETE witnesses of exactly SHAPES T1R / T2R / T6R

`WSC/Props/Shaped/P1Shaped.lean`'s witness leaf values, unchanged, with the
re-cut redeemer map (`rBase = 77`, `rMint = 99`, `rTls = 88` — arbitrary values
in the symbolic slots). No SMT anywhere in this section. -/

namespace P1RShapedWitness

set_option maxRecDepth 1000000

open P1ShapedWitness (ppCS isHaltB isHaltB_sound)

/-- **SHAPE T1R, accepting.** `P1ShapedWitness.ctxOk`'s leaves: 5 in and 5 out at
the mini-ledger, an external pubkey input of 4 and an ESCAPE output of **4** (so
the escape route is non-empty in an accepting context). -/
def ctxOk : ScriptContext :=
  p1RShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 5
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 88
    50

/-- **SHAPE T1R, ESCAPING — the excluded case.** 5 in from the mini-ledger, only
3 out; the missing 2 land in the pubkey output (`qEsc = 6`). -/
def ctxEscape : ScriptContext :=
  p1RShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 3
    (ByteString.mk "DEST") 100 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 88
    50

/-- **SHAPE T2R, BURN — the `mintPos` counterexample, re-cut.** `q = −4`: 5 in
from the mini-ledger, 4 burned, 1 at the mini-ledger output. -/
def ctxBurn : ScriptContext :=
  p1RShapedMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 1
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 99 88
    50

/-- **SHAPE T6R, accepting, requirement met only by BOTH outputs together**:
5 from the mini-ledger, 3 + 2 at the two mini-ledger outputs, 4 escaping. -/
def ctxOut : ScriptContext :=
  p1ROutCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 3 60 2
    (ByteString.mk "DEST") 90 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 88
    50

/-- **SHAPE T7R, burn**: 5 in from the mini-ledger, 4 burned, and 1 + 1 = 2 at
the two mini-ledger outputs (the signed requirement is 1). -/
def ctxOutBurn : ScriptContext :=
  p1ROutMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 1 60 1
    (ByteString.mk "DEST") 90 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 99 88
    50

/-! ### The witnesses satisfy the theorems' hypotheses IN FULL -/

theorem ctxOk_valid : validRewardingContext ctxOk = true := by native_decide
theorem ctxEscape_valid : validRewardingContext ctxEscape = true := by native_decide
theorem ctxBurn_valid : validRewardingContext ctxBurn = true := by native_decide
theorem ctxOut_valid : validRewardingContext ctxOut = true := by native_decide
theorem ctxOutBurn_valid : validRewardingContext ctxOutBurn = true := by native_decide

theorem ctxOk_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxOk.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

theorem ctxBurn_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxBurn.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

/-! ### The ground-truth quantities, evaluated -/

theorem ctxOk_quantities :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOk.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOk.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxOk.scriptContextTxInfo.txInfoMint = 0 := by native_decide

/-- **THE ESCAPE ROUTE IS STILL REAL AT THE REALIZABLE CUT.** -/
theorem ctxEscape_quantities :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxEscape.scriptContextTxInfo.txInfoOutputs = 3
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxEscape.scriptContextTxInfo.txInfoInputs = 5 := by native_decide

/-- The AGGREGATION is genuine at SHAPE T6R: neither mini-ledger output alone
meets the requirement (3 < 5 and 2 < 5); their sum does. -/
theorem ctxOut_aggregation_is_genuine :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOut.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOut.scriptContextTxInfo.txInfoInputs = 5 := by native_decide

/-! ### NON-VACUITY, EXECUTABLE: the real bytecode accepts -/

/-- **NON-VACUITY, SHAPE T1R.** -/
theorem exec_accepts_T1R_at_4400 :
    isSuccessful
      (appliedGlobalShapedT1R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK")
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
        (ByteString.mk "EXT") 100 4
        150 5
        (ByteString.mk "DEST") 100 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, SHAPE T2R** (the burn witness — also the `mintPos`
refutation). -/
theorem exec_accepts_T2R_burn_at_4400 :
    isSuccessful
      (appliedGlobalShapedT2R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
        (ByteString.mk "EXT") 100 4
        150 1
        (ByteString.mk "DEST") 100 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 99 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, SHAPE T6R.** -/
theorem exec_accepts_T6R_at_4400 :
    isSuccessful
      (appliedGlobalShapedT6R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK")
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
        (ByteString.mk "EXT") 100 4
        100 3 60 2
        (ByteString.mk "DEST") 90 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, SHAPE T7R** (the burn witness). -/
theorem exec_accepts_T7R_burn_at_4400 :
    isSuccessful
      (appliedGlobalShapedT7R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
        (ByteString.mk "EXT") 100 4
        100 1 60 1
        (ByteString.mk "DEST") 90 3
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 99 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED CASE, EXECUTABLE.** `ctxEscape` is `validRewardingContext`,
redeemer-covered, and moves 2 units of a registered policy out of the
mini-ledger; the real compiled bytecode REJECTS it with 4400 steps available. -/
theorem exec_rejects_escape :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxEscape) 4400) = false := by
  native_decide

/-- **EXACT STEP COUNTS, UNCHANGED BY THE RE-CUT: T1R K = 2603, T2R K = 3572,
T6R K = 3150** — identical to SHAPES T1/T2/T6 (`K_T1_is_2603`, `K_T2_is_3572`,
`K_T6_is_3150`). Budget 4400; headroom 828 over the most expensive. -/
theorem K_T1R_is_2603 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 2603) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 2602) = false := by
  native_decide

theorem K_T2R_is_3572 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxBurn) 3572) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxBurn) 3571) = false := by
  native_decide

theorem K_T7R_is_3572 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOutBurn) 3572) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOutBurn) 3571) = false := by
  native_decide

theorem K_T6R_is_3150 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOut) 3150) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOut) 3149) = false := by
  native_decide

/-- **ARCHITECTURE.md §3-P1's `mintPos` FORM IS REFUTED AT THE REALIZABLE CUT
TOO.** On the burn witness — accepted by the real CEK, ledger-legal,
redeemer-covered, no covering node — the SIGNED requirement is met (`1 ≥ 5 − 4`)
and the `mintPos` requirement is not (`1 ≥ 5 + 0` is false). -/
theorem mintPos_form_REFUTED :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxBurn.scriptContextTxInfo.txInfoOutputs = 1
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxBurn.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxBurn.scriptContextTxInfo.txInfoMint = -4
    ∧ Model.mintPosOf (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxBurn.scriptContextTxInfo.txInfoMint = 0 := by native_decide

/-- Source-model cross-check on the four re-cut witnesses (four more
differential-test vectors for `globalModel_faithful`, and evidence that the
source model is insensitive to the redeemer map exactly as the bytecode is). -/
theorem model_agrees_on_witnesses :
    Model.globalModel ppCS ctxOk = true
    ∧ Model.globalModel ppCS ctxEscape = false
    ∧ Model.globalModel ppCS ctxBurn = true
    ∧ Model.globalModel ppCS ctxOut = true
    ∧ Model.globalModel ppCS ctxOutBurn = true := by native_decide

end P1RShapedWitness

end WSC
