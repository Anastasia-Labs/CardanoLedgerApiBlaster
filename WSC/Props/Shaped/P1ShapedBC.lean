/-
WSC/Props/Shaped/P1ShapedBC.lean — **P1 (containment) over the NODE-REALIZABLE
re-cuts SHAPE T3R (dispatch PATHS B/C) and SHAPE T4R (input-side builtin
accumulation)** (task H2).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE ADDS, AND WHAT IT DOES NOT
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P1ShapedR.lean` proves P1 over SHAPES T1R/T2R/T6R/T7R/T8R.
Every one of them carries a SINGLE-asset expected value, so every one takes
containment **PATH A** (the single-asset accumulate-scan,
ProgrammableLogicBase.hs:567-593). ARCHITECTURE.md Tier 3.1 asks for all three
dispatch paths.

This module states and proves P1 over two shapes that leave PATH A:

* **SHAPE T3R** — two token names per policy, so the dispatch guard at
  :655-656 is false and `checkWholesaleThenBuiltin` runs: **PATH B** (wholesale
  `Data` equality, :628-644) falling through to **PATH C** (the CIP-153 builtin
  `pvalueContains`, :615-618). This is the first UPLC-level P1 result over
  either path, over a class proved non-empty.
* **SHAPE T4R** — two mini-ledger inputs, so `pvalueFromCred` enters its PHASE 3
  `goBuiltin` (:396-410) and the mini-ledger input total is the output of real
  CIP-153 builtin addition (`punValueData`/`punionValue`/`pinsertCoin`/
  `pvalueData`) on symbolic quantities, rather than PHASE 2's positional
  ada-drop. T4R keeps SHAPE T4's single token name, so its DISPATCH is PATH A;
  it is the INPUT-side axis.

Both shapes were unstatable until 2026-07-28 for TWO independent reasons, and
both are now gone:
1. upstream Blaster defect **D6** made `#prep_uplc` emit a kernel-ill-typed
   `Blaster.dite'` whenever a CIP-153 builtin result stayed symbolic — FIXED at
   `Lean-blaster-wsc` @ `4d320dd`; the reproductions
   `WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` are now regression tests;
2. SHAPES T3 and T4 are PRE-RE-CUT and provably unbuildable on a node (audit
   **F2**) — T3 demands 3 redeemer entries and supplies 1, T4 demands 4 and
   supplies 1. That is what `WSC/Shaped/GlobalShapedP1BC.lean` fixes, and it is
   the work this module rests on. **"D6 is fixed" was never the same thing as
   "the dispatch paths are verified"; this module is the second half.**

SCOPE, unchanged from `P1ShapedR.lean`: budget 4400 via `LR_BUDGET_global`; the
SHAPE T3/T4 FIXED/SYMBOLIC split; one transfer proof index; the non-exemption
hypothesis `coveringNodeExists … = false` whose trust surface is DirWF's missing
partition conjunct; and `PropExecFaithful` (audit F8) — theorems are on `.prop`,
witnesses and every measured K on `.exec`.

════════════════════════════════════════════════════════════════════════════
WHICH DISPATCH PATH EACH SHAPE EXERCISES — CLAIMED **AND BACKED**
════════════════════════════════════════════════════════════════════════════
"SHAPE T3R exercises PATH B/C" is a claim about the compiled program's control
flow. §5 backs it with executable witnesses instead of asserting it. In summary:

* **PATH A is NOT taken at SHAPE T3R — PROVED.** `T3R_not_path_A` exhibits TWO
  ledger-legal, redeemer-covered SHAPE-T3R contexts that the real CEK REJECTS:
  one short on `tn0` with `tn1` whole, one short on `tn1` with `tn0` whole. PATH
  A is `hasAtLeastAssetInProgOutputs` on exactly ONE `(cs, tn)` pair; whichever
  pair it were given, one of the two contexts leaves that pair whole and would
  be ACCEPTED. Both are rejected, so the run is not on PATH A. (Independently,
  the class-level reason: `validTxOutValue`,
  `CardanoLedgerApi/V1/Contexts.lean:787-802`, forces every non-ada quantity in
  every resolved input `> 0`, so `pfilterPositiveCurrencyPairs` cannot reduce the
  expected value to one token name and the :655-656 guard is false for EVERY leaf
  assignment satisfying the theorems' `validRewardingContext` hypothesis.)

* **PATH C is taken and returns True at `ctxC` — PROVED.** `T3R_pathC_is_taken`
  packages the two acceptance facts the argument needs. `ctxB` and `ctxC` are the
  SAME `ScriptContext` except for two output quantities: the mini-ledger output's
  `tn0` (5 vs 6) and the escape output's `tn0` (4 vs 3, so `isBalanced` still
  holds). `expectedProgrammableOutputValue` (`:1225-1268`) is a function of
  `ptxInfo'inputs`, `ptxInfo'referenceInputs`, `ptxInfo'mint`,
  `ptxInfo'signatories`, `ptxInfo'wdrl` and the redeemer — **`ptxInfo'outputs`
  does not appear in its definition at all**, and it is `plet`-bound before the
  containment call at `:1270-1276` — so the expected value `E` is the SAME in
  both runs. Suppose `ctxC` accepted on
  PATH B: then `E` equals `ctxC`'s mini-ledger output map, `{cs:{tn0:6,tn1:5}}`.
  At `ctxB` the output map is `{cs:{tn0:5,tn1:5}} ≠ E`, so `ctxB` falls through
  to PATH C, whose `pvalueContains` requires `E(cs,tn0) = 6 ≤ 5` and fails — so
  `ctxB` would be REJECTED. `ctxB` is ACCEPTED (`exec_accepts_T3R_B_at_4400`).
  Contradiction: `ctxC` did not take PATH B, hence it accepted **through
  `checkByBuiltinContains`, PATH C**.

* **PATH B is taken at `ctxB` — MEASURED, and it CANNOT be proved by an
  accept/reject test.** On ledger-valid contexts PATH B is a strict refinement of
  PATH C: if output 0's map equals `E` exactly then the sum over all mini-ledger
  outputs contains `E` (every other contribution is `> 0` by `validTxOutValue`),
  so PATH B accepts ⟹ PATH C would accept. **PATH B is a pure performance fast
  path with no distinguishing input/output behaviour**, and no acceptance or
  rejection can isolate it. It is isolated by COST instead, and its CONDITION is
  evaluated separately: `T3R_pathB_condition` shows, in ground-truth vocabulary,
  that the output map equals the input map at `ctxB` and differs at `ctxC` — and
  at this shape the expected map IS the input map with ada dropped, because one
  contributing input means `pvalueFromCred` finishes in PHASE 2 with
  `ptail # (pasMap # firstVd)` and no arithmetic. `K_T3R_B_is_1936` and
  `K_T3R_C_is_2228` then pin, two-sided, a **292-step** gap between two contexts
  that differ in ONE integer leaf by ONE. Changing `qOut0` from 5 to 6 cannot cost 292
  CEK steps inside a fixed control flow; it costs them because the equality at
  :638 flipped and the run stopped short-circuiting and executed
  `accumulateOutputsAtCred` + `pvalueContains`. Stated plainly so it is not
  over-read: **PATH C's execution is proved, PATH B's is measured.**

* **SHAPE T4R's PHASE 3 is likewise measured, not asserted**: `K_T4R_is_2696`
  against SHAPE T1R's `K = 2343` at the same budget over the same skeleton plus
  one mini-ledger input.

ANTI-TAUTOLOGY. Every postcondition below is in `WSC/Model/Ground.lean`'s
ground-truth vocabulary — `outSum` / `inSum` / `mintSigned`, functions of
`ScriptContext` fields and CLAB's `valueOf` only. No validator-computed
accumulator appears in any conclusion (ARCHITECTURE.md Tier 0.1 / D3).
-/
import WSC.Shaped.GlobalShapedP1BCPrep
import WSC.Props.Shaped.GlobalRealizability
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): expected `sorry`s.
set_option warn.sorry false
set_option maxHeartbeats 0
-- the §5 realizability terms unify a witness `def` against its shape application
set_option maxRecDepth 1000000

namespace WSC

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash ScriptPurpose
                          TokenName TxInInfo TxOut TxOutRef validRewardingContext
                          findRedeemer hasCurrencySymbol)
open CardanoLedgerApi.V3.Contexts (redeemerCoverageAllPlutus noExtraRedeemersAllPlutus
                                   redeemersExactAllPlutus scriptPurposesWitnessed
                                   spendingPurposesWitnessed rewardingPurposesWitnessed
                                   certifyingPurposesWitnessed mintingPurposesWitnessed
                                   votingPurposesWitnessed proposingPurposesWitnessed
                                   coveredBy certifyingPurposesWitnessedFrom
                                   proposingPurposesWitnessedFrom)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## §1 — P1 over SHAPE T3R (containment dispatch PATHS B/C)

The postcondition is stated for BOTH token names. That is the point of the
shape: PATH A can only ever police one asset, and the two conjuncts are what a
single-asset scan could not deliver. -/

/-- **P1 (containment), SIGNED form, over the REALIZABLE SHAPE T3R — both token
names.** `outAtBase ≥ inAtBase + mintOf` at `(cs, tn0)` AND at `(cs, tn1)`, with
`qIn0`, `qIn1`, `qOut0`, `qOut1`, `qX0`, `qX1`, `qE0`, `qE1` eight INDEPENDENT
free Integers. The mint field is empty at this shape, so `mintSigned = 0` and the
signed form is the pure-transfer case; `Model.mintSigned` is kept in the
statement so the form is literally the one proved at T1R/T2R. -/
def P1BC_T3R_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn0 tn1 plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee) →
    Model.coveringNodeExists dirCS cs
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoReferenceInputs = false →
    isSuccessful
      (appliedGlobalShapedT3R.prop ppCS cs tn0 tn1 plc owner inAda qIn0 qIn1
        ext in2Ada qX0 qX1 outAda qOut0 qOut1 dest escAda qE0 qE1
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
      (Model.outSum (.ScriptCredential plc) cs tn0
          (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
            outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
            dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn0
            (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
              outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn0
            (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
              outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoMint)
      ∧ (Model.outSum (.ScriptCredential plc) cs tn1
          (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
            outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
            dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn1
            (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
              outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn1
            (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
              outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoMint)

/-- **P1 OVER THE REALIZABLE SHAPE T3R — PROVED AT UPLC AGAINST THE PRODUCTION
BYTECODE, ON THE PATH-B/C ARM OF THE CONTAINMENT DISPATCH.** The first such
result in this library: SHAPES T1R/T2R/T6R/T7R/T8R are all PATH A. The class is
proved non-empty by `t3R_realizable` below and redeemer-covered for every leaf
assignment by `t3R_class_coverage`. -/
theorem P1BC_T3R : P1BC_T3R_stmt := by blaster (timeout: 1500)

/-- **MANDATORY VACUITY PROBE AT SHAPE T3R AND ITS OWN PREP TERM.** Expected:
`Falsified`. A shaped theorem over an accept-UNSAT class is worthless and only
this catches it. -/
def P1BC_T3R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn0 tn1 plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT3R.prop ppCS cs tn0 tn1 plc owner inAda qIn0 qIn1
        ext in2Ada qX0 qX1 outAda qOut0 qOut1 dest escAda qE0 qE1
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1BC_T3R_vacuity_probe]

/-- Tightness stanza at SHAPE T3R: the conclusion is NOT hypothesis-implied.
Expected: `Falsified` — the ledger rules alone (in particular `isBalanced`) do
not force containment, because the shape keeps a non-base input AND a non-base
output. Stated on `tn0`; `tn1` is symmetric. -/
def P1BC_T3R_tightness : Prop :=
  ∀ (cs tn0 tn1 plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee) →
    ¬ (Model.outSum (.ScriptCredential plc) cs tn0
          (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
            outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
            dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn0
            (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
              outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoInputs)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1BC_T3R_tightness]

/-! ## §2 — P1 over SHAPE T4R (`pvalueFromCred` PHASE 3, builtin accumulation) -/

/-- **P1 (containment), SIGNED form, over the REALIZABLE SHAPE T4R.** `inAtBase`
is now the SUM of two independently symbolic mini-ledger inputs, and the
bytecode computes it with the CIP-153 builtins rather than a positional
ada-drop. -/
def P1BC_T4R_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString)
    (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase0 rBase1 rTls fee : Integer),
    validRewardingContext
      (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        rBase0 rBase1 rTls fee) →
    Model.coveringNodeExists dirCS cs
      (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        rBase0 rBase1 rTls fee).scriptContextTxInfo.txInfoReferenceInputs = false →
    isSuccessful
      (appliedGlobalShapedT4R.prop ppCS cs tn plc owner inAda0 qIn0 inAda1 qIn1
        ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase0 rBase1 rTls fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
            outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
            rBase0 rBase1 rTls fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
              outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              rBase0 rBase1 rTls fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
              outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
              rBase0 rBase1 rTls fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER THE REALIZABLE SHAPE T4R — PROVED AT UPLC.** The input-side half of
ARCHITECTURE.md §3-P1's lemma L1.3 (`valueFromCred` counts EVERY base input),
which `WSC/Props/P1_Transfer.lean` records as STATED-NOT-PROVED, discharged by
the bytecode on this shape over a node-realizable class. -/
theorem P1BC_T4R : P1BC_T4R_stmt := by blaster (timeout: 1500)

/-- **MANDATORY VACUITY PROBE AT SHAPE T4R AND ITS OWN PREP TERM.** Expected:
`Falsified`. -/
def P1BC_T4R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString)
    (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase0 rBase1 rTls fee : Integer),
    validRewardingContext
      (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        rBase0 rBase1 rTls fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT4R.prop ppCS cs tn plc owner inAda0 qIn0 inAda1 qIn1
        ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase0 rBase1 rTls fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1BC_T4R_vacuity_probe]

/-! ## §3 — CLASS-LEVEL REDEEMER COVERAGE (four-point bar, part (d))

The rule that made the PRE-re-cut SHAPES T3/T4 empty, discharged for EVERY leaf
assignment of the re-cut shapes — in CLAB's own transcription of Conway UTXOW's
`MissingRedeemers` (`redeemerCoverageAllPlutus`) and in the ∀-form
`RedeemerCovered` the emptiness proofs consume. -/

/-- SHAPE T4R's 4-entry map covers the `Spending` purpose of mini-ledger input 0
(`TxOutRef ⟨"",0⟩`). -/
theorem p1AggR_spending0_covered (w0 w1 : ByteString) (rBase0 rBase1 rTls : Integer)
    (own : Data) :
    findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
      (p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own) ≠ none := by
  have : findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
      (p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own) = some (Data.I rBase0) := rfl
  simp [this]

/-- …and of mini-ledger input 1 (`TxOutRef ⟨"",1⟩`) — the entry SHAPE T4 lacked
and the reason its class was empty a second time over. -/
theorem p1AggR_spending1_covered (w0 w1 : ByteString) (rBase0 rBase1 rTls : Integer)
    (own : Data) :
    findRedeemer (.Spending ⟨ByteString.mk "", 1⟩)
      (p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own) ≠ none := by
  have : findRedeemer (.Spending ⟨ByteString.mk "", 1⟩)
      (p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own) = some (Data.I rBase1) := rfl
  simp [this]

/-- …and BOTH script withdrawals. No side condition: the `w0`/`w1` split is on a
decidable `Bool`. -/
theorem p1AggR_rewarding_covered (w0 w1 h : ByteString) (rBase0 rBase1 rTls : Integer)
    (own : Data) (hh : h = w0 ∨ h = w1) :
    findRedeemer (.Rewarding (.ScriptCredential h))
      (p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own) ≠ none := by
  show (if (ScriptPurpose.Spending ⟨ByteString.mk "", 0⟩
            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
        then some (Data.I rBase0)
        else if (ScriptPurpose.Spending ⟨ByteString.mk "", 1⟩
                  == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
             then some (Data.I rBase1)
             else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                       == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                  then some own
                  else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w1)
                            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                       then some (Data.I rTls) else none) ≠ none
  rw [show (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  rw [show (ScriptPurpose.Spending (⟨ByteString.mk "", 1⟩ : TxOutRef)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  by_cases hw : (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
  · simp [hw]
  · have hw1 : h = w1 := by
      rcases hh with h1 | h1
      · exact absurd (by rw [h1]; simp) hw
      · exact h1
    subst hw1
    simp [hw]

/-- **SHAPE T3R is redeemer-covered, for every leaf assignment.** Input 0 sits at
`ScriptCredential plc` with `TxOutRef ⟨"",0⟩`, which the map's first entry names;
input 1 is at a pubkey credential; both script withdrawals have `Rewarding`
entries; the mint clause is vacuous. -/
theorem t3R_class_covered
    (cs tn0 tn1 plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    RedeemerCovered
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1BCShapedCtx] at ht
    rcases ht with rfl | rfl
    · exact p1R_spending_covered w0 w1 rBase rTls p1ShapedRedeemer
    · exact absurd hpc (by simp [payCred, p1TwoExtIn])
  · intro h n hw
    simp [p1BCShapedCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inl hh)
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inr hh)
  · intro c hc
    simp [p1BCShapedCtx, hasCurrencySymbol] at hc

/-- **SHAPE T4R is redeemer-covered, for every leaf assignment.** Clause 1 now has
TWO script inputs to discharge. -/
theorem t4R_class_covered
    (cs tn plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase0 rBase1 rTls fee : Integer) :
    RedeemerCovered
      (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        rBase0 rBase1 rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1AggRCtx] at ht
    rcases ht with rfl | rfl | rfl
    · exact p1AggR_spending0_covered w0 w1 rBase0 rBase1 rTls p1ShapedRedeemer
    · exact p1AggR_spending1_covered w0 w1 rBase0 rBase1 rTls p1ShapedRedeemer
    · exact absurd hpc (by simp [payCred, p1ShapedExtIn2])
  · intro h n hw
    simp [p1AggRCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1AggR_rewarding_covered w0 w1 h rBase0 rBase1 rTls p1ShapedRedeemer (Or.inl hh)
    · exact p1AggR_rewarding_covered w0 w1 h rBase0 rBase1 rTls p1ShapedRedeemer (Or.inr hh)
  · intro c hc
    simp [p1AggRCtx, hasCurrencySymbol] at hc

/-! ## §4 — CONCRETE WITNESSES of exactly SHAPES T3R / T4R

No SMT anywhere in this section: every statement is `native_decide` over the real
CEK machine and CLAB's own ledger predicates. -/

namespace P1BCShapedWitness

set_option maxRecDepth 1000000

open P1ShapedWitness (ppCS isHaltB isHaltB_sound)

/-- SHAPE T3R with the four output quantities as parameters and everything else
pinned. Policy `MMM` with token names `TOKA < TOKB`; the mini-ledger input holds
5 of each, an external pubkey input holds 4 of each, so `isBalanced` reads
`qOut_i + qE_i = 9` and containment must be earned. Ada 200 + 100 in, 150 + 100
out, fee 50. Directory node keyed `("MMM","ZZZ")` — `key = cs` exactly, so the
transfer proof's positive branch passes while `Model.coveringNodeExists`
(STRICT `key < cs`) is false. -/
def mkT3R (qOut0 qOut1 qE0 qE1 : Integer) : ScriptContext :=
  p1BCShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOKA") (ByteString.mk "TOKB")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
    (ByteString.mk "EXT") 100 4 4
    150 qOut0 qOut1
    (ByteString.mk "DEST") 100 qE0 qE1
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 88
    50

/-- **SHAPE T3R, accepting, WHOLESALE (PATH B).** The mini-ledger output carries
exactly the expected map — 5 of each token name — so :638's `equalsData` holds
and the run short-circuits. The escape output carries 4 + 4, so the escape route
is non-empty in an accepting context. -/
def ctxB : ScriptContext := mkT3R 5 5 4 4

/-- **SHAPE T3R, accepting, BUILTIN (PATH C).** `ctxB` with ONE integer leaf
changed by ONE: the mini-ledger output holds 6 of `TOKA` instead of 5 (the escape
output 3 instead of 4, to keep `isBalanced`). The wholesale equality now fails
and containment is decided by the CIP-153 builtin `pvalueContains`. -/
def ctxC : ScriptContext := mkT3R 6 5 3 4

/-- SHAPE T3R, accepting, both token names strictly over-supplied. -/
def ctxC2 : ScriptContext := mkT3R 6 6 3 3

/-- **SHAPE T3R, ESCAPING ON `tn0` — the excluded case, and half of the PATH-A
exclusion.** `TOKA` is short by 1 at the mini-ledger (4 out of 5); `TOKB` is
whole (5 out of 5). -/
def ctxEsc0 : ScriptContext := mkT3R 4 5 5 4

/-- **SHAPE T3R, ESCAPING ON `tn1`** — the mirror image: `TOKA` whole, `TOKB`
short by 1. -/
def ctxEsc1 : ScriptContext := mkT3R 5 4 4 5

/-- **SHAPE T4R, accepting.** Two mini-ledger inputs holding 5 and 3, an external
pubkey input holding 4; 8 back at the mini-ledger output and 4 escaping. SHAPE
T4's own witness leaves (`WSC/Shaped/Probe/T4Probe.lean`) plus the three new
redeemer-slot Integers. -/
def ctxAgg : ScriptContext :=
  p1AggRCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
    (ByteString.mk "EXT") 100 4
    250 8
    (ByteString.mk "DEST") 120 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 78 88
    50

/-- **SHAPE T4R, ESCAPING** — only 6 of the AGGREGATED 5 + 3 come back, so the
2-unit shortfall is invisible to any check that looks at a single input. -/
def ctxAggEscape : ScriptContext :=
  p1AggRCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
    (ByteString.mk "EXT") 100 4
    250 6
    (ByteString.mk "DEST") 120 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    77 78 88
    50

/-! ### The witnesses satisfy the theorems' hypotheses IN FULL -/

theorem ctxB_valid : validRewardingContext ctxB = true := by native_decide
theorem ctxC_valid : validRewardingContext ctxC = true := by native_decide
theorem ctxC2_valid : validRewardingContext ctxC2 = true := by native_decide
theorem ctxEsc0_valid : validRewardingContext ctxEsc0 = true := by native_decide
theorem ctxEsc1_valid : validRewardingContext ctxEsc1 = true := by native_decide
theorem ctxAgg_valid : validRewardingContext ctxAgg = true := by native_decide
theorem ctxAggEscape_valid : validRewardingContext ctxAggEscape = true := by native_decide

theorem ctxB_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxB.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

theorem ctxAgg_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxAgg.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

/-! ### The ground-truth quantities, evaluated -/

/-- At `ctxB` the mini-ledger balances on BOTH token names. -/
theorem ctxB_quantities :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKA") ctxB.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKA") ctxB.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKB") ctxB.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKB") ctxB.scriptContextTxInfo.txInfoInputs = 5 := by native_decide

/-- **BOTH ESCAPE ROUTES ARE REAL.** `ctxEsc0` moves one `TOKA` out of the
mini-ledger while leaving `TOKB` whole; `ctxEsc1` does the mirror image. -/
theorem ctxEsc_quantities :
    (Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKA") ctxEsc0.scriptContextTxInfo.txInfoOutputs = 4
     ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKB") ctxEsc0.scriptContextTxInfo.txInfoOutputs = 5)
    ∧ (Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKA") ctxEsc1.scriptContextTxInfo.txInfoOutputs = 5
     ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKB") ctxEsc1.scriptContextTxInfo.txInfoOutputs = 4)
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKA") ctxEsc0.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOKB") ctxEsc1.scriptContextTxInfo.txInfoInputs = 5 := by native_decide

/-- The AGGREGATION is genuine at SHAPE T4R: neither mini-ledger input alone is
the requirement (5 and 3); their SUM is. -/
theorem ctxAgg_aggregation_is_genuine :
    Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxAgg.scriptContextTxInfo.txInfoInputs = 8
    ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxAgg.scriptContextTxInfo.txInfoOutputs = 8
    ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxAggEscape.scriptContextTxInfo.txInfoOutputs = 6
    := by native_decide

/-! ### NON-VACUITY, EXECUTABLE: the real bytecode accepts -/

/-- **NON-VACUITY, SHAPE T3R, PATH B witness.** -/
theorem exec_accepts_T3R_B_at_4400 :
    isSuccessful
      (appliedGlobalShapedT3R.exec ppCS (ByteString.mk "MMM")
        (ByteString.mk "TOKA") (ByteString.mk "TOKB")
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
        (ByteString.mk "EXT") 100 4 4
        150 5 5
        (ByteString.mk "DEST") 100 4 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, SHAPE T3R, PATH C witness.** -/
theorem exec_accepts_T3R_C_at_4400 :
    isSuccessful
      (appliedGlobalShapedT3R.exec ppCS (ByteString.mk "MMM")
        (ByteString.mk "TOKA") (ByteString.mk "TOKB")
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
        (ByteString.mk "EXT") 100 4 4
        150 6 5
        (ByteString.mk "DEST") 100 3 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, SHAPE T4R.** -/
theorem exec_accepts_T4R_at_4400 :
    isSuccessful
      (appliedGlobalShapedT4R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK")
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
        (ByteString.mk "EXT") 100 4
        250 8
        (ByteString.mk "DEST") 120 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        77 78 88
        50) :=
  isHaltB_sound _ (by native_decide)

/-! ### THE EXCLUDED CASES, EXECUTABLE -/

/-- **PATH A IS NOT THE PATH THIS SHAPE RUNS — PROVED, not asserted.**

Both contexts are `validRewardingContext`, redeemer-covered, and rejected by the
REAL compiled bytecode with 4400 steps available. In `ctxEsc0` the pair
`(MMM, TOKA)` is short by one and `(MMM, TOKB)` is whole; in `ctxEsc1` it is the
other way round (`ctxEsc_quantities`).

PATH A is `hasAtLeastAssetInProgOutputs` (ProgrammableLogicBase.hs:567-593),
which polices exactly ONE `(cs, tn)` pair — the single entry the dispatch guard
at :655-656 requires the expected value to have. Whichever pair that were, one of
these two contexts leaves it whole and PATH A would ACCEPT it. Both are REJECTED,
so the run is on the `checkWholesaleThenBuiltin` arm. -/
theorem T3R_not_path_A :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxEsc0) 4400) = false
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxEsc1) 4400) = false := by
  native_decide

/-- **PATH C IS EXECUTED AND RETURNS TRUE AT `ctxC` — PROVED.**

The two conjuncts are the executable input to the argument in this module's
header, which needs nothing about the validator beyond two facts readable off the
source: (i) `expectedProgrammableOutputValue` (`:1225-1268`) is `plet`-bound
before the containment call at `:1270-1276` and its definition mentions
`ptxInfo'inputs`, `ptxInfo'referenceInputs`, `ptxInfo'mint`,
`ptxInfo'signatories`, `ptxInfo'wdrl` and the redeemer but **not
`ptxInfo'outputs`** — and `ctxB` and `ctxC` agree on every one of those, so both
runs present the SAME expected value `E` to
`poutputsContainExpectedValueAtCred`; (ii) PATH C is `pvalueContains`, which by
its CIP-153 specification requires `E(c,t) ≤ acc(c,t)` for every key.

If `ctxC` had accepted on PATH B then `E = {cs:{TOKA:6, TOKB:5}}`, and `ctxB`
(output map `{cs:{TOKA:5, TOKB:5}} ≠ E`) would fall through to PATH C and be
REJECTED for `6 ≤ 5`. It is accepted. So `ctxC` accepted through
`checkByBuiltinContains`. -/
theorem T3R_pathC_is_taken :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxB) 4400) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxC) 4400) = true := by
  native_decide

/-- **THE TWO SIDES OF PATH B's EQUALITY, IN GROUND-TRUTH VOCABULARY.**

PATH B's test at ProgrammableLogicBase.hs:638 is
`(pmapData # (ptail # (pasMap # txOutValueData))) #== expectedMapData`, i.e. the
mini-ledger OUTPUT's value map with the ada entry dropped, against the expected
map. At SHAPE T3R the expected map is the mini-ledger INPUT's value map with the
ada entry dropped: the shape has exactly ONE contributing input, so
`pvalueFromCred` finishes in PHASE 2 and returns `ptail # (pasMap # firstVd)`
(:411-427) with no arithmetic at all; the mint field is empty so
`punionValue` adds nothing (:1219-1222); and `pfilterPositiveCurrencyPairs`
(:257-298) is the identity here because `validTxOutValue` forces both quantities
`> 0` (`ctxB_valid`).

So this theorem is PATH B's condition, evaluated: it HOLDS at `ctxB` and FAILS at
`ctxC`. Both sides are read straight off the `ScriptContext` — no validator
accumulator appears. -/
theorem T3R_pathB_condition :
    ((ctxB.scriptContextTxInfo.txInfoOutputs.map (fun o => o.txOutValue.tail)).head?
      = (ctxB.scriptContextTxInfo.txInfoInputs.map
          (fun i => i.txInInfoResolved.txOutValue.tail)).head?)
    ∧ ((ctxC.scriptContextTxInfo.txInfoOutputs.map (fun o => o.txOutValue.tail)).head?
        ≠ (ctxC.scriptContextTxInfo.txInfoInputs.map
            (fun i => i.txInInfoResolved.txOutValue.tail)).head?) := by
  native_decide

/-- **THE EXCLUDED CASE AT SHAPE T4R.** `ctxAggEscape` is ledger-legal,
redeemer-covered, and moves 2 units out of the mini-ledger by under-supplying the
AGGREGATE of two inputs; the real compiled bytecode rejects it. -/
theorem exec_rejects_T4R_escape :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxAggEscape) 4400) = false := by
  native_decide

/-! ### EXACT STEP COUNTS, PINNED TWO-SIDED

`K` halts at `K` and budget-errors at `K − 1`. Budget 4400 throughout.

**The B/C separation is here.** `ctxB` and `ctxC` differ in ONE integer leaf by
ONE (`qOut0`: 5 vs 6, with `qE0` 4 vs 3 to keep `isBalanced`), and cost **1936 vs
2228** steps — a 292-step gap. Inside a fixed control flow, changing an integer
leaf by one cannot cost 292 CEK steps; it costs them because the `equalsData` at
:638 flipped and the run stopped short-circuiting on PATH B and executed
`accumulateOutputsAtCred` + `pvalueContains` on PATH C. `ctxC2`, which
over-supplies BOTH token names, costs the same 2228 as `ctxC` — consistent with
both being on PATH C and inconsistent with the cost tracking the quantities. -/
theorem K_T3R_B_is_1936 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxB) 1936) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxB) 1935) = false := by
  native_decide

theorem K_T3R_C_is_2228 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxC) 2228) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxC) 2227) = false := by
  native_decide

theorem K_T3R_C2_is_2228 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxC2) 2228) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxC2) 2227) = false := by
  native_decide

/-- SHAPE T4R costs 2696 steps against SHAPE T1R's 2343 over the same skeleton
plus one mini-ledger input — the price of `pvalueFromCred`'s PHASE 3 builtin
accumulation. Headroom to the 4400 budget: 1704. -/
theorem K_T4R_is_2696 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxAgg) 2696) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxAgg) 2695) = false := by
  native_decide

end P1BCShapedWitness

/-! ## §5 — POINT-LEVEL REALIZABILITY

Each theorem packages, about ONE concrete context of the shape: CLAB's
`validRewardingContext`; `redeemersExactAllPlutus` — **BOTH halves** of Conway
UTXOW's `hasExactSetOfRedeemers` (`MissingRedeemers` AND `ExtraRedeemers`);
`RedeemerCovered`, the ∀-form whose failure made the PRE-re-cut class empty; and
acceptance by the REAL compiled bytecode inside the theorem's budget. -/

/-- **SHAPE T3R IS REALIZABLE** — the first non-empty class on which any
containment dispatch path other than PATH A has been reached at UPLC. Budget
4400, witness K = 1936. -/
theorem t3R_realizable :
    validRewardingContext P1BCShapedWitness.ctxB = true
    ∧ redeemersExactAllPlutus P1BCShapedWitness.ctxB.scriptContextTxInfo = true
    ∧ RedeemerCovered P1BCShapedWitness.ctxB
    ∧ isSuccessful
        (appliedGlobalShapedT3R.exec P1ShapedWitness.ppCS (ByteString.mk "MMM")
          (ByteString.mk "TOKA") (ByteString.mk "TOKB")
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
          (ByteString.mk "EXT") 100 4 4
          150 5 5
          (ByteString.mk "DEST") 100 4 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 88
          50) :=
  ⟨P1BCShapedWitness.ctxB_valid, by native_decide,
   t3R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOKA") (ByteString.mk "TOKB")
     (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
     (ByteString.mk "EXT") 100 4 4 150 5 5 (ByteString.mk "DEST") 100 4 4
     (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
     (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
     (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
     (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
     (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 88 50,
   P1BCShapedWitness.exec_accepts_T3R_B_at_4400⟩

/-- **SHAPE T3R IS REALIZABLE AT THE PATH-C WITNESS TOO.** Same class, the
context whose acceptance `T3R_pathC_is_taken` uses. Budget 4400, witness
K = 2228. -/
theorem t3R_realizable_pathC :
    validRewardingContext P1BCShapedWitness.ctxC = true
    ∧ redeemersExactAllPlutus P1BCShapedWitness.ctxC.scriptContextTxInfo = true
    ∧ RedeemerCovered P1BCShapedWitness.ctxC
    ∧ isSuccessful
        (appliedGlobalShapedT3R.exec P1ShapedWitness.ppCS (ByteString.mk "MMM")
          (ByteString.mk "TOKA") (ByteString.mk "TOKB")
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
          (ByteString.mk "EXT") 100 4 4
          150 6 5
          (ByteString.mk "DEST") 100 3 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 88
          50) :=
  ⟨P1BCShapedWitness.ctxC_valid, by native_decide,
   t3R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOKA") (ByteString.mk "TOKB")
     (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 5
     (ByteString.mk "EXT") 100 4 4 150 6 5 (ByteString.mk "DEST") 100 3 4
     (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
     (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
     (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
     (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
     (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 88 50,
   P1BCShapedWitness.exec_accepts_T3R_C_at_4400⟩

/-- **SHAPE T4R IS REALIZABLE.** Budget 4400, witness K = 2696. -/
theorem t4R_realizable :
    validRewardingContext P1BCShapedWitness.ctxAgg = true
    ∧ redeemersExactAllPlutus P1BCShapedWitness.ctxAgg.scriptContextTxInfo = true
    ∧ RedeemerCovered P1BCShapedWitness.ctxAgg
    ∧ isSuccessful
        (appliedGlobalShapedT4R.exec P1ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
          (ByteString.mk "EXT") 100 4
          250 8
          (ByteString.mk "DEST") 120 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 78 88
          50) :=
  ⟨P1BCShapedWitness.ctxAgg_valid, by native_decide,
   t4R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK")
     (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
     (ByteString.mk "EXT") 100 4 250 8 (ByteString.mk "DEST") 120 4
     (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
     (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
     (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
     (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
     (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 78 88 50,
   P1BCShapedWitness.exec_accepts_T4R_at_4400⟩

/-! ## §6 — AXIOM CENSUS (warning counts are not a census; `#print axioms` is) -/

#print axioms P1BC_T3R
#print axioms P1BC_T4R
#print axioms t3R_realizable
#print axioms t3R_realizable_pathC
#print axioms t4R_realizable
#print axioms t3R_class_covered
#print axioms t4R_class_covered
#print axioms P1BCShapedWitness.T3R_not_path_A
#print axioms P1BCShapedWitness.T3R_pathC_is_taken
#print axioms P1BCShapedWitness.T3R_pathB_condition
#print axioms P1BCShapedWitness.K_T3R_B_is_1936
#print axioms P1BCShapedWitness.K_T3R_C_is_2228
#print axioms P1BCShapedWitness.K_T4R_is_2696

end WSC
