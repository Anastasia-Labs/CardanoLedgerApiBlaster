-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/P2Shaped.lean — **P2 (seize / clawback) PROVED at UPLC level
against the real compiled `programmableSeize` bytecode, over SHAPE S1** — BOTH
conjuncts, including the containment conjunct that the source-model route could
not close (task Z6).

PLAIN ENGLISH.  When the seize validator accepts, it only ever moves the ONE
policy being seized: every mini-ledger input it consumes has a corresponding
continuing output at the same address (staking credential included) with the same
datum and reference script, differing at most in the seized policy; and the
seized amount plus any seize-time mint of that policy stays inside the
mini-ledger.  A seizure relocates the seized tokens within the mini-ledger and
cannot touch anything else.

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED, AND WHY IT MATTERS
════════════════════════════════════════════════════════════════════════════
`WSC/Model/SeizeModel.lean`'s header records P2 as measured UNREACHABLE at UPLC:
symbolic `#prep_uplc` unfinished in 77 min at budget 2,000 and 62 min at 9,000,
and the two budgets whose prep DID complete (600, 1,000) provably admit no
accepting context.  That is why P2 was routed through a hand-transcribed source
model carrying the axiom `seizeModel_faithful`.

Shaping removes BOTH walls at once:

| | source-model route (Z3/Z4) | this module (SHAPE S1) |
|---|---|---|
| prep | never completes at accept-capable budgets | **3.0 s at budget 3800** |
| conjunct 1 (structure) | proved on the MODEL, + `seizeModel_faithful` | **proved on the BYTECODE** |
| conjunct 2 (containment) | **NOT proved** — bridge lemma B1 is FALSE without ledger canonicity (`WSC/Props/P2_Seize.lean` §5) | **PROVED** |
| trust base | one hand-transcription axiom | solver + `admit` + the shape |

**Conjunct 2 is the interesting one.**  On the source model it is blocked by two
machine-checked counterexamples (`WSC/Props/P2_Seize.lean`
`tokensContain_unsound_with_duplicate_names`,
`tokensContain_unsound_when_unsorted`): `ptokenPairsContain` is not pointwise
sound unless every token map is duplicate-free and sorted, which is a LEDGER
rule (`validTxOutValue`) that the model route would have to carry through four
token-list combinators (obligation B2).  **At SHAPE S1 that canonicity is free:
every value in the shape is `Shape.adaPlusOne`, i.e. ada plus one policy with
exactly ONE token name, and a one-entry token map is duplicate-free and sorted by
construction.**  So neither counterexample can be instantiated, and Z3 discharges
the containment conjunct directly against the bytecode.  This is a concrete
illustration of what the shaped route buys that the model route cannot: the shape
supplies, for free and verifiably, the canonicity side conditions that a
general-purpose proof has to earn.

════════════════════════════════════════════════════════════════════════════
SCOPE — THREE BOUNDS, ALL BINDING
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 3800** (ADDENDUM E1).  Every theorem below is about
runs that halt within 3800 CEK steps.  Measured: the shape's "nothing moves"
accepting instance costs K = 3004 and its "residual output" accepting instance
(the shape of the real goldens) K = 3328, so 3800 covers both;
`WSC/Shaped/Probe/S1K.lean`.  There is NO `LR_BUDGET_seize` axiom in
`WSC/Honest.lean`, so unlike P3/P5 this bound is not yet bridged to node
acceptance — see OPEN ISSUES.

**Bound 2 — SHAPE S1**, published in full in `WSC/Shaped/SeizeShaped.lean`'s
header.  In one line: 2 inputs (one mini-ledger candidate at a script address
with a staking credential, one pubkey wallet input), 2 reference inputs (params
node then the directory node the redeemer points at), 2 outputs (the continuing
output, and a second output at a FREE script credential that is the escape route
when it differs from the base credential and the residual seized-tokens output
when it equals it), every value ada + one policy + one token name, a mint of one
policy and one token name with a free SIGNED quantity, a
2-entry all-script withdrawal map, one redeemer entry, empty
cert/signatory/datum/vote/proposal lists, and the redeemer fixed to
`SeizeAct 1 [] 0 0 0 1`.

**Bound 2b — THREE BY-CONSTRUCTION EQUALITIES forced by DEFECT D4** (a
`#prep_uplc` bug on compound-`Bool` branch conditions, diagnosed and measured in
`WSC/Shaped/SeizeShaped.lean`'s header).  At SHAPE S1 the paired input and output
necessarily agree on their PAYMENT credential, on their non-ada policy id and on
their token name, and both carry no reference script.  Consequences to read
honestly:
* `pairPreserved`'s reference-script clause is true by construction here;
* the theorem does not cover pairs whose payment credentials or whose non-ada
  policy/token name DIFFER.  Those assignments are all REJECTED by the
  validator — a differing non-seized policy hits `goOuter`'s `perror` at :1810 /
  :1815 and a differing token name leaves a positive residual requirement that
  `checkBalanceInvariant` refuses at :1508 — so nothing about ACCEPTING runs is
  lost.  But that is an ARGUMENT, not a theorem in this file, and it is the first
  thing to fix when D4 is fixed upstream.
* what is NOT lost: the pair's STAKING credentials stay two independent variables
  (`inStk`, `oStk`).  That is the mini-ledger's ownership field — the clause a
  seizure would have to break to hand tokens to a different holder — and the
  bytecode has to earn it.

**Bound 3 — P2 does not claim the seized policy is legitimate.**  The seized
policy is `key`, read out of whatever reference input the redeemer's
`directoryNodeIdx` points at.  P2 says a seizure cannot touch anything else; it
does NOT say the node is an authentic directory node (that is ARCHITECTURE.md's
L2.5, which lives with `DirWF`), and no `WSC/Honest.lean` axiom is used here.

**NOTHING IN EITHER POSTCONDITION IS SMUGGLED INTO THE SHAPE.**  The four places
where a lazier shape would have handed it over:
1. the base credential `plc` (published by the params datum) is a DIFFERENT
   variable from the pair's payment credential `mlH` and from the second output's
   `escH`, so "at the mini-ledger" is decided by the solver;
2. `inStk` ≠ `oStk` and `dIn` ≠ `dOut` as variables, so the address and datum
   clauses of `pairPreserved` are earned;
3. the seized policy `key` is a DIFFERENT variable from every value's policy, so
   the shape does not pre-decide which policy the containment is about — and the
   ada-as-seized-policy case (`key = ""`) is inside the class;
4. the shape carries a SECOND OUTPUT so that ledger balance alone does NOT imply
   containment (see `WSC/Shaped/SeizeShaped.lean`'s header).  `ctxEscape` below
   is the witness that the excluded assignment is ledger-legal and really is
   rejected by the bytecode.

════════════════════════════════════════════════════════════════════════════
PRECONDITION AUDIT (arch §4.1)
════════════════════════════════════════════════════════════════════════════
MAY assume, and does: `validRewardingContext (seizeShapedCtx …)` — CLAB ledger
normalization only, specialized to the shape.  It never inspects the redeemer's
content.

MUST NOT assume, and does not: nothing about the reference inputs being
authentic, nothing about the params or node datum beyond the shape's skeleton,
no `HonestParams` / `Deployed` / `OnChain` / `DirWF` hypothesis anywhere.

D3 (TAUTOLOGY-RISK) COMPLIANCE, unchanged from `WSC/Props/P2_Seize.lean`: neither
postcondition mentions the validator's `expectedValue` / `deltaAccumulator`.
Conjunct 1 is `WSC.seizeStructurePreserved`, a function of `txInfoInputs` and
`txInfoOutputs` only; conjunct 2 is `valueOf`-sums over base inputs/outputs plus
`WSC.mintOf` — ledger ground truth.  Both are the SAME predicates
`WSC/Props/P2_Seize.lean` states, instantiated at the shape (see §Projection
audit).
-/
import WSC.Shaped.SeizeShaped
import WSC.Props.P2_Seize
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
open WSC.SeizeModel (seizedPolicyOf pairedOutputsOf progLogicCredDataOf)

/-! ## §Projection audit — SHAPE S1 instantiates P2's own projections

`WSC/Props/P2_Seize.lean` states P2 with three `Option`-valued projections that
NAME ledger data the way the validator names it.  The lemmas here show what those
projections evaluate to at SHAPE S1, so the theorems below can be read as
"`P2a_seizeModel_preserves_structure` / `P2b_seized_delta_contained`, specialized
to SHAPE S1 and proved against the bytecode instead of the model". -/

section Leaves
variable (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
         (dIn : ByteString)
         (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
         (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
         (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
         (mCS mTn : ByteString) (mQ : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer)
         (fee : Integer)

/-- The seized policy at SHAPE S1 is `key`, position 0 of the datum of the
reference input the redeemer's `directoryNodeIdx = 1` selects. -/
theorem shape_seizedPolicy :
    seizedPolicyOf
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = some key := rfl

/-- The paired-output cursor at SHAPE S1 is the WHOLE output list
(`outputsStartIdx = 0`). -/
theorem shape_pairedOutputs :
    pairedOutputsOf
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      = some
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs := rfl

/-- The mini-ledger base credential at SHAPE S1 is `ScriptCredential plc`,
position 1 of the params datum — PROVIDED the params UTxO authenticates, i.e.
`pCS = ppCS` (`phasCSH`, ProgrammableLogicBase.hs:832).  That hypothesis is not
decoration: `P2_shaped_gates_are_earned` below proves the bytecode's accept path
forces it. -/
theorem shape_progLogicCred (ppCS : CurrencySymbol) (hpc : pCS = ppCS) :
    progLogicCredDataOf ppCS
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      = some (IsData.toData (Credential.ScriptCredential plc)) := by
  subst hpc
  simp [progLogicCredDataOf, seizeShapedCtx, seizeShapedRedeemer,
        SeizeModel.seizeFieldsOf, SeizeModel.paramsAtRefIdx, SeizeModel.dropL,
        SeizeModel.headM, seizeShapedParamsIn, Shape.adaPlusOne, SeizeModel.hasCSH,
        SeizeModel.paramsDirCSAndProgCred]

end Leaves

/-! ## The bytecode obligations — BOTH PROVED -/

/-- **P2 (a) — STRUCTURE PRESERVATION, over SHAPE S1, PROVED AT UPLC.**

*If the real compiled `programmableSeize` bytecode accepts a shape-S1
transaction, then walking the transaction's inputs in order, each input at the
mini-ledger base credential is paired with the next output, and that pair has the
same address — STAKING CREDENTIAL INCLUDED — the same datum, the same reference
script, and identical holdings of every policy other than the seized one, Ada
included.  Inputs outside the mini-ledger consume no output.*

The postcondition is `WSC.seizeStructurePreserved` verbatim
(WSC/Spec.lean:356-367), i.e. the same predicate
`WSC/Props/P2_Seize.lean`'s `P2a_seizeModel_preserves_structure` concludes — but
about the BYTECODE, with no `seizeModel_faithful`.

MEASURED: see this module's build time in WSC/status-fragments/z6-p2shaped.md. -/
theorem P2a_shaped_structure :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      WSC.seizeStructurePreserved (Credential.ScriptCredential plc) key
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs = true
      := by blaster

/-- **P2 (b) — CONTAINMENT OF THE SEIZED DELTA, over SHAPE S1, PROVED AT UPLC.**
This is the conjunct the source-model route could NOT close.

*If the real compiled `programmableSeize` bytecode accepts a shape-S1
transaction, then for EVERY token name the total holding of the seized policy at
outputs sitting on the mini-ledger base credential is at least the total holding
at inputs spent from it, plus the (signed) net mint of that asset.  The seized
amount cannot leave the mini-ledger.*

The mint is SIGNED, not `mintPos` (ARCHITECTURE.md §3-P2 note): a legitimate burn
lowers the requirement.  The inequality is `≥` and not `=` for the two slack
reasons `WSC/Props/P2_Seize.lean` records — residual base outputs after the
paired ones, and outputs before `outputsStartIdx` — both of which can only ADD to
the base side.

This is `WSC/Props/P2_Seize.lean`'s `P2b_seized_delta_contained` (a `Prop`
DEFINITION there, deliberately not a theorem), instantiated at SHAPE S1 and
proved against the bytecode.  Why it closes here and not there: at this shape
every token map has exactly one entry, so it is duplicate-free and sorted, and
the two machine-checked counterexamples to obligation B1 cannot be
instantiated. -/
theorem P2b_shaped_containment :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint
      := by blaster

/-- **The shape does not pre-satisfy the validator's three authentication
gates.**  An accepting shape-S1 run must clear all three, and this theorem
extracts them, which is what licenses `shape_progLogicCred`'s hypothesis:

* `pCS = ppCS` — `pparamsAtRefIdx`'s `phasCSH` on the params UTxO (:832);
* `nCS = dirCS` — condition 4, `phasCSH` of the DIRECTORY policy published by the
  params datum on the node's own value (:1329);
* `w1 = ilsH` — condition 3, the node datum's `issuerLogicScript` must be the
  credential of the withdrawal entry at `issuerWdrlIdx = 1` (:1323-1328).

Each pair is two DIFFERENT free variables in the shape, so none of the three is
true by construction. -/
theorem P2_shaped_gates_are_earned :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      pCS = ppCS ∧ nCS = dirCS ∧ w1 = ilsH
      := by blaster

/-- **P2, both conjuncts, one statement.** -/
theorem P2_shaped
    (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (hv : validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee))
    (ha : isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) :
      WSC.seizeStructurePreserved (Credential.ScriptCredential plc) key
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs = true
    ∧ ∀ tn : TokenName,
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint :=
  ⟨P2a_shaped_structure ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee hv ha,
   fun tn => P2b_shaped_containment ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee tn hv ha⟩

/-! ## Polarity controls (ADDENDUM E9) — the full control set -/

/-- Negative control for conjunct 1: a shape-S1 context that does NOT preserve
the structure is REJECTED by the bytecode.

NOTE (E9, binding): a negative control is also satisfied by budget-`Error`, so it
cannot detect the 3800-step bound by itself; the vacuity probe and the concrete
witnesses below are what do. -/
theorem P2a_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(WSC.seizeStructurePreserved (Credential.ScriptCredential plc) key
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs = true) →
    isUnsuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      := by blaster

/-- Negative control for conjunct 2: a shape-S1 context in which the seized
policy ESCAPES the mini-ledger for some token name is REJECTED. -/
theorem P2b_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint) →
    isUnsuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      := by blaster

/-- Tightness stanza: the NEGATION of P2's structural postcondition under an
accepting run must be FALSIFIABLE, i.e. accepting shape-S1 contexts that satisfy
it exist.  Expected and MEASURED: `Falsified`. -/
def P2a_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(WSC.seizeStructurePreserved (Credential.ScriptCredential plc) key
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
        (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs = true)

#blaster (gen-cex: 0) (solve-result: 1) [P2a_shaped_tightness]

/-- Tightness stanza for conjunct 2.  Expected and MEASURED: `Falsified`. -/
def P2b_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
                wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
                escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
                nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint)

#blaster (gen-cex: 0) (solve-result: 1) [P2b_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT THE SHAPE.**  "No accepting shape-S1 context
exists within 3800 CEK steps" must be FALSIFIED.

Expected and MEASURED: `Falsified`.  Contrast `WSC/Prep/Seize.lean`'s budget-600
prep, whose probe is `Valid` — genuinely vacuous — which is exactly why no P2
theorem could be stated at UPLC before this module.  The two concrete witnesses
below discharge the obligation a second time without the solver. -/
def P2_shaped_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (gen-cex: 0) (solve-result: 1) [P2_shaped_vacuity_probe]

/-! ## CONCRETE instances OF EXACTLY SHAPE S1 — executable, no SMT

Three instances, all `validRewardingContext`-normalized, all run through the REAL
compiled bytecode by `native_decide`:

* `ctxAccept`   — accepting, "nothing moves": the pair keeps all 10 seized tokens
                  and output 1 sits outside the mini-ledger holding an unrelated
                  policy.  K = 3004.
* `ctxResidual` — accepting, "residual output": 5 of the 9 seized tokens leave the
                  pair and land in output 1, which IS at the base credential.
                  This is the shape of both accepting seize goldens.  K = 3328.
* `ctxEscape`   — **the excluded case**: 6 seized tokens escape the mini-ledger
                  through a non-base output.  Ledger-legal, inside SHAPE S1, and
                  violating conjunct 2 — and the real bytecode REJECTS it, at
                  3800 and also at 20000 steps, so the rejection is genuine and
                  not budget exhaustion.

* `ctxStolen`   — **the other excluded case**, for conjunct 1: `ctxAccept` with the
                  continuing output's STAKING credential changed.  Every token
                  stays at the mini-ledger payment credential, so conjunct 2
                  holds, but the tokens are re-pointed at a different holder.
                  Ledger-legal, and REJECTED at 3800 and 20000 steps.

The two `ctx…` rejection instances are sharper controls than the tightness stanza: tightness only says
SOME accepting context satisfies the postcondition, whereas this exhibits the
specific ledger-legal context the postcondition EXCLUDES and shows the real CEK
refusing it.  Without it, "accept ⟹ contained" could have been
hypothesis-implied.
-/

namespace P2ShapedWitness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1 at a leaf assignment; the three instances differ only in the
quantities, the second output's credential and the two non-ada policies. -/
def mk (i0Qty o0Qty : Integer) (escH : ByteString) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (i1CS i1Tn : ByteString) (i1Qty : Integer) (mQ : Integer) : ScriptContext :=
  seizeShapedCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") i0Qty (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 i1CS i1Tn i1Qty
    (ByteString.mk "USERSTK") 300 o0Qty (ByteString.mk "DTM")
    escH 50 o1CS o1Tn o1Qty
    (ByteString.mk "MMM") (ByteString.mk "TOK") mQ
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    50

def ctxAccept : ScriptContext :=
  mk 10 12 (ByteString.mk "CHANGE") (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
     (ByteString.mk "ZZZP") (ByteString.mk "WT") 1 2

def ctxResidual : ScriptContext :=
  mk 9 4 (ByteString.mk "PROGLOGIC") (ByteString.mk "MMM") (ByteString.mk "TOK") 8
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

def ctxEscape : ScriptContext :=
  mk 10 4 (ByteString.mk "CHANGE") (ByteString.mk "MMM") (ByteString.mk "TOK") 9
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

/-- INSTANCE 4 — THE OTHER EXCLUDED CASE, for conjunct 1: `ctxAccept` with the
continuing output's STAKING credential changed from `USERSTK` to `THIEFSTK`, i.e.
a seizure that keeps the tokens at the mini-ledger payment credential but
re-points them at a different holder.  Ledger-legal, inside SHAPE S1, and
violating `seizeStructurePreserved`'s address clause.  Must be REJECTED. -/
def ctxStolen : ScriptContext :=
  seizeShapedCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") 10 (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "THIEFSTK") 300 12 (ByteString.mk "DTM")
    (ByteString.mk "CHANGE") 50 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
    (ByteString.mk "MMM") (ByteString.mk "TOK") 2
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- All three instances satisfy the theorems' ledger-normalization hypothesis IN
FULL — including `isBalanced`, which is what makes `ctxEscape` a legitimate
counterexample candidate rather than an impossible transaction. -/
theorem all_four_valid :
    validRewardingContext ctxAccept = true ∧
    validRewardingContext ctxResidual = true ∧
    validRewardingContext ctxEscape = true ∧
    validRewardingContext ctxStolen = true := by native_decide

/-- The two accepting instances satisfy BOTH conjuncts of P2, in the theorems'
EXACT form (mint term included); `ctxEscape` VIOLATES conjunct 2 at the seized
token name; `ctxStolen` VIOLATES conjunct 1.

The last conjunct pins the mint term as load-bearing: `WSC.mintOf` is 2 on
`ctxAccept`, whose inequality is `12 ≥ 10 + 2` — TIGHT.  Drop the mint term and
the statement would be strictly weaker; keep it and the accepting instance is on
the boundary, which is what one wants from a containment bound. -/
theorem postconditions_on_the_four_instances :
    WSC.seizeStructurePreserved (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "MMM") ctxAccept.scriptContextTxInfo.txInfoInputs
        ctxAccept.scriptContextTxInfo.txInfoOutputs = true ∧
    WSC.P2.sumOutAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxAccept.scriptContextTxInfo.txInfoOutputs
      ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          ctxAccept.scriptContextTxInfo.txInfoInputs
        + WSC.mintOf (ByteString.mk "MMM") (ByteString.mk "TOK")
            ctxAccept.scriptContextTxInfo.txInfoMint ∧
    WSC.P2.sumOutAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxResidual.scriptContextTxInfo.txInfoOutputs
      ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          ctxResidual.scriptContextTxInfo.txInfoInputs
        + WSC.mintOf (ByteString.mk "MMM") (ByteString.mk "TOK")
            ctxResidual.scriptContextTxInfo.txInfoMint ∧
    ¬ (WSC.P2.sumOutAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxEscape.scriptContextTxInfo.txInfoOutputs
      ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          ctxEscape.scriptContextTxInfo.txInfoInputs
        + WSC.mintOf (ByteString.mk "MMM") (ByteString.mk "TOK")
            ctxEscape.scriptContextTxInfo.txInfoMint) ∧
    WSC.seizeStructurePreserved (Credential.ScriptCredential (ByteString.mk "PROGLOGIC"))
        (ByteString.mk "MMM") ctxStolen.scriptContextTxInfo.txInfoInputs
        ctxStolen.scriptContextTxInfo.txInfoOutputs = false ∧
    WSC.mintOf (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxAccept.scriptContextTxInfo.txInfoMint = 2 := by native_decide

/-- **NON-VACUITY, EXECUTABLE.**  The real compiled bytecode ACCEPTS the
"nothing moves" instance at budget 3800, through the SHAPED applied term the
theorems above quantify over. -/
theorem exec_accepts_at_3800 :
    isSuccessful
      (appliedSeizeShaped3800.exec ppCS
        (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
          (ByteString.mk "MMM") (ByteString.mk "TOK") 10 (ByteString.mk "DTM")
        (ByteString.mk "WALLET") 100 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
        (ByteString.mk "USERSTK") 300 12 (ByteString.mk "DTM")
        (ByteString.mk "CHANGE") 50 (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
        (ByteString.mk "MMM") (ByteString.mk "TOK") 2
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
          (ByteString.mk "SEIZELOGIC")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
          (ByteString.mk "ZZILS") (ByteString.mk "GS")
        (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- …and the residual-output instance — the shape of the real accepting seize
goldens — is accepted too, through the same shaped term. -/
theorem exec_accepts_residual_at_3800 :
    isSuccessful
      (appliedSeizeShaped3800.exec ppCS
        (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
          (ByteString.mk "MMM") (ByteString.mk "TOK") 9 (ByteString.mk "DTM")
        (ByteString.mk "WALLET") 100 (ByteString.mk "MMM") (ByteString.mk "TOK") 1
        (ByteString.mk "USERSTK") 300 4 (ByteString.mk "DTM")
        (ByteString.mk "PROGLOGIC") 50 (ByteString.mk "MMM") (ByteString.mk "TOK") 8
        (ByteString.mk "MMM") (ByteString.mk "TOK") 2
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
          (ByteString.mk "SEIZELOGIC")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
          (ByteString.mk "ZZILS") (ByteString.mk "GS")
        (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED-CASE WITNESS.**  The escaping context is ledger-legal
(`all_four_valid`) and violates conjunct 2
(`postconditions_on_the_four_instances`), and the real compiled bytecode
REJECTS it — at the theorems' budget 3800 and also at 20000 steps, so this is a
genuine rejection and not budget exhaustion. -/
theorem exec_rejects_escaping_seize :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxEscape) 3800) = false ∧
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxEscape) 20000) = false := by native_decide

/-- **THE EXCLUDED-CASE WITNESS FOR CONJUNCT 1.**  `ctxStolen` is ledger-legal
(`all_four_valid`), keeps every token at the mini-ledger payment credential, and
differs from the accepting `ctxAccept` in ONE leaf: the continuing output's
staking credential.  `seizeStructurePreserved` is `false` on it
(`postconditions_on_the_four_instances`) and the real compiled bytecode REJECTS
it, at 3800 and at 20000 steps.  So the address clause of conjunct 1 is not
decoration: a seizure genuinely cannot re-point the continuing output at another
holder, and the shape can express the attempt. -/
theorem exec_rejects_stolen_staking_credential :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxStolen) 3800) = false ∧
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxStolen) 20000) = false := by native_decide

/-- **EXACT STEP COUNTS.**  K = 3004 for the "nothing moves" instance and
K = 3328 for the residual-output instance: each halts at its K and budget-errors
one step below.  (Measured by bisection in `WSC/Shaped/Probe/S1K.lean`; pinned
here as a theorem.)  For comparison the two accepting seize GOLDENS cost 2,570
and 4,647 steps (`WSC/goldens/K-MEASUREMENTS.md` §3), so SHAPE S1 sits in the same
step-count regime as the real off-chain transactions. -/
theorem K_is_3004_and_3328 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxAccept) 3004) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxAccept) 3003) = false
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual) 3328) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
              (WSC.seizeInputs ppCS ctxResidual) 3327) = false := by native_decide

end P2ShapedWitness

/-! ## AXIOM AUDIT -/

#print axioms WSC.P2a_shaped_structure
#print axioms WSC.P2b_shaped_containment
#print axioms WSC.P2_shaped
#print axioms WSC.P2ShapedWitness.exec_accepts_at_3800
#print axioms WSC.P2ShapedWitness.exec_rejects_escaping_seize
#print axioms WSC.P2ShapedWitness.exec_rejects_stolen_staking_credential

end WSC
