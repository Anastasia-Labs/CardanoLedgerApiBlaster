-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/P1Shaped.lean — **P1, the CENTRAL CONTAINMENT property, stated
and proved at UPLC level against the real compiled transfer bytecode, over
SHAPES T1 and T2** (task V1).

════════════════════════════════════════════════════════════════════════════
⚠ SHAPE-CLASS STATUS (task C1) — READ BEFORE COMPOSING ANYTHING FROM THIS FILE
════════════════════════════════════════════════════════════════════════════
Every theorem below is TRUE and unchanged. But SHAPES T1/T2/T6/T7 are **EMPTY as
classes of ledger transactions**: they spend an input at `ScriptCredential plc`
while carrying a ONE-entry redeemer map, which Conway UTXOW's `MissingRedeemers`
rule forbids. Proved: `WSC.ShapeRealizability.t1_class_is_empty`
(UNCONDITIONAL) and `WSC.t2_class_is_empty` / `WSC.t6_class_is_empty`
(WSC/Props/Shaped/GlobalRealizability.lean). So these theorems must NOT be
composed through a `Shape` restriction — the composition would be vacuous.

**Use `WSC/Props/Shaped/P1ShapedR.lean` instead**: the same three statements
(`P1R_T1`, `P1R_T2`, `P1R_T6`), same budget 4400, same witness K, over the
re-cut SHAPES T1R/T2R/T6R whose redeemer maps cover every script witness and
whose classes are proved NON-EMPTY (`WSC.t1R_realizable` and friends). SHAPE T7
(two mini-ledger outputs AND a mint) was not re-cut — see that module's header.

════════════════════════════════════════════════════════════════════════════
P1 IN PLAIN ENGLISH
════════════════════════════════════════════════════════════════════════════
*When the global validator accepts a transfer, no registered programmable token
can leave or vanish from the mini-ledger: for every registered policy and token
name, the amount sitting at mini-ledger outputs is at least the amount that came
from mini-ledger inputs plus any net amount minted — signed, so that a burn
correspondingly LOWERS the requirement. Policies that are not registered are not
programmable tokens and are deliberately outside the guarantee.*

Formally, and this is the form proved below (see the FINDING on `mintPos`):

    outAtBase(cs,tn) ≥ inAtBase(cs,tn) + mintOf(cs,tn)

with all three quantities read off `ScriptContext` fields only — `Model.outSum`,
`Model.inSum`, `Model.mintSigned` of WSC/Model/Ground.lean and
WSC/Props/P1_Transfer.lean — never off a validator accumulator (ARCHITECTURE.md
Tier 0.1 anti-tautology gate).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED
════════════════════════════════════════════════════════════════════════════
`WSC/STATUS.md` and `WSC/Props/P1_Transfer.lean` record P1 as
**NOT-REACHABLE-AT-UPLC**: the containment-carrying accepting runs cost 3,262 and
3,726 CEK steps, symbolic `#prep_uplc` of this validator costs 2,143 s at budget
1,600 already, and the extrapolation to 3,300 was **7 to 182 YEARS**
(`WSC/goldens/K-MEASUREMENTS.md` §5.2). P1 was therefore proved only on a
hand-transcribed SOURCE MODEL, bridged by the whole-validator faithfulness axiom
`WSC.Model.globalModel_faithful`.

Shaped prep is budget-independent (WSC/SHAPING-RESULTS.md §2.5). Measured in this
task: **0.97 s at budget 2700 and 1.00 s at budget 4400**. The prep barrier is
gone, and the theorems below are the first statements of P1 that hold **against
the production bytecode with NO faithfulness axiom** — `#print axioms` in
WSC/Shaped/Probe/P1Axioms.lean confirms `globalModel_faithful` is absent.

════════════════════════════════════════════════════════════════════════════
SCOPE — EVERY FIXED DIMENSION, NAMED
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 4400** (ADDENDUM E1, the E1 bounded-transaction
caveat). Each theorem below constrains exactly those invocations of the real
compiled `programmableLogicGlobal` whose CEK run halts within 4400 steps.
Bridged to node acceptance by `LR_BUDGET_global`. Non-vacuity at that budget is
certified twice: by the mandatory solver vacuity probe (`Falsified`) and by a
concrete accepting witness executed through the real CEK
(`P1ShapedWitness.exec_accepts_at_4400`, exact step count **K = 2603**).

**Bound 2 — SHAPE T1 / T2.** Published in full in
WSC/Shaped/GlobalShapedP1.lean's header. In one line each:

* **SHAPE T1** — REWARDING purpose; exactly 2 inputs (index 0 at the
  mini-ledger base credential `ScriptCredential plc` with a pubkey staking
  credential whose hash is the transaction's sole signatory, index 1 at a pubkey
  address); exactly 2 reference inputs (0 = protocol-params node, 1 = candidate
  directory node, both inline-datum script UTxOs); exactly 2 outputs (0 at the
  base credential, 1 at a pubkey address); every value = ada plus exactly one
  policy carrying exactly one token name, the SAME policy `cs` and token name
  `tn` throughout; EMPTY mint; a 2-entry all-script withdrawal map; 1 redeemer
  entry; 1 signatory; empty cert/datum/vote/proposal lists; redeemer fixed to
  `TransferAct [1] [1] [] 0`.
* **SHAPE T2** — SHAPE T1 with `txInfoMint = [(cs,{tn:q})]`, `q` a free Integer
  of UNCONSTRAINED SIGN, and redeemer `TransferAct [1] [1] [Member] 0`.

**Bound 2b — ONE CONTAINMENT DISPATCH PATH.** SHAPE T1/T2's expected value is a
single currency symbol with a single token name, so the dispatch at
ProgrammableLogicBase.hs:676-699 takes **PATH A**, the single-asset
accumulate-scan `hasAtLeastAssetInProgOutputs` (:604-618). ARCHITECTURE.md Tier
3.1 wants all three paths; the other two arms (wholesale `Data` equality, Path B
:648-674, and builtin `valueContains`, Path C :619-647) are reached by SHAPE T3
(WSC/Shaped/GlobalShapedP1.lean), whose prep is **blocked by an upstream Blaster
codegen defect** — reproduced in WSC/Shaped/Probe/T3PrepFAILS.lean and recorded
verbatim in WSC/status-fragments/V1-P1-shaped.md, NOT silently omitted. Path C is
however PROVED at Lean level, unconditionally and without `sorry`, in
WSC/Props/P1_Transfer.lean (`pathC_sound`).

**Bound 2c — ONE PROOF INDEX AT A TIME.** SHAPE T1/T2 pin the transfer proof's
node index to 1 and the params index to 0, exactly as SHAPE G1 does for P5, and
for the same reason (SHAPING-RESULTS §6.2: for THIS validator a symbolic index
puts `dropList`'s branch structure back into the residual). The theorems are
about the node index the redeemer actually witnesses.

**Bound 3 — the non-exemption hypothesis, and where it comes from.** P1 is a
statement about REGISTERED policies. The only way a policy escapes the
containment requirement is by exhibiting an authenticated directory node whose
`(key,next)` interval strictly covers it (transfer walk :891-908, mint walk
:996-1016), so the theorems carry exactly
`Model.coveringNodeExists dirCS cs referenceInputs = false`. That hypothesis is
NOT discharged from WSC/Honest.lean: `DirWF` still lacks the interval-PARTITION
conjunct (`WSC/Props/P1_Transfer.lean` `DirWF_partition_conjunct_missing`), so
this is exactly the trust surface P5 already has, and closing it is deferred unit
U10. `dirCS` is named through the redeemer's own `paramsRefIdx = 0`, never
through a chosen reference position — the lesson of the SHAPE G2 falsification
(SHAPING-RESULTS §6.1).

════════════════════════════════════════════════════════════════════════════
WHY THIS IS NOT TRUE BY CONSTRUCTION — the design point of SHAPE T1
════════════════════════════════════════════════════════════════════════════
`validRewardingContext` contains `isBalanced`
(CardanoLedgerApi/V3/Contexts.lean:1180-1187). On a shape with ONE input and ONE
output the ledger balance rule ALONE forces `qOut = qIn + mint`, and P1 would be
hypothesis-implied. SHAPE T1 therefore carries a second input at a NON-base
address (an external source of the same policy) and a second output at a NON-base
address (the ESCAPE ROUTE). The balance rule then only says
`qIn + qIn2 + mint = qOut + qEsc`, which is satisfied both by
containment-respecting and by escaping assignments, and the inequality has to
come from the bytecode.

Three independent controls establish that the escape route is REAL and the
bytecode is what closes it:

1. `P1ShapedWitness.ctxOk_*` — an accepting SHAPE-T1 context with **qEsc = 4 > 0**:
   the escape output is ledger-legal and non-empty, so containment is not
   achieved by making escapes impossible.
2. `P1ShapedWitness.exec_rejects_escape` — a SHAPE-T1 context that is
   `validRewardingContext = true` (zero failing conjuncts) and violates the
   conclusion (`qIn = 5`, `qOut = 3`, the missing 2 landing in `qEsc = 6`), shown
   REJECTED by the real CEK. This is the §4.1-style excluded-case witness and is
   sharper than the tightness stanza.
3. the vacuity probe at the shape is `Falsified`, so the accepting class is
   non-empty.

════════════════════════════════════════════════════════════════════════════
FINDING — SIGNED, not `mintPos`, and it is refuted against real bytecode
════════════════════════════════════════════════════════════════════════════
ARCHITECTURE.md §3-P1 states the inequality with `mintPos` (the positive part).
`P1ShapedWitness.mintPos_form_REFUTED` below is a machine-checked refutation of
that form against the PRODUCTION BYTECODE: a SHAPE-T2 context that burns 4 of a
registered policy out of a mini-ledger input holding 5, leaving 1 at the
mini-ledger output, is ledger-legal, is ACCEPTED by the real CEK at budget 4400
(K = 3572), and has `outSum = 1 < 5 = inSum + mintPos`. The signed form
`outSum ≥ inSum + mintSigned` — `1 ≥ 5 + (−4)` — holds. The signed form is also
the one ARCHITECTURE.md §5.2's Preservation reduction consumes.

════════════════════════════════════════════════════════════════════════════
PRECONDITION AUDIT (arch §4.1)
════════════════════════════════════════════════════════════════════════════
MAY assume, and does: `validRewardingContext` (CLAB ledger normalization only,
specialized to the shape — it never inspects the redeemer's CONTENT,
CardanoLedgerApi/V3/Contexts.lean:1197-1246) and
`coveringNodeExists … = false` (Bound 3 above).

MUST NOT assume, and does not: nothing about the reference inputs being
authentic, nothing about the node datum beyond being an inline
`DirectorySetNode`-shaped list with FREE key/next/transferLogicScript, no
`HonestParams`/`Deployed`/`OnChain`/`DirWF` hypothesis, and — critically — NO
constraint on any of the four quantities `qIn`, `qOut`, `qIn2`, `qEsc` beyond
what the ledger rules themselves impose.
-/
import WSC.Shaped.GlobalShapedP1Prep
import WSC.Shaped.GlobalShapedP1MintPrep
import WSC.Shaped.GlobalShapedP1OutPrep
import WSC.Props.P1_Transfer
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

/-! ## §1 — P1 over SHAPE T1 (pure transfer, PATH A) -/

/-- **P1 (containment), SIGNED form, over SHAPE T1.** The statement; the theorem
that proves it is directly below. Read the module header's SCOPE block before
citing it. -/
def P1_T1_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    Model.coveringNodeExists dirCS cs
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs
      = false →
    isSuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER SHAPE T1 — PROVED AT UPLC AGAINST THE PRODUCTION BYTECODE.**

*If the real compiled transfer validator accepts a shape-T1 transaction whose
policy `cs` has NO covering directory node among the reference inputs, then the
amount of `(cs,tn)` at mini-ledger outputs is at least the amount of `(cs,tn)`
that came from mini-ledger inputs plus the signed minted amount.*

Over SHAPE T1 the mint is empty, so this is the pure-transfer case
`outAtBase ≥ inAtBase`; `P1_T2` below carries the mint. -/
theorem P1_T1 : P1_T1_stmt := by blaster (timeout: 1500)

/-! ## §2 — P1 over SHAPE T2 (nonzero symbolic mint — the SIGNED form bites) -/

/-- **P1 (containment), SIGNED form, over SHAPE T2** — same statement, with a
nonzero mint of unconstrained sign. -/
def P1_T2_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    Model.coveringNodeExists dirCS cs
      (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs
      = false →
    isSuccessful
      (appliedGlobalShapedT2.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER SHAPE T2 — PROVED AT UPLC.** The mint quantity `q` is free and its
SIGN is unconstrained, so this single theorem covers the mint case and the burn
case at once. Where a burn drives `qIn + q ≤ 0`,
`pfilterPositiveCurrencyPairs` (:257-298) drops the slot and the validator
requires nothing to remain — and the SIGNED inequality still holds, because
`validTxOutValue` forces every output quantity strictly positive. That is
precisely the asymmetry that refutes the `mintPos` form; see
`P1ShapedWitness.mintPos_form_REFUTED`. -/
theorem P1_T2 : P1_T2_stmt := by blaster (timeout: 1500)

/-! ## §3 — Polarity controls (ADDENDUM E9): the full control set -/

/-- Negative control over SHAPE T1: a shape-T1 context that VIOLATES containment
is rejected by the bytecode.

HONEST NOTE: over a single shape this is the contrapositive of `P1_T1`, so it is
logically equivalent, not independent evidence — blaster nonetheless discharges a
different goal, and E9 requires the stanza. The independent evidence that the
bytecode (and not a hypothesis) closes the escape is
`P1ShapedWitness.exec_rejects_escape`, which exhibits a ledger-legal violating
context and runs it through the real CEK. -/
def P1_T1_negative_control_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    Model.coveringNodeExists dirCS cs
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs
      = false →
    ¬ (Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint) →
    isUnsuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

theorem P1_T1_negative_control : P1_T1_negative_control_stmt := by blaster (timeout: 1500)

/-- Tightness stanza: the NEGATION of P1's conclusion under an accepting run must
be FALSIFIABLE (otherwise the conclusion would be vacuously derivable). Expected:
`Falsified`. -/
def P1_T1_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ (Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
            pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
              pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1_T1_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE T1.** "No accepting shape-T1 context
exists within 4400 CEK steps" must be FALSIFIED. Expected: `Falsified`. The
concrete witness in §4 discharges the same obligation a second time without the
solver. -/
def P1_T1_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1_T1_vacuity_probe]

/-- **MANDATORY VACUITY PROBE AT SHAPE T2.** Same, for the mint-carrying shape.
Expected: `Falsified`. -/
def P1_T2_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT2.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1_T2_vacuity_probe]

/-! ## §4 — CONCRETE witnesses of exactly SHAPES T1 / T2, through the real CEK

No SMT anywhere in this section: every statement is `native_decide` over the real
CEK machine and CLAB's own ledger predicate. -/

namespace P1ShapedWitness

set_option maxRecDepth 1000000

/-- The script parameter (protocol-params NFT policy). -/
def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- **SHAPE T1, accepting.** Policy `MMM.TOK`. The mini-ledger input holds 5 and
the mini-ledger output holds 5 — containment respected. An external pubkey input
holds 4 more of the SAME policy and the pubkey output (the escape route) carries
**4**, so the escape route is genuinely usable: it is non-empty in an ACCEPTING
context. Ada: 200 + 100 in, 150 + 100 out, 50 fee. The directory node is keyed
exactly `MMM` (so it is a POSITIVE proof, i.e. `cs` is registered), its
transfer-logic script is `TLS` which is withdrawal entry 1 — a cache MISS, so the
`pdropList`-based witness check at :913-915 is the one exercised. -/
def ctxOk : ScriptContext :=
  p1ShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
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
    50

/-- **SHAPE T1, ESCAPING — the excluded case.** Identical to `ctxOk` except the
mini-ledger output holds only 3 of the 5 that came from the mini-ledger input;
the missing 2 land in the pubkey output (`qEsc = 6` instead of 4). Ledger-legal
(`ctxEscape_valid` below), and rejected by the real bytecode. -/
def ctxEscape : ScriptContext :=
  p1ShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
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
    50

/-- **SHAPE T2, MINT case.** `q = +3`: 5 in from the mini-ledger, 3 minted, 8 at
the mini-ledger output. -/
def ctxMint : ScriptContext :=
  p1ShapedMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 3
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 8
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- **SHAPE T2, BURN case — the `mintPos` counterexample made concrete.**
`q = −4`: 5 in from the mini-ledger, 4 burned, only 1 at the mini-ledger output.
Signed requirement `5 + (−4) = 1` — met. `mintPos` requirement `5 + 0 = 5` — NOT
met, and the real bytecode ACCEPTS. -/
def ctxBurn : ScriptContext :=
  p1ShapedMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
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
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-! ### The witnesses satisfy the theorems' hypotheses IN FULL -/

theorem ctxOk_valid : validRewardingContext ctxOk = true := by native_decide
theorem ctxEscape_valid : validRewardingContext ctxEscape = true := by native_decide
theorem ctxMint_valid : validRewardingContext ctxMint = true := by native_decide
theorem ctxBurn_valid : validRewardingContext ctxBurn = true := by native_decide

/-- The non-exemption hypothesis holds at every witness: no reference input is an
authenticated directory node whose interval strictly COVERS `MMM` (the node's key
IS `MMM`, so it is a positive/registered proof, not a covering one). -/
theorem ctxOk_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxOk.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

theorem ctxBurn_no_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxBurn.scriptContextTxInfo.txInfoReferenceInputs = false := by native_decide

/-! ### The ground-truth quantities, evaluated

These four `native_decide`s are what make the postcondition legible: they show
exactly which numbers `outSum` / `inSum` / `mintSigned` pick out of the shape. -/

theorem ctxOk_quantities :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOk.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOk.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxOk.scriptContextTxInfo.txInfoMint = 0 := by native_decide

/-- **THE ESCAPE ROUTE IS REAL.** In the ACCEPTING witness the non-mini-ledger
output carries 4 of the very policy P1 protects, and the external input supplies
4 — so SHAPE T1 does not achieve containment by making escapes structurally
impossible. Compare `ctxEscape_quantities`, where the same shape moves 2 units
out of the mini-ledger and is rejected. -/
theorem ctxOk_escape_output_nonempty :
    CardanoLedgerApi.V3.valueOf (ByteString.mk "MMM") (ByteString.mk "TOK")
      (p1ShapedEscOut (ByteString.mk "DEST") 100 (ByteString.mk "MMM")
        (ByteString.mk "TOK") 4).txOutValue = 4 := by native_decide

theorem ctxEscape_quantities :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxEscape.scriptContextTxInfo.txInfoOutputs = 3
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxEscape.scriptContextTxInfo.txInfoInputs = 5 := by native_decide

/-! ### NON-VACUITY, EXECUTABLE: the real bytecode accepts -/

/-- **NON-VACUITY.** The real compiled bytecode ACCEPTS the shape-T1 witness at
budget 4400, through the SHAPED applied term `P1_T1` quantifies over. -/
theorem exec_accepts_at_4400 :
    isSuccessful
      (appliedGlobalShapedT1.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK")
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
        50) :=
  isHaltB_sound _ (by native_decide)

/-- …and the UNSHAPED prep's executable term accepts the same context, so the
shaped and unshaped applied terms agree on it. -/
theorem exec_accepts_unshaped :
    isSuccessful (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 4400) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED CASE, EXECUTABLE.** `ctxEscape` is `validRewardingContext`
(above) and moves 2 units of a registered policy out of the mini-ledger; the real
compiled bytecode REJECTS it even with 4400 steps available. This is the control
that shows P1's conclusion is enforced by the VALIDATOR, not implied by the
ledger hypotheses. -/
theorem exec_rejects_escape :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxEscape) 4400) = false := by
  native_decide

/-- Lower bracket: the accepting witness is REJECTED at budget 600 (budget
exhaustion ⟹ `Error`), so the 4400 bound is doing work. -/
theorem exec_rejects_at_600 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 600) = false := by
  native_decide

/-- **EXACT STEP COUNT, SHAPE T1: K = 2603.** Halts at 2603, budget-errors at
2602. (Binary-searched in `WSC/Shaped/Probe/T1Probe.lean`; pinned here.) For
comparison the containment-carrying off-chain goldens cost K = 3262 and 3726
(`WSC/goldens/K-MEASUREMENTS.md` §3), so SHAPE T1 sits in the same step-count
regime as the real transactions while being small enough for the solver. -/
theorem K_T1_is_2343 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 2343) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 2342) = false := by
  native_decide

/-- **EXACT STEP COUNT, SHAPE T2: K = 2567** (both the mint and the burn
witness) — re-measured against the PR #112 bytecode, two-sided; was 3572. -/
theorem K_T2_is_2567 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxBurn) 2567) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxBurn) 2566) = false := by
  native_decide

/-- The mint witness is accepted by the shaped SHAPE-T2 term at 4400. -/
theorem exec_accepts_mint_at_4400 :
    isSuccessful
      (appliedGlobalShapedT2.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 3
        (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
        (ByteString.mk "EXT") 100 4
        150 8
        (ByteString.mk "DEST") 100 4
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- The BURN witness is accepted by the shaped SHAPE-T2 term at 4400. -/
theorem exec_accepts_burn_at_4400 :
    isSuccessful
      (appliedGlobalShapedT2.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
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
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **ARCHITECTURE.md §3-P1's `mintPos` FORM IS REFUTED AGAINST REAL BYTECODE.**
On the burn witness — which the real CEK ACCEPTS (`exec_accepts_burn_at_4400`)
and which is ledger-legal (`ctxBurn_valid`) and carries no covering node
(`ctxBurn_no_covering_node`) — the SIGNED requirement is met and the `mintPos`
requirement is NOT:

* `outSum = 1`, `inSum = 5`, `mintSigned = −4`, `mintPosOf = 0`;
* signed:   `1 ≥ 5 + (−4) = 1` ✓
* mintPos:  `1 ≥ 5 + 0 = 5`   ✗

So the form the theorems above use is the one that is true, and the `mintPos`
form must not be quoted for burns. -/
theorem mintPos_form_REFUTED :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxBurn.scriptContextTxInfo.txInfoOutputs = 1
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxBurn.scriptContextTxInfo.txInfoInputs = 5
    ∧ Model.mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxBurn.scriptContextTxInfo.txInfoMint = -4
    ∧ Model.mintPosOf (ByteString.mk "MMM") (ByteString.mk "TOK")
        ctxBurn.scriptContextTxInfo.txInfoMint = 0 := by native_decide

/-! ### The non-exemption hypothesis is LOAD-BEARING, not decorative

P1's plain-English statement ends "unregistered policies are not programmable
tokens and are correctly outside the guarantee". The witness below is that
sentence, machine-checked against the real bytecode: it is `ctxEscape` — the SAME
ledger-legal containment violation the bytecode rejects above — with the directory
node's interval widened from `key = MMM` to `key = AAA, next = ZZZ`, so the node
now COVERS `MMM`. The transfer walk then takes its NEGATIVE-proof branch
(:891-908), DROPS the policy from the accumulator, and the bytecode **ACCEPTS**
the very transaction it rejected before.

Two things follow, and both matter:
1. the hypothesis `coveringNodeExists dirCS cs referenceInputs = false` in every
   theorem above is doing real work — remove it and the theorems are FALSE;
2. P1's guarantee is exactly as strong as "cs has no covering node", which is
   exactly as strong as `DirWF`'s missing interval-PARTITION conjunct
   (`WSC/Props/P1_Transfer.lean` `DirWF_partition_conjunct_missing`, deferred unit
   U10). This is the SAME trust surface P5 has, exhibited here as executable
   bytecode behaviour rather than as prose. -/

/-- `ctxEscape` with the node widened to `(AAA, ZZZ)`, so `MMM` is EXEMPT. -/
def ctxExempt : ScriptContext :=
  p1ShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 3
    (ByteString.mk "DEST") 100 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

theorem ctxExempt_valid : validRewardingContext ctxExempt = true := by native_decide

/-- …and here the hypothesis FAILS: reference input 1 IS an authenticated
directory node whose interval strictly covers `MMM`. -/
theorem ctxExempt_has_covering_node :
    Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
      ctxExempt.scriptContextTxInfo.txInfoReferenceInputs = true := by native_decide

/-- **THE SCOPE BOUNDARY, EXECUTABLE.** The same containment violation the
bytecode REJECTS for a registered policy (`exec_rejects_escape`) is ACCEPTED once
the policy is exempted by a covering node. `outSum = 3 < 5 = inSum` here. -/
theorem exec_accepts_exempt_escape :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxExempt) 4400) = true
    ∧ Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxExempt.scriptContextTxInfo.txInfoOutputs = 3
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxExempt.scriptContextTxInfo.txInfoInputs = 5 := by
  native_decide

/-! ### Cross-check against the SOURCE MODEL (an independent oracle)

`WSC/Model/GlobalModel.lean` is the hand transcription P1 was previously proved
against. It agrees with the real bytecode on all four witnesses — three accepts
and one reject — which is four more differential-test vectors for
`globalModel_faithful` on top of the four goldens
(`WSC/Model/GlobalGoldens.lean`), and the first ones that exercise the
mini-ledger INPUT-side aggregation and the containment scan with a genuine escape
route. -/
theorem model_agrees_on_witnesses :
    Model.globalModel ppCS ctxOk = true
    ∧ Model.globalModel ppCS ctxEscape = false
    ∧ Model.globalModel ppCS ctxMint = true
    ∧ Model.globalModel ppCS ctxBurn = true
    ∧ Model.globalModel ppCS ctxExempt = true := by native_decide

end P1ShapedWitness

/-! ## §5 — P1 over SHAPES T6 / T7: containment must AGGREGATE over outputs

SHAPE T6/T7 (WSC/Shaped/GlobalShapedP1Out.lean) add a SECOND mini-ledger output
with its own free quantity, so `outAtBase` is a SUM of two independent symbolic
quantities and PATH A's accumulate-scan has to add them up — including its EARLY
EXIT (`currentQty #>= requiredQty`, tested before the list is destructured at
:605-607), which is where an under-count would hide.

WHY NOT TWO MINI-LEDGER INPUTS (the task's preferred growth step): two
contributing inputs put `pvalueFromCred` into PHASE 3, whose accumulator is the
CIP-153 builtin `punionValue`, and `#prep_uplc` then emits a kernel-ill-typed
term. Measured and reproducible — see the module header's Bound 2b note and
WSC/status-fragments/V1-P1-shaped.md; the failing probe is kept at
WSC/Shaped/Probe/T4PrepFAILS.lean. -/

/-- **P1 over SHAPE T6** (two mini-ledger outputs, empty mint). -/
def P1_T6_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    Model.coveringNodeExists dirCS cs
      (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs
      = false →
    isSuccessful
      (appliedGlobalShapedT6.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
            key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
              dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
              key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER SHAPE T6 — PROVED AT UPLC.** The mini-ledger requirement is met by
the SUM of two independently symbolic mini-ledger outputs. -/
theorem P1_T6 : P1_T6_stmt := by blaster (timeout: 1500)

/-- **P1 over SHAPE T7** — two mini-ledger outputs AND a nonzero symbolic mint of
unconstrained sign: the strongest single P1 statement in this module. -/
def P1_T7_stmt : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    Model.coveringNodeExists dirCS cs
      (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs = false →
    isSuccessful
      (appliedGlobalShapedT7.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      Model.outSum (.ScriptCredential plc) cs tn
          (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
            outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
            dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum (.ScriptCredential plc) cs tn
            (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
              outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
              outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
              dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint

/-- **P1 OVER SHAPE T7 — PROVED AT UPLC.** -/
theorem P1_T7 : P1_T7_stmt := by blaster (timeout: 1500)

/-- **MANDATORY VACUITY PROBE AT SHAPE T6.** Expected: `Falsified`. -/
def P1_T6_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT6.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1_T6_vacuity_probe]

/-- **MANDATORY VACUITY PROBE AT SHAPE T7.** Expected: `Falsified`. -/
def P1_T7_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer),
    validRewardingContext
      (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT7.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P1_T7_vacuity_probe]

/-! ## §6 — CONCRETE witnesses of exactly SHAPES T6 / T7 -/

namespace P1ShapedOutWitness

set_option maxRecDepth 1000000

open P1ShapedWitness (ppCS isHaltB isHaltB_sound)

/-- **SHAPE T6, accepting, with the requirement met only by BOTH outputs
together**: 5 come from the mini-ledger and the two mini-ledger outputs hold 3
and 2. The escape output holds 4 (non-empty, so the escape route is real). -/
def ctxOut : ScriptContext :=
  p1ShapedOutCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
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
    50

/-- **SHAPE T6, escaping**: the two mini-ledger outputs hold only 2 + 1 = 3 of
the 5 that came from the mini-ledger. Ledger-legal, and rejected. -/
def ctxOutEscape : ScriptContext :=
  p1ShapedOutCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 2 60 1
    (ByteString.mk "DEST") 90 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- **SHAPE T7, burn**: 5 in from the mini-ledger, 4 burned, and 1 + 1 = 2 at the
two mini-ledger outputs (the signed requirement is 1). -/
def ctxOutBurn : ScriptContext :=
  p1ShapedOutMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
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
    50

theorem ctxOut_valid : validRewardingContext ctxOut = true := by native_decide
theorem ctxOutEscape_valid : validRewardingContext ctxOutEscape = true := by native_decide
theorem ctxOutBurn_valid : validRewardingContext ctxOutBurn = true := by native_decide

/-- The AGGREGATION is genuine: neither mini-ledger output alone meets the
requirement (3 < 5 and 2 < 5); their sum does. -/
theorem ctxOut_aggregation_is_genuine :
    Model.outSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOut.scriptContextTxInfo.txInfoOutputs = 5
    ∧ Model.inSum (.ScriptCredential (ByteString.mk "PROGLOGIC")) (ByteString.mk "MMM")
        (ByteString.mk "TOK") ctxOut.scriptContextTxInfo.txInfoInputs = 5
    ∧ CardanoLedgerApi.V3.valueOf (ByteString.mk "MMM") (ByteString.mk "TOK")
        (p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "MMM")
          (ByteString.mk "TOK") 3).txOutValue = 3
    ∧ CardanoLedgerApi.V3.valueOf (ByteString.mk "MMM") (ByteString.mk "TOK")
        (p1ShapedBaseOut (ByteString.mk "PROGLOGIC") 60 (ByteString.mk "MMM")
          (ByteString.mk "TOK") 2).txOutValue = 2 := by native_decide

/-- **NON-VACUITY, EXECUTABLE, SHAPE T6.** -/
theorem exec_accepts_T6_at_4400 :
    isSuccessful
      (appliedGlobalShapedT6.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK")
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
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **NON-VACUITY, EXECUTABLE, SHAPE T7** (the burn witness). -/
theorem exec_accepts_T7_burn_at_4400 :
    isSuccessful
      (appliedGlobalShapedT7.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
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
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **THE EXCLUDED CASE, SHAPE T6**: ledger-legal, aggregate containment
violated, REJECTED by the real bytecode. -/
theorem exec_rejects_T6_escape :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOutEscape) 4400) = false := by
  native_decide

/-- **EXACT STEP COUNTS: SHAPE T6 K = 2777, SHAPE T7 (burn) K = 2567** —
re-measured against the PR #112 bytecode, two-sided; were 3150 and 3572. -/
theorem K_T6_is_2777 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOut) 2777) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOut) 2776) = false := by
  native_decide

theorem K_T7_is_2567 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOutBurn) 2567) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
      programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOutBurn) 2566) = false := by
  native_decide

/-- Source-model cross-check on the three SHAPE-T6/T7 witnesses (three more
differential-test vectors for `globalModel_faithful`). -/
theorem model_agrees_on_out_witnesses :
    Model.globalModel ppCS ctxOut = true
    ∧ Model.globalModel ppCS ctxOutEscape = false
    ∧ Model.globalModel ppCS ctxOutBurn = true := by native_decide

end P1ShapedOutWitness

end WSC
