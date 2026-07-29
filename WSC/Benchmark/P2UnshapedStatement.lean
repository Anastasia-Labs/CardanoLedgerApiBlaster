/-
WSC/Benchmark/P2UnshapedStatement.lean — **THE REVIEWABLE HALF of the UNSHAPED
P2 benchmark. THIS MODULE BUILDS.** Its companion
`WSC/Benchmark/P2Unshaped.lean` does not, deliberately, and says so in its own
banner. Read `WSC/Benchmark/P1UnshapedStatement.lean`'s header first — the split,
the reasoning about the added hypotheses, and the `accept`-abstraction caveat are
the same and are not repeated at length here.

════════════════════════════════════════════════════════════════════════════
WHAT P2 SAYS, AND WHY IT HAS TWO CONJUNCTS
════════════════════════════════════════════════════════════════════════════
When the seize (clawback) validator accepts, it may only move the ONE policy
being seized:

* **(a) STRUCTURE PRESERVATION.** Walking the transaction's inputs in order, each
  input at the mini-ledger base credential is paired with the next output of the
  paired-output cursor, and that pair has the same address (STAKING CREDENTIAL
  INCLUDED), the same datum, the same reference script, and identical holdings of
  every policy other than the seized one and other than ada; ada may only be
  TOPPED UP, never reduced. Inputs outside the mini-ledger consume no output.
  Postcondition: `WSC.seizeStructurePreservedAdaTopUp` (`WSC/Spec.lean`).

* **(b) CONTAINMENT OF THE SEIZED DELTA.** For EVERY token name, the total
  holding of the seized policy at outputs on the mini-ledger base credential is
  at least the total at inputs spent from it, plus the SIGNED net mint of that
  asset. Postcondition: `WSC.P2.sumOutAtBase ≥ WSC.P2.sumInAtBase + WSC.mintOf`
  (`WSC/Props/P2_Seize.lean`, `WSC/Spec.lean:45`).

Both are PROVED against the production bytecode over the shaped class S1R —
`WSC.P2a_R_structure` and `WSC.P2b_R_containment` in
`WSC/Props/Shaped/P2ShapedR.lean`, with (b) additionally proved over the
two-token-name generalisation S1R2 as `WSC.P2b_R2_containment`
(`WSC/Props/Shaped/P2ShapedR2.lean`). This module states the UNSHAPED versions.

The ada clause of (a) is an INEQUALITY IN ONE DIRECTION and that asymmetry is the
security-relevant half: PR #112 legalised an ada top-up on purpose (raising
min-UTxO must not make a UTxO permanently unseizable), and
`WSC.P2a_R_ada_only_tops_up` proves the direction is real. `pairPreserved` with
ada EQUALITY is ❌ FALSIFIED against production — do not restore it.

════════════════════════════════════════════════════════════════════════════
THE THREE HYPOTHESES THE SHAPE SUPPLIED BY CONSTRUCTION
════════════════════════════════════════════════════════════════════════════
`P2a_R_structure` quantifies ~50 scalar leaves and names three objects the
POSTCONDITION talks about, each of which SHAPE S1R ties to the transaction by
construction:

| object | shaped, by construction | unshaped, as a hypothesis |
|---|---|---|
| the seized policy `key` | position 0 of the datum of reference input `dirIdx = 1` | `SeizeModel.seizedPolicyOf ctx = some key` |
| the base credential `plc` | position 1 of the params datum at `paramsIdx = 0` | `progLogicCredPublishedBySeize ctx = some (toData (ScriptCredential plc))` |
| the paired-output cursor | `outputsStartIdx = 0`, so the whole output list | `SeizeModel.pairedOutputsOf ctx = some pairedOuts` |

The right column is **not optional**, for exactly the reason spelled out in
`P1UnshapedStatement.lean`'s header: with `key` and `plc` freely quantified over
an arbitrary `ctx` the statement is FALSE, not merely weaker (pick a `plc` the
transaction never mentions and a `key` it does move, and (b) reads `0 ≥ 0 + q`).

`seizedPolicyOf` and `pairedOutputsOf` are used BY NAME: they are the audited
ledger-only projections of `WSC/Model/SeizeModel.lean` §6, they are the very
quantities ARCHITECTURE.md §3-P2 and `WSC/Props/P2_Seize.lean` write P2 over, and
`WSC/Props/Shaped/P2ShapedR.lean`'s "§Projection audit" (`shapeR_seizedPolicy`,
`shapeR_pairedOutputs`, `shapeR_progLogicCred`) exists precisely to license
reading the shaped theorems as P2 specialised to S1R. Nothing here touches
`SeizeModel.seizeModel`, the transcription whose fidelity axiom was retracted at
task R1 — these three are pure `ScriptContext` projections.

**Why `paramsPublishedBySeize` and not `SeizeModel.progLogicCredDataOf`.** The
latter also applies the `phasCSH ppCS` authentication gate
(ProgrammableLogicBase.hs:832). Omitting the gate makes the hypothesis WEAKER and
therefore the statement STRONGER — it quantifies over contexts whose params UTxO
is unauthenticated too, and those are contexts the bytecode ERRORS on, so the
obligation is discharged there by the `accept` hypothesis rather than by an
assumption. It also keeps §3's specialisations free of a side condition: with the
gate in, each would have to assume `pCS = ppCS`, exactly as
`WSC.shapeR_progLogicCred` does, and that equation is only available from the
accept path (`WSC.P2_R_gates_are_earned` proves accept forces it). Same choice,
same reason, as `WSC/Benchmark/P1UnshapedStatement.lean`'s `paramsPublishedBy`.

════════════════════════════════════════════════════════════════════════════
CONJUNCT (a) IN THIS FORM IS ALREADY A PROVED LEAN THEOREM — ABOUT THE MODEL
════════════════════════════════════════════════════════════════════════════
`WSC.P2.P2a_seizeModel_preserves_structure` (`WSC/Props/P2_Seize.lean:254`) is
`P2aUnshapedForm`, hypothesis for hypothesis, with TWO differences:

| that theorem | `P2aUnshapedForm accept` |
|---|---|
| `seizeModel ppCS ctx = true` (the hand TRANSCRIPTION) | `accept ppCS ctx` (the real BYTECODE's prepped residual) |
| — | `validRewardingContext ctx` (the ledger rule; needed on the bytecode side for canonicity) |
| `seizedPolicyOf ctx = some seizedCS` | identical |
| `pairedOutputsOf ctx = some paired` | identical |
| `progLogicCredDataOf ppCS ctx = some (toData base)` | `progLogicCredPublishedBySeize ctx = some (toData base)` — same read, gate omitted |
| `seizeStructurePreserved base seizedCS ins paired = true` | `seizeStructurePreservedAdaTopUp …` — the **PR #112** pair rule |

and it is proved **UNCONDITIONALLY IN THE LEAN KERNEL, for an ARBITRARY `ctx`,
with no shape and no well-formedness side conditions.** So the *shape* of the
unshaped P2a statement — including the choice of a general `base : Credential`,
the three `Option` naming hypotheses and the walk-and-pair postcondition — is not
invented here; it is the published §3-P2 statement, and it is known to be
provable at this level of generality about *something*. What the benchmark asks is
that it be provable about the COMPILED PROGRAM, which the retracted
`seizeModel_faithful` axiom no longer provides.

The one postcondition change is mandatory, not cosmetic: `seizeStructurePreserved`
(ada EQUALITY) is ❌ FALSIFIED against the post-#112 bytecode, measured, with a
counterexample whose sole defect is an ada top-up. `P2bUnshapedForm` likewise
mirrors `WSC.P2.P2b_seized_delta_contained` (`WSC/Props/P2_Seize.lean:300`), which
is STATED at the same generality and is the conjunct the source-model route could
not close.

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE DOES NOT ESTABLISH
════════════════════════════════════════════════════════════════════════════
1. It does NOT prove P2 unshaped. No prep is mentioned; the obligations are in
   the companion module and are OPEN.
2. §3 abstracts the accept predicate, so it does not derive the shaped THEOREMS
   from a hypothetical unshaped one — `appliedSeizeU3800.prop` and
   `appliedSeizeRShaped3800.prop` are two different `Optimize.main` outputs and
   this library has measured that prep residuals are not definitionally
   interchangeable (audit F8, docs/LIMITATIONS.md §5).
3. DEFECT D4 is NOT inherited. SHAPE S1R shares one payment-credential variable,
   one non-ada policy variable and one token-name variable between input 0 and
   output 0, and forces `txOutReferenceScript := none` on both; those are honest
   scope losses OF THE SHAPE. The unshaped statement below has none of them —
   which is a large part of what makes it the property we actually want.
-/
import WSC.Props.Shaped.P2ShapedR
import WSC.Props.Shaped.P2ShapedR2

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Benchmark

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §1 — the base-credential hypothesis, in ground truth only -/

/-- `plgrParamsRefIdx` — the FIFTH field of `PSeizeAct`
(ProgrammableLogicBase.hs:1061, position 4; `WSC/Redeemer.lean` transcribes the
six fields and verified them unchanged by PR #112). The arm is reached
positionally and constructor index 0 is `PTransferAct`, which this validator
rejects outright (`SeizeModel.seizeFieldsOf`, :1298); ANY other index is treated
as `PSeizeAct` by the generated dispatch, which is why the second pattern is
`Data.Constr _` and not `Data.Constr 1`. -/
def seizeParamsRefIdx : Data → Option Integer
  | Data.Constr 0 _ => none
  | Data.Constr _ (_ :: _ :: _ :: _ :: Data.I p :: _) => some p
  | _ => none

/-- **The protocol-params datum this seize transaction publishes**, read the way
`pparamsAtRefIdx` reads it (ProgrammableLogicBase.hs:824-838) MINUS the
`phasCSH ppCS` gate — see the module header for why the gate is deliberately left
to the bytecode. `dropL` clamps a negative index exactly as the raw `pdropList`
at :1307 does; position 1 is kept as raw `Data` because the validator never
decodes it (`WSC/Model/SeizeModel.lean:556-560). -/
def paramsPublishedBySeize (ctx : ScriptContext) : Option (CurrencySymbol × Data) :=
  match seizeParamsRefIdx ctx.scriptContextRedeemer with
  | none => none
  | some idx =>
      match SeizeModel.headM
              (SeizeModel.dropL idx ctx.scriptContextTxInfo.txInfoReferenceInputs) with
      | none => none
      | some i =>
          match i.txInInfoResolved.txOutDatum with
          | .OutputDatum d => SeizeModel.paramsDirCSAndProgCred d
          | _ => none

/-- Just position 1 — the mini-ledger base credential, as raw `Data`. Same type
as `SeizeModel.progLogicCredDataOf` so the two read side by side; the only
difference is the omitted `phasCSH` gate. P2 never needs position 0 (`dirCS`);
that is a transfer-side quantity. -/
def progLogicCredPublishedBySeize (ctx : ScriptContext) : Option Data :=
  (paramsPublishedBySeize ctx).map Prod.snd

/-! ## §2 — THE STATEMENTS, both conjuncts

Diff against `WSC.P2a_R_structure` and `WSC.P2b_R_containment`
(`WSC/Props/Shaped/P2ShapedR.lean`). Every `seizeRCtx <~50 leaves>` becomes the
single universally quantified `ctx`; the `isSuccessful (appliedSeizeRShaped3800.prop
ppCS <leaves>)` hypothesis becomes `accept ppCS ctx`; the three §1/§SeizeModel
hypotheses replace what the shape supplied by construction; the
`validRewardingContext` hypothesis and both postconditions are unchanged. -/

/-- **P2 (a) — STRUCTURE PRESERVATION, UNSHAPED, parametric in `accept`.** -/
def P2aUnshapedForm (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol) (paired : List TxOut),
    validRewardingContext ctx →
    SeizeModel.seizedPolicyOf ctx = some seizedCS →
    progLogicCredPublishedBySeize ctx = some (IsData.toData base) →
    SeizeModel.pairedOutputsOf ctx = some paired →
    accept ppCS ctx →
      WSC.seizeStructurePreservedAdaTopUp base seizedCS
        ctx.scriptContextTxInfo.txInfoInputs paired = true

/-- **P2 (b) — CONTAINMENT OF THE SEIZED DELTA, UNSHAPED, parametric in `accept`.**
The mint is SIGNED (`WSC.mintOf = valueOf`): a legitimate burn of the seized
policy lowers the requirement, and the `max(mint,0)` form is refuted at the
transfer side by `WSC.P1RShapedWitness.mintPos_form_REFUTED`. -/
def P2bUnshapedForm (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx →
    SeizeModel.seizedPolicyOf ctx = some seizedCS →
    progLogicCredPublishedBySeize ctx = some (IsData.toData base) →
    accept ppCS ctx →
      WSC.P2.sumOutAtBase base seizedCS tn
          ctx.scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase base seizedCS tn
            ctx.scriptContextTxInfo.txInfoInputs
          + WSC.mintOf seizedCS tn ctx.scriptContextTxInfo.txInfoMint

/-! ## §3 — the three hypotheses hold of SHAPE S1R / S1R2, for all leaves

These are the same three facts `WSC/Props/Shaped/P2ShapedR.lean`'s "§Projection
audit" establishes (`shapeR_seizedPolicy`, `shapeR_pairedOutputs`,
`shapeR_progLogicCred`), re-proved here over the public `seizeRCtx` rather than
over that section's `private abbrev rCtx`, and with the base-credential one in its
gate-free form so that no `pCS = ppCS` side condition is needed. All by `rfl`. -/

/-- The seized policy at SHAPE S1R is `key` — position 0 of the datum of the
reference input the redeemer's `directoryNodeIdx = 1` selects. -/
theorem seizedPolicyOf_S1R
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
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    SeizeModel.seizedPolicyOf
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some key := rfl

/-- The paired-output cursor at SHAPE S1R is the WHOLE output list
(`outputsStartIdx = 0`). -/
theorem pairedOutputsOf_S1R
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
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    SeizeModel.pairedOutputsOf
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs := rfl

/-- The base credential SHAPE S1R publishes is `ScriptCredential plc` — position 1
of the params datum at `paramsRefIdx = 0`. -/
theorem progLogicCredPublishedBySeize_S1R
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
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    progLogicCredPublishedBySeize
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some (IsData.toData (Credential.ScriptCredential plc)) := rfl

/-- SHAPE S1R2 (two token names per value, two in the mint) publishes the same
three quantities; only the VALUES changed, not the skeleton positions. -/
theorem seizedPolicyOf_S1R2
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    SeizeModel.seizedPolicyOf
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some key := rfl

theorem progLogicCredPublishedBySeize_S1R2
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    progLogicCredPublishedBySeize
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      = some (IsData.toData (Credential.ScriptCredential plc)) := rfl

/-! ## §4 — SPECIALISATION: the unshaped statements give the shaped ones

Each theorem is the corresponding shaped obligation of
`WSC/Props/Shaped/P2ShapedR.lean` / `P2ShapedR2.lean` with its
`isSuccessful (appliedSeizeR*Shaped3800.prop …)` hypothesis replaced by
`accept ppCS (seizeR*Ctx …)`, derived from the §2 form by instantiation alone. -/

/-- **`P2aUnshapedForm accept` ⟹ `P2a_R_structure` at the same `accept`.**
Diff the conclusion against `WSC.P2a_R_structure`: binder list,
`validRewardingContext` hypothesis and `seizeStructurePreservedAdaTopUp`
postcondition are character for character the same. -/
theorem P2a_unshaped_specialises_S1R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P2aUnshapedForm accept) :
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
    (spRed mtRed ilRed : ByteString)
    (fee : Integer),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    accept ppCS
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.seizeStructurePreservedAdaTopUp (Credential.ScriptCredential plc) key
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
        (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs = true := by
  intro ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk
    o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty
    dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
    spRed mtRed ilRed fee hv hacc
  exact H ppCS (.ScriptCredential plc) _ key _ hv
    (seizedPolicyOf_S1R mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn
      i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn
      pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0
      w1 a0 a1 spRed mtRed ilRed fee)
    (progLogicCredPublishedBySeize_S1R mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet
      i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn
      mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next
      tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
    (pairedOutputsOf_S1R mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn
      i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn
      pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0
      w1 a0 a1 spRed mtRed ilRed fee) hacc

/-- **`P2bUnshapedForm accept` ⟹ `P2b_R_containment` at the same `accept`** —
the conjunct the source-model route could not close. -/
theorem P2b_unshaped_specialises_S1R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P2bUnshapedForm accept) :
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
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    accept ppCS
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk
    o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty
    dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
    spRed mtRed ilRed fee tn hv hacc
  exact H ppCS (.ScriptCredential plc) _ key tn hv
    (seizedPolicyOf_S1R mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn
      i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn
      pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0
      w1 a0 a1 spRed mtRed ilRed fee)
    (progLogicCredPublishedBySeize_S1R mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet
      i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn
      mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next
      tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) hacc

/-- **`P2bUnshapedForm accept` ⟹ `P2b_R2_containment` at the same `accept`** —
the MULTI-TOKEN-NAME generalisation. The same unshaped form covers both shapes,
which is the point: the "one token name per value" caveat P2ShapedR's header once
carried is not a feature of the statement at all. -/
theorem P2b_unshaped_specialises_S1R2 (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P2bUnshapedForm accept) :
  ∀ (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn mlTn2 : ByteString)
      (i0Qty i0Qty2 : Integer) (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty o0Qty2 : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn o1Tn2 : ByteString)
      (o1Qty o1Qty2 : Integer)
    (mCS mTn mTn2 : ByteString) (mQ mQ2 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    (tn : TokenName),
    validRewardingContext
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
    accept ppCS
      (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) →
      WSC.P2.sumOutAtBase (Credential.ScriptCredential plc) key tn
          (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoOutputs
        ≥ WSC.P2.sumInAtBase (Credential.ScriptCredential plc) key tn
            (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoInputs
          + WSC.mintOf key tn
              (seizeR2Ctx mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut
        escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn wallet i1Ada i1CS i1Tn
    i1Qty oStk o0Ada o0Qty o0Qty2 dOut escH o1Ada o1CS o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn
    mTn2 mQ mQ2 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key
    next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee tn hv hacc
  exact H ppCS (.ScriptCredential plc) _ key tn hv
    (seizedPolicyOf_S1R2 mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2 dIn wallet i1Ada
      i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut escH o1Ada o1CS o1Tn o1Tn2 o1Qty
      o1Qty2 mCS mTn mTn2 mQ mQ2 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS
      nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
    (progLogicCredPublishedBySeize_S1R2 mlH inStk i0Ada mlCS mlTn mlTn2 i0Qty i0Qty2
      dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty o0Qty2 dOut escH o1Ada o1CS
      o1Tn o1Tn2 o1Qty o1Qty2 mCS mTn mTn2 mQ mQ2 pHash pCS pTn pAda pQty dirCS plc
      glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed
      ilRed fee) hacc

/-! ## §5 — NON-VACUITY, and why the benchmark budget is 3800

Below the minimal accepting step count the `accept` hypothesis is unsatisfiable
and both forms are VACUOUS. The theorem below is measured on the UNSHAPED term —
`cekExecuteProgram programmableSeize.script (WSC.seizeInputs ppCS ctx) K`, exactly
the program-and-inputs pair `WSC/Benchmark/P2Unshaped.lean` preps, with only the
meter changed. It is the same term the library's own two-sided K pins use
(`WSC.P2RWitness.K_is_2301_and_2412`, `WSC.P2R2Witness.K_R2_is_2739`), so those
pins transfer to the benchmark verbatim. -/

/-- **THE P2 BENCHMARK IS NON-VACUOUS AT 3800 AND VACUOUS AT 600.**

Conjuncts 1-3: `WSC.P2RWitness.ctxAccept` satisfies every §2 hypothesis other than
`accept` — ledger validity (`all_four_valid.1`), the seized policy is `"MMM"`, and
the base credential is `ScriptCredential "PROGLOGIC"`.

Conjunct 4: the real compiled bytecode HALTS SUCCESSFULLY at 3800.
Conjunct 5: it does NOT halt at 2300 — one step below the pinned K = 2301.
Conjunct 6: it does NOT halt at 600, which is the budget of the ONLY unshaped
seize prep that exists (`WSC.appliedSeize`, `WSC/Prep/Seize.lean`, ≈1.3 s). That
prep is therefore unusable for P2, which is the whole reason this benchmark asks
for 3800.

MARGIN: 3800 − 2739 = 1061 steps over the most expensive measured witness
(S1R2's residual instance), 3800 − 2412 = 1388 over S1R's.

HONEST LIMIT: this is an `∃`. It proves 3800 is NON-EMPTY; it does not characterise
WHICH seizures 3800 covers (audit F2, still open). For calibration: post-#112 the
two accepting seize GOLDENS cost 2,305 and 2,905 steps
(`WSC/goldens/K-MEASUREMENTS.md` §2), so both are inside 3800 — but that is a
statement about two transactions, not about the class. -/
theorem P2_unshaped_nonvacuous_at_3800_and_vacuous_at_600 :
    validRewardingContext P2RWitness.ctxAccept = true
    ∧ SeizeModel.seizedPolicyOf P2RWitness.ctxAccept = some (ByteString.mk "MMM")
    ∧ progLogicCredPublishedBySeize P2RWitness.ctxAccept
        = some (IsData.toData (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")))
    ∧ P2RWitness.isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
        programmableSeize.script
        (WSC.seizeInputs P2RWitness.ppCS P2RWitness.ctxAccept) 3800) = true
    ∧ P2RWitness.isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
        programmableSeize.script
        (WSC.seizeInputs P2RWitness.ppCS P2RWitness.ctxAccept) 2300) = false
    ∧ P2RWitness.isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
        programmableSeize.script
        (WSC.seizeInputs P2RWitness.ppCS P2RWitness.ctxAccept) 600) = false := by
  native_decide

/-- The accept side of the P2 benchmark statement is SATISFIABLE on the `.exec`
term at budget 3800. -/
theorem P2_unshaped_accept_is_satisfiable :
    ∃ (ppCS : CurrencySymbol) (ctx : ScriptContext),
      validRewardingContext ctx = true
      ∧ isSuccessful (PlutusCore.UPLC.CekMachine.cekExecuteProgram
          programmableSeize.script (WSC.seizeInputs ppCS ctx) 3800) :=
  ⟨P2RWitness.ppCS, P2RWitness.ctxAccept,
   P2RWitness.all_four_valid.1,
   P2RWitness.isHaltB_sound _
     P2_unshaped_nonvacuous_at_3800_and_vacuous_at_600.2.2.2.1⟩

/-! ## §6 — AXIOM AUDIT

Expected: §3's five `rfl`s carry NO axioms; §4's three carry only the Lean
standard set; §5's two carry the two `native_decide` compiler-trust axioms. NO
`sorryAx` anywhere — there is no `blaster` call in this module. -/

#print axioms WSC.Benchmark.seizedPolicyOf_S1R
#print axioms WSC.Benchmark.pairedOutputsOf_S1R
#print axioms WSC.Benchmark.progLogicCredPublishedBySeize_S1R
#print axioms WSC.Benchmark.seizedPolicyOf_S1R2
#print axioms WSC.Benchmark.progLogicCredPublishedBySeize_S1R2
#print axioms WSC.Benchmark.P2a_unshaped_specialises_S1R
#print axioms WSC.Benchmark.P2b_unshaped_specialises_S1R
#print axioms WSC.Benchmark.P2b_unshaped_specialises_S1R2
#print axioms WSC.Benchmark.P2_unshaped_nonvacuous_at_3800_and_vacuous_at_600
#print axioms WSC.Benchmark.P2_unshaped_accept_is_satisfiable

end Benchmark
end WSC
