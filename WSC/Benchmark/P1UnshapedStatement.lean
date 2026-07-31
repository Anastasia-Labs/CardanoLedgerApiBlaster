/-
WSC/Benchmark/P1UnshapedStatement.lean — **THE REVIEWABLE HALF of the UNSHAPED
P1 benchmark. THIS MODULE BUILDS.** Its companion
`WSC/Benchmark/P1Unshaped.lean` does not, deliberately, and says so in its own
banner.

════════════════════════════════════════════════════════════════════════════
WHY THE BENCHMARK IS SPLIT IN TWO
════════════════════════════════════════════════════════════════════════════
The artifact the Blaster team is being handed is an UNSHAPED `#prep_uplc` of the
production transfer validator at an accept-capable budget, plus the P1 obligation
stated over it. That prep does not complete (WSC/BENCHMARK-PREP.md has the
numbers), so the module that carries it cannot be checked by anything.

That would leave the STATEMENT unchecked too — and the statement is the whole
deliverable: a malformed benchmark wastes the optimiser team's time and
misrepresents what we claim. So everything about the statement that does NOT
need the intractable prep lives HERE, in a module that compiles:

* §1 the ONE hypothesis the shaped statements get for free from their shape, and
  the ledger-only projection that expresses it;
* §2 `P1UnshapedForm`, the statement, PARAMETRIC in the accept predicate;
* §3 four SPECIALISATION theorems — `P1UnshapedForm accept` implies, verbatim,
  the body of `P1R_T1_stmt` / `P1R_T2_stmt` / `P1R_T6_stmt` / `P1R_T7_stmt`
  with the same `accept`. Kernel proofs, no solver, no `sorry`. This is the
  evidence that the unshaped statement WOULD give the property;
* §4 the executable NON-VACUITY certificate: a concrete `ScriptContext` that
  satisfies every hypothesis of §2 and on which the real compiled bytecode
  HALTS SUCCESSFULLY inside the benchmark's 4400-step budget — and does NOT
  halt inside 1600, which is why the two unshaped preps that already exist
  (600 and 1600) cannot carry this statement.

`WSC/Benchmark/P1Unshaped.lean` then contains exactly two things this module
cannot: the `#prep_uplc … 4400` and `P1UnshapedForm` instantiated at that prep's
`.prop`, with a `by blaster` attempt.

════════════════════════════════════════════════════════════════════════════
THE ONE DIFFERENCE FROM THE SHAPED STATEMENTS — READ THIS BEFORE DIFFING
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P1ShapedR.lean`'s `P1R_T1_stmt` quantifies ~40 SCALAR LEAVES
and applies `p1RShapedCtx` to them. Four of those leaves are not ordinary
scalars — they are the objects the POSTCONDITION talks about:

  * `cs`, `tn` — the asset. These stay universally quantified here. Nothing to do.
  * `plc`      — the mini-ledger BASE payment credential, i.e. the credential
                 `Model.outSum` / `Model.inSum` sum over. (§2 generalises it to a
                 `base : Credential`, exactly as `WSC.Model.P1_model` does; the
                 shapes instantiate it to `.ScriptCredential plc`.)
  * `dirCS`    — the DIRECTORY policy id the "no covering node" (⇒ registered)
                 hypothesis is relative to.

In the shaped statements `plc` and `dirCS` are tied to the transaction BY
CONSTRUCTION OF THE SHAPE: `p1ShapedParamsIn` (WSC/Shaped/GlobalShapedP1.lean:221)
puts a protocol-params reference input into the context whose inline datum
publishes `directoryNodeCS = dirCS` and `progLogicCred = ScriptCredential plc`,
and the shaped redeemer's `plgrParamsRefIdx` is the literal `0`, which is that
input's index.

**Quantifying `plc` and `dirCS` FREELY over an arbitrary `ctx` does NOT give P1 —
it gives a statement that is FALSE, and refutably so.** Take any accepted
transfer that mints a positive quantity of `(cs, tn)` at a pubkey address, then
instantiate `plc` to a credential the transaction never mentions and `dirCS` to a
policy no reference input carries. `Model.coveringNodeExists dirCS cs … = false`
holds vacuously, `outSum = inSum = 0`, and the conclusion reads `0 ≥ 0 + q` with
`q > 0`. So the "shape is the only difference" instruction cannot be followed
literally: the unshaped statement needs ONE extra hypothesis, and it is exactly
the by-construction fact the shape supplied.

That hypothesis is §1's

    paramsPublishedBy ctx = some (dirCS, IsData.toData (Credential.ScriptCredential plc))

and §3 proves it holds of `p1RShapedCtx <leaves>` for all leaves, by computation,
so the specialisation is real and the delta is genuinely just this one clause.
Everything else — the `validRewardingContext` ledger-validity hypothesis, the
`Model.coveringNodeExists … = false` registration hypothesis, and the
`Model.outSum ≥ Model.inSum + Model.mintSigned` ground-truth conclusion — is
IDENTICAL in form to `P1R_T1_stmt`, clause for clause.

════════════════════════════════════════════════════════════════════════════
THE STATEMENT IS NOT NEW — IT IS THE PUBLISHED MODEL-LEVEL P1, RE-POINTED
════════════════════════════════════════════════════════════════════════════
This library ALREADY publishes an unshaped, fully-symbolic P1 statement:
`WSC.Model.P1_model` (`WSC/Props/P1_Transfer.lean:362`). Compare it clause for
clause with §2's `P1UnshapedForm`:

| `P1_model ppCS ctx base dirCS cs tn` | `P1UnshapedForm accept` |
|---|---|
| `globalModel ppCS ctx = true` (the hand TRANSCRIPTION) | `accept ppCS ctx` (the real BYTECODE's prepped residual) |
| `cs ≠ ByteString.mk ""` | identical — **see the CORRECTED DEFECT note below** |
| `paramsPinned ppCS dirCS base (…refs) = true` | `paramsPublishedBy ctx = some (dirCS, toData base)` |
| `coveringNodeExists dirCS cs (…refs) = false` | identical |
| `∀ o ∈ outs, validTxOutValue o.txOutValue = true` | subsumed by `validRewardingContext ctx` — and that is now PROVED, not asserted: §2.1's `outputs_ledger_valid_of_validRewardingContext` |
| `outSum base cs tn … ≥ inSum base cs tn … + mintSigned cs tn …` | identical |

So the unshaped statement was not invented here. What is new is only that the
accept hypothesis names the COMPILED PROGRAM instead of the transcription — which
matters, because the transcription's fidelity axiom is FALSE at wsc-poc
`2306678` and was retracted (`WSC/Model/GlobalModelRefuted.lean`), so `P1_model`
implies nothing about production. `base` is a general `Credential` here for the
same reason it is in `P1_model`: nothing about P1 needs it to be a script
credential.

════════════════════════════════════════════════════════════════════════════
⚠️ CORRECTED DEFECT — THE `cs ≠ ada` GUARD WAS MISSING, AND THE STATEMENT WAS
FALSE WITHOUT IT (found and repaired 2026-07-31)
════════════════════════════════════════════════════════════════════════════
**AS FIRST PUBLISHED, `P1UnshapedForm` DROPPED `P1_model`'s `cs ≠ ByteString.mk ""`
clause** while the table above claimed the two agreed clause for clause. Dropping
a hypothesis makes a ∀-statement STRICTLY STRONGER, and this one was strong enough
to be FALSE. Do not read the history away: this is a corrected defect and the
record is the useful part of it.

**THE REFUTATION, at `cs = tn = adaSymbol = ByteString.mk ""`.** The witness is
this library's OWN non-vacuity certificate, `WSC.P1RShapedWitness.ctxOk`
(`WSC/Props/Shaped/P1ShapedR.lean:582-596`) — the same context §4 below uses. It
satisfies every hypothesis the broken form had:

* `validRewardingContext ctxOk = true` — `WSC.P1RShapedWitness.ctxOk_valid`;
* the §1 params hypothesis — §4's conjunct 2, by `native_decide`;
* the registration hypothesis is **FREE at ada, for every reference-input list**:
  `Model.coveringNodeExists` (`WSC/Props/P1_Transfer.lean:222-234`) needs
  `decide (k < cs)`, and nothing is `< ""`, so the covering test is `false` at
  every node. The escape route the hypothesis is supposed to shut is not even
  reachable at the ada slot;
* the bytecode ACCEPTS — §4's conjunct 4, `native_decide` at 4400 steps.

And the conclusion FAILS on it: `outSum = 150`, `inSum = 200`, `mintSigned = 0`,
so `150 ≥ 200 + 0` is false. **The 50-lovelace gap is `txInfoFee := 50`.** The
transfer validator deliberately never constrains ada — a transaction must be able
to pay its fee out of a mini-ledger UTxO — so no budget, no shape and no better
prep could ever make the unguarded statement true. It is a statement defect, not a
proof gap.

REFUTATION ARTIFACT: `WSC/Benchmark/AdaRefutation.lean` (standalone, re-derives
`outSum`/`inSum`/`mintSigned`/`coveringNodeExists`/`adaPlusOne` from their cited
definition sites and carries `ctxOk_refutes_P1_at_ada`, `covering_false_at_ada`,
`shaped_value_invalid_at_ada`, `shaped_value_valid_off_ada`).

**WHY THE SHAPED THEOREMS `P1R_T1`/`T2`/`T6`/`T7` ARE UNAFFECTED — and why §3 now
needs a case split.** `Shape.adaPlusOne` (`WSC/Shaped/Shape.lean:60-63`) puts `cs`
SECOND, after the ada slot, and `validTxOutValue`
(`CardanoLedgerApi/V1/Contexts.lean:787-802`) demands strictly ascending currency
symbols (`prev_cs < cs`). At `cs = adaSymbol` the shaped output value is therefore
NOT ledger-valid, `validRewardingContext` is false, and every shaped statement is
VACUOUSLY TRUE there. **That vacuity is exactly the protection the unshaped
statement lost when it dropped the guard**, and it is what §3.1 below now proves
outright so that each specialisation can discharge the restored hypothesis
(§2.1: `validTxOutValue_adaPlusOne_at_ada`,
`outputs_ledger_valid_of_validRewardingContext`).

**WHY THE ROW ABOVE ONCE READ "not needed".** The reasoning recorded there was
that the shaped bytecode theorems come back `✅ Valid` without the guard. That is
true and it is beside the point: they are `✅ Valid` because they are vacuous at
ada, which is a fact about the SHAPE's value skeleton, not about the property.
Generalising a shaped theorem to an arbitrary `ctx` throws that skeleton away, so
any hypothesis the skeleton was silently supplying has to be restored explicitly.
The same trap is what §1 already documented for `plc`/`dirCS`; the ada slot is the
third instance of it and was missed.

**WHY `ByteString.mk ""` AND NOT `adaSymbol`.** `P1_model`
(`WSC/Props/P1_Transfer.lean:366`) spells it `cs ≠ ByteString.mk ""` and neither
that module nor this one opens `CardanoLedgerApi.V1.Value.adaSymbol`. The point of
the guard is that the two statements agree character for character, so the
spelling is copied rather than improved. (`adaSymbol` is *defined* as
`ByteString.mk ""`, `CardanoLedgerApi/V1/Value.lean`; `WSC/Composition.lean:207-220`
records the same side condition under that name and explains why the head
sentinel makes it MANDATORY there too.)

**WHY `paramsPublishedBy` AND NOT `paramsPinned`, since the latter is the
published one.** `paramsPinned ppCS dirCS base refs` is a ∀-SCAN: *every*
reference input that `hasCSH ppCS` accepts must publish exactly `(dirCS, base)`.
`paramsPublishedBy` instead reads the ONE input the redeemer's `plgrParamsRefIdx`
names, which is what the validator does (`pparamsAtRefIdx`, :824-838). Two
consequences, both in the statement's favour:

* The two hypotheses are INCOMPARABLE in general: `paramsPinned` is vacuously
  true when no reference input carries `ppCS`, while `paramsPublishedBy` can
  hold in a context where a differently-indexed `ppCS`-authenticated input
  publishes a different pair. What makes the choice safe is that UNDER `accept`
  they coincide — the validator authenticates exactly the input at the
  redeemer's index (`pparamsAtRefIdx`), so both pin `(dirCS, base)` to the same
  datum at the point of use. The index-based read is preferred because it
  mirrors what the bytecode actually does, not because it is weaker.
* At every P1 shape, `paramsPinned` would need the side condition `nCS ≠ ppCS` —
  the DIRECTORY NODE must not also carry the params NFT, or the scan reaches the
  node's 5-field `DirectorySetNode` datum and fails. `nCS` and `ppCS` are distinct
  free leaves of the shape, so that is a real extra hypothesis. §3's
  specialisations need no side condition at all.

Both readings are sound as hypotheses because ACCEPT does the authenticating: if
no reference input at the redeemer's index carries the params NFT, `phasCSH`
fails, the validator `perror`s, and the obligation is discharged by the accept
hypothesis rather than by an assumption.

════════════════════════════════════════════════════════════════════════════
THE MINT IS SIGNED — DO NOT "FIX" IT TO `mintPos`
════════════════════════════════════════════════════════════════════════════
The conclusion uses `Model.mintSigned` (`WSC/Props/P1_Transfer.lean:203`,
definitionally `valueOf cs tn mint`, i.e. the ledger's ONE signed integer per
asset = minted − burned). The `max(mint, 0)` variant ARCHITECTURE.md §3-P1 once
carried is MACHINE-REFUTED on a burn: `WSC.P1RShapedWitness.mintPos_form_REFUTED`
(WSC/Props/Shaped/P1ShapedR.lean) exhibits a ledger-legal, redeemer-covered,
bytecode-ACCEPTED burn on which the signed requirement holds (`1 ≥ 5 − 4`) and
the `mintPos` requirement fails (`1 ≥ 5 + 0`).

Because the unshaped statement quantifies over ONE `ctx` rather than over a
shape, it does not need a separate "mint case": §3's specialisations to T2R
(mint/burn, single output) and T7R (mint/burn, two outputs) come out of the SAME
`P1UnshapedForm`. That is itself evidence the form is right — the shaped family
needs four theorems where the unshaped statement needs one.

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE DOES NOT ESTABLISH
════════════════════════════════════════════════════════════════════════════
1. It does NOT prove P1 unshaped. Nothing here mentions a prep. The obligation
   is in the companion module and is OPEN.
2. §3 abstracts the accept predicate, so it does NOT derive `P1R_T1` (the shaped
   THEOREM) from a hypothetical unshaped theorem. Those two accept predicates are
   `isSuccessful (appliedGlobalUCeiling.prop ppCS ctx)` and
   `isSuccessful (appliedGlobalShapedT1R.prop ppCS <leaves>)`: the same program at
   the same budget on the same context, but two DIFFERENT `Optimize.main` outputs,
   and this library has measured that `#prep_uplc` residuals are not
   definitionally interchangeable (`WSC/Shaped/Probe/BridgeProbe2FAILS.lean`, the
   `prop`-vs-`exec` finding, audit F8 / docs/LIMITATIONS.md §5). §3 is therefore
   the strongest statement-level certificate available without a new bridge, and
   the residual gap is a pre-existing, published one, not a new assumption.
3. §4 is an `∃`-witness, not a coverage claim. It shows the benchmark's accept
   class is non-empty at 4400; it says nothing about which transactions 4400
   covers (audit F2 is still open).
-/
import WSC.Props.Shaped.P1ShapedR
import WSC.Model.SeizeModel

set_option maxHeartbeats 0
-- The §4 witness is a large concrete `Data` skeleton, as in every witness module.
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

/-! ## §1 — the one hypothesis the shape supplied by construction

GROUND TRUTH ONLY (ARCHITECTURE.md D3 / Tier 0.1): both definitions below are
functions of `ScriptContext` fields — the redeemer `Data`, the reference-input
list and one inline datum. No validator-computed accumulator appears.

The three helpers reused by name — `WSC.SeizeModel.dropL`, `…headM`,
`…paramsDirCSAndProgCred` — are the AUDITED mirrors of `pdropList`, `phead` and
the `pparamsAtRefIdx` positional datum read, each carrying its
`ProgrammableLogicBase.hs` / `ProtocolParams.hs` citation at its definition site
(WSC/Model/SeizeModel.lean:105, :109, :561). They are ledger-only projections;
NOTHING here touches `SeizeModel.seizeModel`, the transcription whose
fidelity axiom was retracted at task R1. `pparamsAtRefIdx`
(ProgrammableLogicBase.hs:824-838) is ONE helper called from BOTH the transfer
and the seize path, which is why reusing them is exact rather than analogical. -/

/-- `plgrParamsRefIdx` — the FIFTH field of `PTransferAct`
(ProgrammableLogicBase.hs:1054; five fields post-#112, see WSC/Redeemer.lean).
The arm is reached positionally: constructor index 0 is `PTransferAct` and any
other index is `PSeizeAct`, which post-#112 is a hard error in this validator
(:1290-1291) — so `none` there is not a loss, it only makes the hypothesis
unsatisfiable on contexts the bytecode rejects anyway. Extra fields are ignored,
exactly as a raw `phead`/`ptail` chain does. -/
def transferParamsRefIdx : Data → Option Integer
  | Data.Constr 0 (_ :: _ :: _ :: _ :: Data.I p :: _) => some p
  | _ => none

/-- **The protocol-params datum this transaction publishes**, read the way the
validator reads it: reference input at the redeemer's `plgrParamsRefIdx` (raw
`pdropList`, so a negative index is CLAMPED, not rejected), inline datum, then
positions 0 (`directoryNodeCS`, a `Data.B`) and 1 (`progLogicCred`, kept as raw
`Data` because the validator never decodes it — WSC/Model/SeizeModel.lean:556-560).

**DELIBERATELY OMITS the `phasCSH ppCS` authentication gate** that
`SeizeModel.paramsAtRefIdx` carries (:832). Two reasons, and both make the
statement stronger rather than weaker:

* the hypothesis is then WEAKER, so `P1UnshapedForm` quantifies over MORE
  contexts — including every context whose params UTxO is unauthenticated. Those
  are contexts the bytecode ERRORS on, so `accept` is false there and the
  obligation is discharged by the accept hypothesis, not by an assumption;
* the specialisation theorems of §3 then need NO side condition. With the gate
  in, each would have to assume `pCS = ppCS` (compare
  `WSC.shapeR_progLogicCred`, which does), and that equation is only available
  from the accept path — see `WSC.P2_R_gates_are_earned`. Leaving the gate to the
  bytecode is what keeps the specialisation a pure instantiation. -/
def paramsPublishedBy (ctx : ScriptContext) : Option (CurrencySymbol × Data) :=
  match transferParamsRefIdx ctx.scriptContextRedeemer with
  | none => none
  | some idx =>
      match SeizeModel.headM
              (SeizeModel.dropL idx ctx.scriptContextTxInfo.txInfoReferenceInputs) with
      | none => none
      | some i =>
          match i.txInInfoResolved.txOutDatum with
          | .OutputDatum d => SeizeModel.paramsDirCSAndProgCred d
          | _ => none

/-! ## §2 — THE STATEMENT

Diff this against `WSC/Props/Shaped/P1ShapedR.lean`'s `P1R_T1_stmt`. Every
`p1RShapedCtx <~40 leaves>` becomes the single universally quantified `ctx`; the
`isSuccessful (appliedGlobalShapedT1R.prop ppCS <leaves>)` hypothesis becomes
`accept ppCS ctx`; TWO hypotheses appear that no shaped statement writes down,
and the module header explains why NEITHER is optional:

* §1's `paramsPublishedBy` clause, which the shape supplied by construction;
* `cs ≠ ByteString.mk ""`, which the shape's VALUE SKELETON supplied by making
  itself ledger-invalid at the ada slot (see the CORRECTED DEFECT note).

Both are clauses of `WSC.Model.P1_model`, so against the PUBLISHED model-level
statement the form below adds nothing at all; everything else is unchanged,
clause for clause. -/

/-- **P1 — TRANSFER CONTAINMENT, UNSHAPED, over a FULLY SYMBOLIC `ScriptContext`,
parametric in the accept predicate.**

*For every ledger-valid transaction, every NON-ADA asset `(cs, tn)` whose policy
is REGISTERED (no authenticated directory node in the reference inputs covers
`cs`, so the walk's only exemption route is shut), and the mini-ledger base
credential `base` this transaction's own protocol-params datum publishes: if the
real compiled `programmableLogicGlobal` bytecode accepts, then the amount of
`(cs, tn)` at outputs on `base` is at least the amount at inputs spent from
`base` plus the SIGNED net mint of `(cs, tn)`.*

`accept` is abstract so that §3 can be proved in the kernel. The benchmark
instantiates it to `fun ppCS ctx => isSuccessful (appliedGlobalUCeiling.prop ppCS ctx)`
in `WSC/Benchmark/P1Unshaped.lean`.

**THE `cs ≠ ByteString.mk ""` HYPOTHESIS IS LOAD-BEARING AND WAS ONCE MISSING.**
It is `WSC.Model.P1_model`'s own guard (`WSC/Props/P1_Transfer.lean:366`), copied
character for character. Without it the statement is FALSE — refuted by this
library's own accepting witness, on which the ada gap is exactly `txInfoFee`. The
full record, the refutation and why the SHAPED theorems are unaffected are in the
module header's CORRECTED DEFECT note and in
`WSC/Benchmark/AdaRefutation.lean`. Do not remove it, and do not weaken it to a
statement about the shapes: the shapes get it for free and an arbitrary `ctx`
does not. -/
def P1UnshapedForm (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
    cs ≠ ByteString.mk "" →
    validRewardingContext ctx →
    paramsPublishedBy ctx = some (dirCS, IsData.toData base) →
    Model.coveringNodeExists dirCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
    accept ppCS ctx →
      Model.outSum base cs tn
          ctx.scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum base cs tn
            ctx.scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn
            ctx.scriptContextTxInfo.txInfoMint

/-! ## §2.1 — LEDGER-VALIDITY PROJECTIONS

Two facts about CLAB's `validRewardingContext`, both needed by §3.1 and both
worth having on their own:

* it really does subsume `P1_model`'s FIFTH clause
  `∀ o ∈ outputs, validTxOutValue o.txOutValue = true` — that is the header
  table's "subsumed by" entry, and it is PROVED below rather than asserted;
* the canonical shaped output value is NOT ledger-valid at the ada slot, with the
  three quantities left SYMBOLIC. This is
  `WSC.AdaRefutation.shaped_value_invalid_at_ada` generalised off its concrete
  numbers, and it is what makes each of §3.1's vacuity branches one line.

The chain is `validRewardingContext` (`CardanoLedgerApi/V3/Contexts.lean:1867`)
⟹ `validScriptContext` (:1849) ⟹ `validTxInfo` (:1821) ⟹ `validOutputs` (:1696)
⟹ `V2.validTxOutValue` on each output (`CardanoLedgerApi/V1/Contexts.lean:787`).
The two `Bool` projections are spelled out by `Bool.rec` rather than by `simp` so
that the arithmetic of the `&&` chain is visible and axiom-free. -/

/-- `&&`, left projection on `= true`. Axiom-free. -/
theorem andEqTrueL {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact Bool.noConfusion h

/-- `&&`, right projection on `= true`. Axiom-free. -/
theorem andEqTrueR {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- `validRewardingContext` is `validScriptContext` behind a `ScriptInfo` guard
(`CardanoLedgerApi/V3/Contexts.lean:1867-1870`). -/
theorem validScriptContext_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    CardanoLedgerApi.V3.validScriptContext ctx = true := by
  unfold CardanoLedgerApi.V3.validRewardingContext at h
  split at h
  · exact h
  · exact Bool.noConfusion h

/-- …and `validScriptContext` carries `validOutputs` as one conjunct of
`validTxInfo`. Proved by CONTRADICTION on the `Bool` rather than by counting
positions in the 14-conjunct chain, so a future CLAB conjunct cannot silently
shift the projection. -/
theorem validOutputs_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    CardanoLedgerApi.V3.validOutputs ctx.scriptContextTxInfo.txInfoOutputs = true := by
  have h := validScriptContext_of_validRewardingContext h
  cases hb : CardanoLedgerApi.V3.validOutputs ctx.scriptContextTxInfo.txInfoOutputs with
  | true => rfl
  | false =>
      exfalso
      unfold CardanoLedgerApi.V3.validScriptContext CardanoLedgerApi.V3.validTxInfo at h
      rw [hb] at h
      simp at h

/-- `validOutputs` is a `Recursor.all` over the output list
(`CardanoLedgerApi/V3/Contexts.lean:1696-1697`), so it hands out per-output
validity. -/
theorem validTxOutValue_of_mem_validOutputs :
    ∀ (outs : List TxOut) (o : TxOut),
      CardanoLedgerApi.V3.validOutputs outs = true → o ∈ outs →
        CardanoLedgerApi.V2.validTxOutValue o.txOutValue = true := by
  intro outs
  induction outs with
  | nil => intro o _ ho; cases ho
  | cons x rest ih =>
      intro o h ho
      have hx : CardanoLedgerApi.V2.validTxOutValue x.txOutValue = true := andEqTrueL h
      have hrest : CardanoLedgerApi.V3.validOutputs rest = true := andEqTrueR h
      cases ho with
      | head => exact hx
      | tail _ hmem => exact ih o hrest hmem

/-- **The header table's "subsumed by `validRewardingContext ctx`" entry, PROVED.**
`P1_model`'s fifth clause (`WSC/Props/P1_Transfer.lean:368`) is a consequence of
the benchmark's ledger-validity hypothesis, so `P1UnshapedForm` really does state
the model-level P1 and not a weakened relative of it. -/
theorem outputs_ledger_valid_of_validRewardingContext {ctx : ScriptContext}
    (h : validRewardingContext ctx = true) :
    ∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs,
      CardanoLedgerApi.V2.validTxOutValue o.txOutValue = true :=
  fun o ho =>
    validTxOutValue_of_mem_validOutputs _ o (validOutputs_of_validRewardingContext h) ho

/-- **THE SHAPED OUTPUT VALUE IS NOT LEDGER-VALID AT THE ADA SLOT**, for every
lovelace amount, token name and quantity. `Shape.adaPlusOne`
(`WSC/Shaped/Shape.lean:60-63`) is `[(B "", Map [(B "", I n)]), (B cs, Map [(B tn,
I q)])]`, and `validTxOutValue` (`CardanoLedgerApi/V1/Contexts.lean:787-802`)
requires the second policy to satisfy `prev_cs < cs` with `prev_cs = ""`. At
`cs = ByteString.mk ""` that test is `"" < ""`, which is false BY COMPUTATION, so
the whole `&&` chain collapses and only the leading `n > 0` conjunct is left over
— hence `Bool.and_false`. Axiom-free.

This is the ONLY reason the four shaped P1 theorems survive with `cs` free, and
therefore the only reason §3.1's vacuity branches close. -/
theorem validTxOutValue_adaPlusOne_at_ada (n q : Integer) (tn : TokenName) :
    CardanoLedgerApi.V2.validTxOutValue (Shape.adaPlusOne n (ByteString.mk "") tn q)
      = false :=
  Bool.and_false _

/-! ## §3 — SPECIALISATION: the unshaped statement gives the shaped ones

Each theorem below is the corresponding `P1R_*_stmt` of
`WSC/Props/Shaped/P1ShapedR.lean` with its `isSuccessful (appliedGlobalShapedT*R.prop …)`
hypothesis replaced by `accept ppCS (<shape> …)`. **The shaped statements quantify
`cs` FREELY and must keep doing so** — they are the published theorems and their
binder lists are part of the deliverable — so each specialisation now has to
discharge `P1UnshapedForm`'s `cs ≠ ByteString.mk ""` itself. Each therefore SPLITS
on the ada slot:

* `cs ≠ ada` — instantiate the unshaped form, exactly as before (§3.0 supplies
  the params hypothesis);
* `cs = ada` — the SHAPED statement is vacuous: its own `validRewardingContext`
  hypothesis is unsatisfiable, because the shape's first output carries
  `Shape.adaPlusOne outAda cs tn qOut` and that value is not ledger-valid when
  `cs` is the ada symbol (§2.1, §3.1). The branch is CLOSED, not assumed.

Nothing about the shaped conclusions changes, so the specialisation is still the
full four-way containment claim; what changed is that the ada slot is now
discharged in the open instead of being smuggled in by the shape.

Consequence a reviewer can check by inspection: the unshaped statement is not
merely *similar* to the shaped ones, it CONTAINS all four of them — including
both mint shapes, so the signed-mint half is exercised. -/

/-! ### §3.0 — the added hypothesis holds of every P1 shape, for all leaves -/

/-- SHAPE T1R publishes `(dirCS, ScriptCredential plc)`: its redeemer's
`plgrParamsRefIdx` is the literal `0` (`p1ShapedRedeemer_eq`) and reference input
0 is `p1ShapedParamsIn`, whose inline datum is
`GlobalParams.mk dirCS (.ScriptCredential plc) …` encoded as a 4-element
`Data.List` (WSC/Redeemer.lean, `ProtocolParams.hs:84-96`). -/
theorem paramsPublishedBy_T1R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    paramsPublishedBy
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)
      = some (dirCS, IsData.toData (Credential.ScriptCredential plc)) := rfl

/-- SHAPE T2R — same params input, same literal index; the redeemer differs only
in `plgrMintProofs` (`p1ShapedRedeemerMint_eq`), which is field 4, not field 5. -/
theorem paramsPublishedBy_T2R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    paramsPublishedBy
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee)
      = some (dirCS, IsData.toData (Credential.ScriptCredential plc)) := rfl

/-- SHAPE T6R (two mini-ledger outputs). -/
theorem paramsPublishedBy_T6R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    paramsPublishedBy
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)
      = some (dirCS, IsData.toData (Credential.ScriptCredential plc)) := rfl

/-- SHAPE T7R (two mini-ledger outputs AND a nonzero mint of free sign). -/
theorem paramsPublishedBy_T7R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    paramsPublishedBy
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee)
      = some (dirCS, IsData.toData (Credential.ScriptCredential plc)) := rfl

/-! ### §3.1 — THE ADA BRANCH IS CLOSED: every P1 shape is LEDGER-INVALID at
`cs = adaSymbol`, for all leaves

This is the half of the repair that is not bookkeeping. `Shape.adaPlusOne` puts
`cs` in the SECOND value slot, after ada, and `validTxOutValue` demands strictly
ascending currency symbols — so a shaped context whose asset IS ada cannot satisfy
`validRewardingContext` at all, whatever the ~40 remaining leaves are. Each of the
four theorems below turns that into `False`, which is what lets §3.2-§3.4 close
the `cs = ada` case outright instead of assuming it away.

Only the shape's FIRST output is used, and in all four shapes that is the
mini-ledger output `p1ShapedBaseOut` (`WSC/Shaped/GlobalShapedR.lean:301`, `:369`,
`:436`, `:503`) — the escape output would do just as well; the first one keeps the
`&&` projection a single `andEqTrueL`. -/

/-- SHAPE T1R is ledger-invalid at the ada slot. -/
theorem shaped_invalid_at_ada_T1R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer)
    (hada : cs = ByteString.mk "")
    (hv : validRewardingContext
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) = true) : False := by
  subst hada
  have h : CardanoLedgerApi.V2.validTxOutValue
      (Shape.adaPlusOne outAda (ByteString.mk "") tn qOut) = true :=
    andEqTrueL (validOutputs_of_validRewardingContext hv)
  rw [validTxOutValue_adaPlusOne_at_ada] at h
  exact Bool.noConfusion h

/-- SHAPE T2R (mint/burn) is ledger-invalid at the ada slot. -/
theorem shaped_invalid_at_ada_T2R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer)
    (hada : cs = ByteString.mk "")
    (hv : validRewardingContext
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) = true) : False := by
  subst hada
  have h : CardanoLedgerApi.V2.validTxOutValue
      (Shape.adaPlusOne outAda (ByteString.mk "") tn qOut) = true :=
    andEqTrueL (validOutputs_of_validRewardingContext hv)
  rw [validTxOutValue_adaPlusOne_at_ada] at h
  exact Bool.noConfusion h

/-- SHAPE T6R (two mini-ledger outputs) is ledger-invalid at the ada slot; the
FIRST of the two is enough. -/
theorem shaped_invalid_at_ada_T6R
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer)
    (hada : cs = ByteString.mk "")
    (hv : validRewardingContext
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) = true) : False := by
  subst hada
  have h : CardanoLedgerApi.V2.validTxOutValue
      (Shape.adaPlusOne outAda0 (ByteString.mk "") tn qOut0) = true :=
    andEqTrueL (validOutputs_of_validRewardingContext hv)
  rw [validTxOutValue_adaPlusOne_at_ada] at h
  exact Bool.noConfusion h

/-- SHAPE T7R (two mini-ledger outputs AND a mint) is ledger-invalid at the ada
slot. -/
theorem shaped_invalid_at_ada_T7R
    (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer)
    (hada : cs = ByteString.mk "")
    (hv : validRewardingContext
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) = true) : False := by
  subst hada
  have h : CardanoLedgerApi.V2.validTxOutValue
      (Shape.adaPlusOne outAda0 (ByteString.mk "") tn qOut0) = true :=
    andEqTrueL (validOutputs_of_validRewardingContext hv)
  rw [validTxOutValue_adaPlusOne_at_ada] at h
  exact Bool.noConfusion h

/-! ### §3.2 — SHAPE T1R: `P1R_T1_stmt`, with `accept` abstracted -/

/-- **`P1UnshapedForm accept` ⟹ `P1R_T1_stmt` at the same `accept`.**
Diff the conclusion below against `WSC.P1R_T1_stmt`: the binder list, the
`validRewardingContext` hypothesis, the `coveringNodeExists … = false`
hypothesis and the `outSum ≥ inSum + mintSigned` conclusion are character for
character the same. -/
theorem P1_unshaped_specialises_T1R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P1UnshapedForm accept) :
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
      accept ppCS
        (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
          pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
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
                fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee hv hcn hacc
  by_cases hada : cs = ByteString.mk ""
  · exact (shaped_invalid_at_ada_T1R cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
      dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee hada hv).elim
  · exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hada hv
      (paramsPublishedBy_T1R cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) hcn hacc

/-! ### §3.3 — SHAPE T2R: the MINT case (`q` free, sign unconstrained) -/

/-- **`P1UnshapedForm accept` ⟹ `P1R_T2_stmt` at the same `accept`.** `q` is a
free `Integer`, so this one statement covers mint AND burn — the half a reviewer
will want to see, because it is where `Model.mintSigned` bites and where the
`mintPos` variant is refuted (`WSC.P1RShapedWitness.mintPos_form_REFUTED`). -/
theorem P1_unshaped_specialises_T2R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P1UnshapedForm accept) :
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
      accept ppCS
        (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
          pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
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
                fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee hv hcn hacc
  by_cases hada : cs = ByteString.mk ""
  · exact (shaped_invalid_at_ada_T2R cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
      dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee hada hv).elim
  · exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hada hv
      (paramsPublishedBy_T2R cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) hcn hacc

/-! ### §3.4 — SHAPES T6R and T7R: output-side aggregation, without and with mint -/

/-- **`P1UnshapedForm accept` ⟹ `P1R_T6_stmt` at the same `accept`.** -/
theorem P1_unshaped_specialises_T6R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P1UnshapedForm accept) :
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
      accept ppCS
        (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
          dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
          key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
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
                fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee hv hcn hacc
  by_cases hada : cs = ByteString.mk ""
  · exact (shaped_invalid_at_ada_T6R cs tn plc owner inAda qIn ext in2Ada qIn2
      outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee hada hv).elim
  · exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hada hv
      (paramsPublishedBy_T6R cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) hcn hacc

/-- **`P1UnshapedForm accept` ⟹ `P1R_T7_stmt` at the same `accept`** — the
strongest single shaped P1 statement in the library (aggregation AND a nonzero
mint of unconstrained sign) falls out of the same unshaped form. -/
theorem P1_unshaped_specialises_T7R (accept : CurrencySymbol → ScriptContext → Prop)
    (H : P1UnshapedForm accept) :
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
      accept ppCS
        (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
          dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
          key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) →
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
                fee).scriptContextTxInfo.txInfoMint := by
  intro ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee hv hcn hacc
  by_cases hada : cs = ByteString.mk ""
  · exact (shaped_invalid_at_ada_T7R cs tn q plc owner inAda qIn ext in2Ada qIn2
      outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee
      hada hv).elim
  · exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hada hv
      (paramsPublishedBy_T7R cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) hcn hacc

/-! ## §4 — NON-VACUITY, and why the benchmark budget is 4400 and not 1600

Below the minimal accepting step count the `accept` hypothesis is unsatisfiable
and `P1UnshapedForm` is VACUOUS — true and worthless. This library's own history
is the reason the check is mandatory: task V3 stated P6 at budget 2500, got
`✅ Valid`, and the vacuity probe then showed the accept class was UNSAT
(`WSC/Shaped/Probe/G6Vacuous2500.lean`).

The theorem below is the two-sided answer for the UNSHAPED P1 statement, and it
is measured on the UNSHAPED term — `cekExecuteProgram
programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) K`, exactly the
program-and-inputs pair `WSC/Benchmark/P1Unshaped.lean` preps, with only the
meter changed. `WSC.P1RShapedWitness.ctxOk` is used as the witness because it is
already certified `validRewardingContext` (`ctxOk_valid`), redeemer-covered
(`WSC.t1R_realizable`), and no-covering-node (`ctxOk_no_covering_node`); the
shape it came from is irrelevant to the `∃`. -/

/-- **THE BENCHMARK IS NON-VACUOUS AT 4400 AND VACUOUS AT 1600.**

Conjuncts 1-3: `ctxOk` satisfies every TRANSACTION-level hypothesis of
`P1UnshapedForm` other than `accept` — ledger validity, the §1 params hypothesis,
and "no covering directory node for `cs = "MMM"`", i.e. the policy is REGISTERED.
The remaining hypothesis is about the ASSET, not the transaction, and is
`ctxOk_asset_is_not_ada` below.

Conjunct 4: the real compiled bytecode HALTS SUCCESSFULLY on it with 4400 steps.
Conjunct 5: it does NOT halt with 1600 steps.

Conjunct 5 is the load-bearing one for the benchmark's design. Two unshaped preps
of this validator already exist and are cheap — `WSC.appliedGlobal` at 600
(2.0 s) and `WSC.appliedGlobal1600` at 1600 (≈38 s) — and a P1 statement over
either of them would be VACUOUS, hence worthless. `WSC.P1RShapedWitness.K_T1R_is_2343`
pins this witness's cost two-sided (`Halt` at 2343, budget-`Error` at 2342), and
the most expensive of P1's four shapes needs 2777 (`K_T6R_is_2777`); the
`mintPos`-refuting burn witness needs 2567 (`K_T2R_is_2567`), T7R 2567 and T8R
2288. So the whole P1 family lives in [2288, 2777] and 4400 clears it with 1623
steps of headroom, while 1600 clears none of it. The independent corroboration on
a REAL off-chain transaction is `WSC.GlobalModelRefuted.golden_shows_budget_gap`:
the golden `transfer-member-single-policy` costs 2782 steps and does not halt at
1600.

HONEST LIMIT: this is an `∃`, so it proves 4400 is non-vacuous. It does NOT prove
that 1600's P1 class is empty — only that no context this library has ever
measured as an accepting registered transfer fits inside 1600, the cheapest being
2288. -/
theorem P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600 :
    validRewardingContext P1RShapedWitness.ctxOk = true
    ∧ paramsPublishedBy P1RShapedWitness.ctxOk
        = some (ByteString.mk "DIRCS",
                IsData.toData (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")))
    ∧ Model.coveringNodeExists (ByteString.mk "DIRCS") (ByteString.mk "MMM")
        P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoReferenceInputs = false
    ∧ P1ShapedWitness.isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
        programmableLogicGlobal1600.script
        (globalInputs1600 P1ShapedWitness.ppCS P1RShapedWitness.ctxOk) 4400) = true
    ∧ P1ShapedWitness.isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
        programmableLogicGlobal1600.script
        (globalInputs1600 P1ShapedWitness.ppCS P1RShapedWitness.ctxOk) 1600) = false := by
  native_decide

/-- The §4 witness's asset is `"MMM"`, so the restored `cs ≠ ByteString.mk ""`
guard is satisfied and the non-vacuity certificate covers the CURRENT form —
not merely the form as it stood before the guard was restored. (This is the one
hypothesis the `native_decide` conjunction above cannot carry, because it is a
`Prop` about the asset rather than a `Bool` about the context.) -/
theorem ctxOk_asset_is_not_ada : ByteString.mk "MMM" ≠ ByteString.mk "" := by decide

/-- The `∃` in the form `P1UnshapedForm`'s accept hypothesis needs: there is a
context at which the accept side of the benchmark statement is SATISFIABLE on the
`.exec` term. `isHaltB_sound` is `WSC.P1ShapedWitness.isHaltB_sound`. -/
theorem P1_unshaped_accept_is_satisfiable :
    ∃ (ppCS : CurrencySymbol) (ctx : ScriptContext),
      validRewardingContext ctx = true
      ∧ isSuccessful (PlutusCore.UPLC.CekMachine.cekExecuteProgram
          programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) 4400) :=
  ⟨P1ShapedWitness.ppCS, P1RShapedWitness.ctxOk,
   P1RShapedWitness.ctxOk_valid,
   P1ShapedWitness.isHaltB_sound _
     P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600.2.2.2.1⟩

/-! ## §5 — AXIOM AUDIT

**NOTHING IN THIS MODULE MAY CARRY `sorryAx`** — there is no `blaster` call here,
so anything that did would be a hole, not a measurement. Measured profile:

| declarations | axioms |
|---|---|
| §2.1's two `Bool` projections, `validTxOutValue_of_mem_validOutputs`, `validTxOutValue_adaPlusOne_at_ada`; §3.0's four `rfl`s | NONE |
| §4's `ctxOk_asset_is_not_ada` | `[propext]` (`decide` on `ByteString`) |
| §2.1's `validScriptContext_of_…`, `validOutputs_of_…`, `outputs_ledger_valid_of_…`; §3.1's four vacuity theorems; §3.2-§3.4's four specialisations | `[propext, Quot.sound]` — the Lean standard set |
| §4's two measured theorems | the above plus `Lean.ofReduceBool`, `Lean.trustCompiler` (`native_decide`) |

CORRECTION OF THE RECORD: this section previously claimed the four
specialisations carried "NO axioms at all". That was never true — they carried
`[propext, Quot.sound]` before the ada repair as well, inherited from
`validRewardingContext`'s own dependency cone, which their STATEMENTS mention. The
repair therefore adds no axiom that was not already there; what it adds is §2.1
and §3.1, and those land in the same bucket. -/

#print axioms WSC.Benchmark.andEqTrueL
#print axioms WSC.Benchmark.andEqTrueR
#print axioms WSC.Benchmark.validScriptContext_of_validRewardingContext
#print axioms WSC.Benchmark.validOutputs_of_validRewardingContext
#print axioms WSC.Benchmark.validTxOutValue_of_mem_validOutputs
#print axioms WSC.Benchmark.outputs_ledger_valid_of_validRewardingContext
#print axioms WSC.Benchmark.validTxOutValue_adaPlusOne_at_ada
#print axioms WSC.Benchmark.paramsPublishedBy_T1R
#print axioms WSC.Benchmark.paramsPublishedBy_T2R
#print axioms WSC.Benchmark.paramsPublishedBy_T6R
#print axioms WSC.Benchmark.paramsPublishedBy_T7R
#print axioms WSC.Benchmark.shaped_invalid_at_ada_T1R
#print axioms WSC.Benchmark.shaped_invalid_at_ada_T2R
#print axioms WSC.Benchmark.shaped_invalid_at_ada_T6R
#print axioms WSC.Benchmark.shaped_invalid_at_ada_T7R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T1R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T2R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T6R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T7R
#print axioms WSC.Benchmark.ctxOk_asset_is_not_ada
#print axioms WSC.Benchmark.P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600
#print axioms WSC.Benchmark.P1_unshaped_accept_is_satisfiable

end Benchmark
end WSC
