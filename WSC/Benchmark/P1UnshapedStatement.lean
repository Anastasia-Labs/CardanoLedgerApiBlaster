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
| `cs ≠ ByteString.mk ""` | — (not needed: the shaped bytecode theorems are `✅ Valid` without it) |
| `paramsPinned ppCS dirCS base (…refs) = true` | `paramsPublishedBy ctx = some (dirCS, toData base)` |
| `coveringNodeExists dirCS cs (…refs) = false` | identical |
| `∀ o ∈ outs, validTxOutValue o.txOutValue = true` | subsumed by `validRewardingContext ctx` |
| `outSum base cs tn … ≥ inSum base cs tn … + mintSigned cs tn …` | identical |

So the unshaped statement was not invented here. What is new is only that the
accept hypothesis names the COMPILED PROGRAM instead of the transcription — which
matters, because the transcription's fidelity axiom is FALSE at wsc-poc
`2306678` and was retracted (`WSC/Model/GlobalModelRefuted.lean`), so `P1_model`
implies nothing about production. `base` is a general `Credential` here for the
same reason it is in `P1_model`: nothing about P1 needs it to be a script
credential.

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
`accept ppCS ctx`; ONE hypothesis is added (§1's, and the module header explains
why it is not optional); everything else is unchanged, clause for clause. -/

/-- **P1 — TRANSFER CONTAINMENT, UNSHAPED, over a FULLY SYMBOLIC `ScriptContext`,
parametric in the accept predicate.**

*For every ledger-valid transaction, every asset `(cs, tn)` whose policy is
REGISTERED (no authenticated directory node in the reference inputs covers `cs`,
so the walk's only exemption route is shut), and the mini-ledger base credential
`base` this transaction's own protocol-params datum publishes: if the real
compiled `programmableLogicGlobal` bytecode accepts, then the amount of
`(cs, tn)` at outputs on `base` is at least the amount at inputs spent from
`base` plus the SIGNED net mint of `(cs, tn)`.*

`accept` is abstract so that §3 can be proved in the kernel. The benchmark
instantiates it to `fun ppCS ctx => isSuccessful (appliedGlobalUCeiling.prop ppCS ctx)`
in `WSC/Benchmark/P1Unshaped.lean`. -/
def P1UnshapedForm (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
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

/-! ## §3 — SPECIALISATION: the unshaped statement gives the shaped ones

Each theorem below is the corresponding `P1R_*_stmt` of
`WSC/Props/Shaped/P1ShapedR.lean` with its `isSuccessful (appliedGlobalShapedT*R.prop …)`
hypothesis replaced by `accept ppCS (<shape> …)`, derived from `P1UnshapedForm accept`
by instantiation alone. Read together with §3.0, which is what discharges the
added hypothesis.

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

/-! ### §3.1 — SHAPE T1R: `P1R_T1_stmt`, with `accept` abstracted -/

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
  exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hv
    (paramsPublishedBy_T1R cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
      pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) hcn hacc

/-! ### §3.2 — SHAPE T2R: the MINT case (`q` free, sign unconstrained) -/

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
  exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hv
    (paramsPublishedBy_T2R cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
      pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) hcn hacc

/-! ### §3.3 — SHAPES T6R and T7R: output-side aggregation, without and with mint -/

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
  exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hv
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
  exact H ppCS _ (.ScriptCredential plc) dirCS cs tn hv
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

Conjuncts 1-3: `ctxOk` satisfies every hypothesis of `P1UnshapedForm` other than
`accept` — ledger validity, the §1 params hypothesis, and "no covering directory
node for `cs = "MMM"`", i.e. the policy is REGISTERED.

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

Expected: §3's four specialisations and §3.0's four `rfl`s carry NO axioms at all
(pure kernel reduction). §4's two carry the two `native_decide` compiler-trust
axioms and NOT `sorryAx` — no `blaster` call appears in this module. -/

#print axioms WSC.Benchmark.paramsPublishedBy_T1R
#print axioms WSC.Benchmark.paramsPublishedBy_T2R
#print axioms WSC.Benchmark.paramsPublishedBy_T6R
#print axioms WSC.Benchmark.paramsPublishedBy_T7R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T1R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T2R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T6R
#print axioms WSC.Benchmark.P1_unshaped_specialises_T7R
#print axioms WSC.Benchmark.P1_unshaped_nonvacuous_at_4400_and_vacuous_at_1600
#print axioms WSC.Benchmark.P1_unshaped_accept_is_satisfiable

end Benchmark
end WSC
