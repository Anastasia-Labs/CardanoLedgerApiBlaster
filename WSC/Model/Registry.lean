/-
WSC/Model/Registry.lean — **LAYER 0 of the P1 containment architecture: ONE
SHARED EXEMPTION PREDICATE.**

WHY THIS MODULE EXISTS. Three machine-checked defects of the P1 statements
(`WSC.Benchmark.P1UnshapedForm`, `WSC.Model.P1_model`) had the same shape: a
hypothesis meant to say "`cs` is a programmable token subject to containment"
failed to exclude a context the compiled bytecode treats as EXEMPT. They lived on
three DIFFERENT adversary surfaces:

| defect | surface | closed by |
|---|---|---|
| 1 — ada | VALUE (the positional ada strip, ProgrammableLogicBase.hs@2306678:409/:424/:638) | the `cs == ""` disjunct of `exempt` |
| 2 — arity | DATUM (both walks' negative arms, :890-906 / :993-1013) | `dirNodeInterval`'s 2-field reader |
| R3 — no-ada input | VALUE again (`ptail` at :424) | `validRewardingContext`'s INPUT half (NOT here — it is a hypothesis of the statements) |

and the statements re-derived the exclusion by hand, twice, and drifted. This
module is the single definition object both statements now quantify over.

IMPORT-GRAPH FACT THAT MAKES THIS POSSIBLE (checked, load-bearing): it imports
only `WSC.Model.GlobalModel` (which imports `CardanoLedgerApi.V3`, `WSC.Redeemer`,
`WSC.Spec`, `PlutusCore.Value.Algebra` — GlobalModel.lean:79-82) and
`WSC.Model.Ground` (`WSC.Spec`, `PlutusCore.Value.Algebra` — Ground.lean:25-26).
So it is importable by `WSC/Props/P1_Transfer.lean`, `WSC/Composition.lean` AND
`WSC/Benchmark/P1UnshapedStatement.lean` alike. `WSC.Model.coveringNodeExists`
MOVED HERE from `WSC/Props/P1_Transfer.lean` (it kept its fully-qualified name,
so every existing reference still resolves), and `WSC.Composition.coveringRaw` —
a verbatim duplicate kept only to dodge an import cycle, self-documented at
Composition.lean:1400-1410 — is DELETED in favour of `exemptible`.

⚠️ **K9 (design-integrity review rule) APPLIES TO THIS FILE AS WELL AS TO
`WSC/Benchmark/P1UnshapedStatement.lean`.** A benchmark statement about compiled
bytecode must not assume a deployment. Because the benchmark statement quantifies
over the predicates defined here, a deployment axiom smuggled into THIS module
would enter the benchmark through the import and a grep of the statement module
alone would not see it. So: nothing in this file may mention `WSC.Deployed`,
`WSC.OnChain`, `WSC.DirWF`/`WSC.DIRWF` or any `WSC.TS*`. Everything below is a
function of `ScriptContext` fields only (ARCHITECTURE.md D3 / Tier 0.1).

REVISION PIN: every `ProgrammableLogicBase.hs` line number in this file is a
wsc-poc **2306678** line (`WSC/flats/PROVENANCE.md:6` pins the flat to that
revision). Line numbers at other revisions do NOT match.
-/
import WSC.Model.GlobalModel
import WSC.Model.Ground

namespace WSC.Model

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext TxInInfo valueOf)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## §1 — the node reader, AS THE BYTECODE READS IT ON BOTH EXEMPTION ARMS -/

/-- **The directory node as the two exemption arms actually read it.**

* MINT walk, `PNonMember` (`pcheckMintLogicAndGetProgrammableValue`,
  ProgrammableLogicBase.hs@2306678:993-1013): the `pmatch` at :997-1001 names ONLY
  `{pkey, pnext}`, and the guards at :1006-1008 use only those two.
* TRANSFER walk, negative branch (:881-906): its `pmatch` at :881-886 NAMES
  `ptransferLogicScript` (:884) but the branch at :890-906 never forces it.
  MEASURED, not inferred from laziness:
  `WSC.BaseAbsentProbe.transfer_walk_also_accepts_the_truncated_node`
  (WSC/Benchmark/BaseAbsentProbe.lean:518) exhibits the bytecode ACCEPTING a
  2-field node on the transfer arm.

TIGHTNESS IS MEASURED, NOT ASSUMED — this is the answer to "does the fix close
only the two witnesses you happened to build?". `WSC/Review/ExemptionCensus.lean`
pins the whole acceptance BOUNDARY on BOTH arms at 44000 steps
(`arity_floor_mint_walk`:115, `arity_floor_transfer_walk`:127): a one-field list,
a non-`B` key, a non-`B` next, `Data.Constr 0 [B k, B n]` and
`Data.Map [(B k, B n)]` ALL `perror`. So the bytecode's node-acceptance set is
EXACTLY `Data.List (Data.B k :: Data.B n :: _)`: this pattern accepts neither more
nor less.

Contrast `WSC.Model.dirNodeFields` (GlobalModel.lean:318-320), which demands a
THIRD field. That is defect 2: simultaneously too strong (a field neither walk
reads) and too weak (it also accepts 6+ fields). -/
def dirNodeInterval : Data → Option (CurrencySymbol × CurrencySymbol)
  | Data.List (Data.B k :: Data.B n :: _) => some (k, n)
  | _ => none

/-! ## §2 — the covering test, old and repaired -/

/-- **THE OLD (3-FIELD) COVERING TEST — MOVED HERE VERBATIM from
`WSC/Props/P1_Transfer.lean:222-234`, name unchanged.**

Some reference input is a `phasCSH`-authenticated directory node whose
`(key, next)` interval strictly covers `cs`. Ground truth: a pure function of
`txInfoReferenceInputs` and their datums.

🛑 IT IS NOT THE BYTECODE'S EXEMPTION TEST (defect 2). It is kept, unchanged, for
exactly two reasons: the four PUBLISHED shaped P1 theorems
(`WSC/Props/Shaped/P1ShapedR.lean`) state their exemption hypothesis in it, and at
those four shapes it COINCIDES with `exemptible` by `rfl` for all leaves
(`WSC.Benchmark.exemptible_eq_covering_T{1,2,6,7}R`). New statements must use
`isProgrammable`/`exempt` below. -/
def coveringNodeExists (dirCS : CurrencySymbol) (cs : CurrencySymbol) :
    List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeFields d with
            | some (k, n, _) =>
                decide (k < cs) && decide (cs < n) &&
                  (hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || coveringNodeExists dirCS cs rest

/-- **The validator's own exemption certificate, on the DATUM surface**: some
reference input is a `phasCSH`-authentic directory node (:750-753, mirrored by
`Model.hasCSH`, GlobalModel.lean:140-147) whose `(key, next)` interval STRICTLY
covers `cs`, read through the 2-field `dirNodeInterval`.

**EXISTENTIAL OVER THE WHOLE REFERENCE-INPUT LIST, NOT INDEXED — and the cost of
that is published here rather than buried.**

* WHY NOT INDEXED. The bytecode resolves the node at a REDEEMER-SUPPLIED index
  through the raw `pdropList` (:879 transfer, :995 mint), and the cursor that
  chooses which proof goes with which policy is a validator-computed accumulator
  over the AGGREGATED input value (:867-871). Writing that cursor into the
  statement would re-create the transcription whose global fidelity axiom is
  REFUTED (`WSC/Model/GlobalModelRefuted.lean`) and would violate the statement's
  own Tier 0.1 ground-truth rule (P1UnshapedStatement.lean:311-325). The
  ADDRESSABLE node set really is this list: `pdropList`'s PCB denotation CLAMPS a
  negative count to 0 and `perror`s past the end
  (PlutusCore/UPLC/BuiltinFunctions/List.lean:102-110), measured at index 99 and
  index -1 (`WSC/Benchmark/FidelityAuditProbe.lean`, ctxK/ctxL — both REJECT).
* **THE COVERAGE COST, STATED (review finding).** The over-approximation is sound
  but it monotonically SHRINKS the statement's positive content: `exemptible`
  fires on ANY authentic-looking covering node ANYWHERE in
  `txInfoReferenceInputs`, while the bytecode consumes only the node the redeemer
  ADDRESSES. So a transaction that merely CARRIES such a node — with no proof
  pointing at it — has `exempt = true` and `P1UnshapedFormD` asserts nothing about
  it, even though the transfer walk genuinely retained `cs`. The loss grows with
  reference-input count. Under `DirWF` it is not a live loss (a covering interval
  contains no registered key), but the BENCHMARK layer is precisely the layer that
  must not assume `DirWF`, so at that layer the loss is real.
* NOTE the measured tightness cited on `dirNodeInterval` is about DATUM SHAPE at a
  FIXED index. It does not speak to this addressing over-approximation. Two
  different claims; do not quote one for the other. -/
def exemptible (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeInterval d with
            | some (k, n) =>
                decide (k < cs) && decide (cs < n) &&
                  (hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || exemptible dirCS cs rest

/-- **`exempt` — THE FULL EXEMPTION DISJUNCTION, one disjunct per adversary
surface the walks expose.**

* `cs == ""` — the ADA slot. CITED, not re-derived: DIR-1 (`pInsert` asserts every
  inserted key is exactly 28 bytes, `LinkedList/Common.hs:229`) plus DIR-5 (the
  only `""` key is the head sentinel `pInit` creates, `PTokenDirectory.hs:206-210`,
  and `isHeadNode` compares `pkey` to `pemptyCSData`, :190-194) means ada is never
  a directory key. The BYTECODE-side reason ada escapes containment is DIFFERENT
  and deeper — the positional ada strip at :409/:424/:638 removes the first
  currency entry unconditionally — which is why this disjunct must be stated and
  CANNOT be derived from the covering test. Measured:
  `WSC.Review.AdversarialProbe.ada_disjunct_is_the_only_one_that_fires`:398 shows
  `exemptible` is FREE-FALSE at `cs = ""` (covering needs `k < ""` and nothing is
  strictly less than `""`), so the ada disjunct carries the whole ada exclusion.
  That free-falseness is exactly what hid defect 1: the old hypothesis
  `coveringNodeExists … = false` was VACUOUSLY SATISFIED at ada.
* `exemptible …` — the DATUM surface, above.

**WHAT IS NOT A DISJUNCT, AND WHY.** The VALUE surface (defect 1's bytecode cause
and R3) is closed by `validRewardingContext`, a HYPOTHESIS of both statements, not
by this predicate — `WSC.Review.ExemptionCensus.the_saving_clause_is_validInputs`
(:262) measures that it is the INPUT half (`validInputs`,
CardanoLedgerApi/V3/Contexts.lean:1645-1654) that does the work, while every
output is `validTxOutValue`-valid. -/
def exempt (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  (cs == ByteString.mk "") || exemptible dirCS cs refs

/-- **THE SHARED PREDICATE, STATED POSITIVELY**: *`cs` is a currency symbol this
transaction is obliged to contain.*

Positive by construction. The double negative (`¬ coveringNodeExists`) is what hid
defect 1 — at `cs = ada` the covering test is FREE-FALSE, so the hypothesis was
VACUOUSLY SATISFIED rather than unsatisfiable
(`WSC/Benchmark/P1UnshapedStatement.lean:131-135`). Here the ada slot makes
`isProgrammable = false`, i.e. P1 says NOTHING, which is the correct and visible
failure mode. -/
def isProgrammable (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  !(exempt dirCS cs refs)

/-! ## §3 — the params clause, shared by both statements -/

/-- The two fields of the protocol-params datum the validator reads: position 0
(`directoryNodeCS`, a `Data.B`) and position 1 (`progLogicCred`, kept RAW —
`pparamsAtRefIdx` never decodes it). MOVED HERE from
`WSC/Benchmark/P1UnshapedStatement.lean` (which used `SeizeModel.paramsDirCSAndProgCred`)
so that `P1_model` and the benchmark share ONE definition object; the migration
pins `paramsDirCSAndProgCredRaw = SeizeModel.paramsDirCSAndProgCred` by `rfl`
downstream (`WSC.Benchmark.paramsDirCSAndProgCredRaw_eq_seize`). -/
def paramsDirCSAndProgCredRaw : Data → Option (CurrencySymbol × Data)
  | Data.List (Data.B dcs :: plcD :: _) => some (dcs, plcD)
  | _ => none

/-- `plgrParamsRefIdx` — the FIFTH field of `PTransferAct`
(ProgrammableLogicBase.hs@2306678:1054; FIVE fields post-#112). Constructor index
0 is `PTransferAct`; any other index is `PSeizeAct`, a hard error in this
validator (:1290-1291), so `none` there is not a loss. Extra fields are ignored,
exactly as a raw `phead`/`ptail` chain does.

⚠️ **ARITY IS A VACUITY TRAP.** `PTransferAct` had FOUR fields at wsc-poc
`f918ec6` and FIVE at `2306678`. Against a 4-field redeemer this returns `none`,
`paramsPublishedBy` returns `none`, the params hypothesis becomes unsatisfiable
and the ENTIRE BENCHMARK BECOMES VACUOUSLY TRUE. Pinned loud-failingly by
`WSC.Benchmark.transferAct_arity_pin`. -/
def transferParamsRefIdx : Data → Option Integer
  | Data.Constr 0 (_ :: _ :: _ :: _ :: Data.I p :: _) => some p
  | _ => none

/-- **The protocol-params datum this transaction publishes**, read the way
`pparamsAtRefIdx` (ProgrammableLogicBase.hs@2306678:820-834) reads it: reference
input at the redeemer's `plgrParamsRefIdx` via the raw `pdropList` (so a negative
index is CLAMPED, not rejected — `Model.atIdx`, GlobalModel.lean:128-131), inline
datum, then positions 0 and 1.

**DELIBERATELY OMITS the `phasCSH ppCS` authentication gate** the validator
applies at :828. That makes the hypothesis WEAKER, so the statements quantify over
MORE contexts — including every context whose params UTxO is unauthenticated,
which are contexts the bytecode ERRORS on, so `accept` is false there and the
obligation is discharged by the accept hypothesis rather than by an assumption.
The gate is re-introduced, as `paramsAuthAtIdx`, only in the honest-deployment
corollary (Layer 2), where it is measured inhabited
(`WSC/Review/DesignProbe.lean:209,:221`). -/
def paramsPublishedBy (ctx : ScriptContext) : Option (CurrencySymbol × Data) :=
  match transferParamsRefIdx ctx.scriptContextRedeemer with
  | none => none
  | some idx =>
      match atIdx idx ctx.scriptContextTxInfo.txInfoReferenceInputs with
      | none => none
      | some i =>
          match i.txInInfoResolved.txOutDatum with
          | .OutputDatum d => paramsDirCSAndProgCredRaw d
          | _ => none

/-! ## §4 — the containment obligation, named once -/

/-- **THE CONTAINMENT OBLIGATION.** *The amount of `(cs, tn)` at outputs on the
mini-ledger base credential is at least the amount at inputs spent from it, plus
the SIGNED net mint.*

Named once so that the benchmark statement and the model statement read
IDENTICALLY — drift between two hand-maintained copies is what produced defects 1
and 2. `outSum`/`inSum` are `WSC/Model/Ground.lean:45-58`; the mint term is
`WSC.mintOf` (`WSC/Spec.lean:45`), which is definitionally
`WSC.Model.mintSigned` (`WSC/Props/P1_Transfer.lean:203`) — spelled `WSC.mintOf`
here only because `mintSigned` lives DOWNSTREAM of this module.

THE MINT IS SIGNED. The `max(mint, 0)` variant is MACHINE-REFUTED on a burn
(`WSC.P1RShapedWitness.mintPos_form_REFUTED`); do not "repair" it. -/
def Contained (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Prop :=
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
      + _root_.WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-! ## §5 — THE FOUR SHIPPED LEMMAS -/

/-- **REFINEMENT.** The old 3-field reader is a refinement of the new 2-field one:
whenever `dirNodeFields` sees a node, `dirNodeInterval` sees the same interval.
(First proved at `WSC/Review/DesignProbe.lean:70`; that copy is now redundant.) -/
theorem dirNodeInterval_of_dirNodeFields {d : Data} {k n : CurrencySymbol} {tls : Data}
    (h : dirNodeFields d = some (k, n, tls)) : dirNodeInterval d = some (k, n) := by
  unfold dirNodeFields at h
  split at h
  · injection h with h; injection h with h1 h2; subst h1
    injection h2 with h3 _; subst h3
    rfl
  · exact Option.noConfusion h

/-- **STRENGTHENING, forward direction.** `exemptible` is TRUE wherever
`coveringNodeExists` is: the repaired predicate sees strictly more nodes. -/
theorem exemptible_of_coveringNodeExists {dirCS cs : CurrencySymbol} :
    ∀ refs : List TxInInfo,
      coveringNodeExists dirCS cs refs = true → exemptible dirCS cs refs = true := by
  intro refs
  induction refs with
  | nil => intro h; simp [coveringNodeExists] at h
  | cons i rest ih =>
      intro h
      simp only [coveringNodeExists, Bool.or_eq_true] at h
      simp only [exemptible, Bool.or_eq_true]
      rcases h with hhd | htl
      · refine Or.inl ?_
        match hdat : i.txInInfoResolved.txOutDatum with
        | .OutputDatum d =>
            simp only [hdat] at hhd ⊢
            match hf : dirNodeFields d with
            | some (k, n, tls) =>
                simp only [hf] at hhd
                simp only [dirNodeInterval_of_dirNodeFields hf]
                exact hhd
            | none => simp only [hf] at hhd; exact Bool.noConfusion hhd
        | .OutputDatumHash _ => simp only [hdat] at hhd; exact Bool.noConfusion hhd
        | .NoOutputDatum => simp only [hdat] at hhd; exact Bool.noConfusion hhd
      · exact Or.inr (ih htl)

/-- **STRENGTHENING, the form the statements use.** `exemptible … = false` is a
STRICTLY STRONGER hypothesis than `coveringNodeExists … = false`. This is the ONE
genuinely new proof obligation of Layer 0; `WSC/Review/DesignProbe.lean:85`
explicitly left it to the implementer. -/
theorem coveringNodeExists_false_of_exemptible_false {dirCS cs : CurrencySymbol}
    {refs : List TxInInfo} (h : exemptible dirCS cs refs = false) :
    coveringNodeExists dirCS cs refs = false := by
  cases hc : coveringNodeExists dirCS cs refs with
  | false => rfl
  | true =>
      rw [exemptible_of_coveringNodeExists refs hc] at h
      exact Bool.noConfusion h

/-- The two spellings of the guard are the same `Bool`. -/
theorem isProgrammable_eq_not_exempt (dirCS cs : CurrencySymbol) (refs : List TxInInfo) :
    isProgrammable dirCS cs refs = !(exempt dirCS cs refs) := rfl

/-- `isProgrammable = true` unpacks to BOTH disjuncts being false. -/
theorem exempt_false_of_isProgrammable {dirCS cs : CurrencySymbol} {refs : List TxInInfo}
    (h : isProgrammable dirCS cs refs = true) : exempt dirCS cs refs = false := by
  simpa [isProgrammable] using h

/-- …in particular `cs` is not ada. This is the half `WSC/Composition.lean:1141`
(`LeafSet.p1`) and `:1520` (`nonEscape_of_contain` → `LR_BALANCE_SLOT`) consume
under the name `cs ≠ adaSymbol`. -/
theorem ne_ada_of_isProgrammable {dirCS cs : CurrencySymbol} {refs : List TxInInfo}
    (h : isProgrammable dirCS cs refs = true) : cs ≠ ByteString.mk "" := by
  intro hcs
  have := exempt_false_of_isProgrammable h
  rw [exempt, hcs] at this
  simp at this

/-- …and the datum half. -/
theorem exemptible_false_of_isProgrammable {dirCS cs : CurrencySymbol}
    {refs : List TxInInfo} (h : isProgrammable dirCS cs refs = true) :
    exemptible dirCS cs refs = false := by
  have := exempt_false_of_isProgrammable h
  rw [exempt] at this
  simpa using (Bool.or_eq_false_iff.mp this).2

/-- **THE ADA SLOT IS EXEMPT, unconditionally, for every reference-input list.**
So `P1UnshapedFormD`/`P1UnshapedFormH` say NOTHING at `cs = adaSymbol` — the
correct and visible failure mode, and the exact defect-1 repair. -/
theorem exempt_at_ada (dirCS : CurrencySymbol) (refs : List TxInInfo) :
    exempt dirCS (ByteString.mk "") refs = true := by
  simp [exempt]

/-- The contrapositive, in the form a `by_cases hada : cs = ByteString.mk ""`
branch wants. -/
theorem ne_ada_of_exempt_false {dirCS cs : CurrencySymbol} {refs : List TxInInfo}
    (h : exempt dirCS cs refs = false) : cs ≠ ByteString.mk "" := by
  intro hcs; rw [hcs, exempt_at_ada] at h; exact Bool.noConfusion h

/-- The converse assembly the statements need: NOT ada plus NOT exemptible gives
the positive guard. -/
theorem isProgrammable_of {dirCS cs : CurrencySymbol} {refs : List TxInInfo}
    (hada : cs ≠ ByteString.mk "") (hex : exemptible dirCS cs refs = false) :
    isProgrammable dirCS cs refs = true := by
  simp only [isProgrammable, exempt, hex, Bool.or_false, Bool.not_eq_true']
  simpa using hada

#print axioms dirNodeInterval_of_dirNodeFields
#print axioms exemptible_of_coveringNodeExists
#print axioms coveringNodeExists_false_of_exemptible_false
#print axioms isProgrammable_eq_not_exempt
#print axioms exempt_false_of_isProgrammable
#print axioms ne_ada_of_isProgrammable
#print axioms exemptible_false_of_isProgrammable
#print axioms exempt_at_ada
#print axioms ne_ada_of_exempt_false
#print axioms isProgrammable_of

end WSC.Model
