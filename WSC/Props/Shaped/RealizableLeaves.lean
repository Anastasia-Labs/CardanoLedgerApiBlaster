-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/RealizableLeaves.lean — **a `LeafSet` over a shape class that is
NOT empty** (task C4, audit finding **F1**).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS, AND WHAT CHANGED TO MAKE IT POSSIBLE
════════════════════════════════════════════════════════════════════════════
`WSC/Composition.lean`'s `top_claim` consumes `leaves : LeafSet hp Shape`. Two
`LeafSet` terms existed before this module, and audit §9 says exactly what each is
worth:

* `ShapeRealizability.t1VacuousLeaves` — over SHAPE T1, whose class is PROVED
  EMPTY. Every field is `absurd`. Worth nothing, and labelled as such.
* `Composition.containedLeaves` — over `ContainedTx`, an ACCOUNTING class whose
  defining property is that nothing leaves the mini-ledger by construction. Real,
  but it uses **no UPLC result** and its acceptance hypotheses are provably unused.

Task C1 re-cut the global validator's shapes to be node-realizable, so a third
option exists for the first time: a `Shape` class that is (a) inhabited by a
transaction a node would accept, and (b) one over which a **bytecode** theorem
about the production validator discharges a leaf. That is this module.

**THE HONEST HEADLINE, and it is a THREE-of-four result, not four-of-four.**
Over `T1RShape` — "this transaction is an instance of the re-cut SHAPE T1R at this
deployment's credentials" — the `LeafSet` fields stand as follows:

| field | discharged? | by what | uses the acceptance hypothesis? |
|---|---|---|---|
| `p1` | **YES** | `WSC.P1R_T1` — the production `programmableLogicGlobal` bytecode at budget 4400, via `bridge_T1R` + `WSC.LR_BUDGET_global` | **YES** — `NodeAcceptsGlobal` is consumed, and this is the ONLY leaf discharge in the library of which that is true |
| `p4` | YES | the SHAPE: T1R's `txInfoMint` is `[]`, so `mintPos cs = false` — a pure-transfer transaction mints nothing, so the custody obligation is discharged by its fourth disjunct | **NO** — `NodeAcceptsMinting` is unused, and §4 says so in the proof |
| `nopre` | YES | the SHAPE: T1R's two outputs both carry `NoOutputDatum`, so no output is a directory node and `registeredIn` is false — a pure-transfer transaction registers nothing | **NO** — no acceptance hypothesis, by the field's own signature |
| `p2` | **NO** | — | — |

So **N = 1**: `containment_on_realizable_class_of_p2` (§7) is the top claim over
this class carrying `p2` — the seize-validator leaf — as its single remaining
hypothesis. That is the smallest honest gap this campaign can currently state, and
§7.3 says precisely why `p2` cannot be closed here: P2 is proved at SHAPE **S1R**,
a seize-transaction shape, and a T1R transaction is not an S1R transaction. Closing
it needs a `Shape` that is the UNION of the twelve re-cut shapes and a P2 discharge
at each — which is a coverage argument, i.e. audit F2's other half, still open.

**WHAT A READER MUST NOT CONCLUDE.** Not "containment is proved". This is one
shape class, still doubly bounded (a 4400-step CEK budget and a fixed `Data`
skeleton), still carrying `p2`, and realizability is NECESSARY not SUFFICIENT (§6).
What is new is only this: the class is no longer empty, and a bytecode theorem now
does load-bearing work in a composed result. Audit F1's "the class, not the code,
does the work" is answered for one field over one class — not withdrawn.
-/
import WSC.Composition
import WSC.Props.Shaped.P1ShapedR
import WSC.Props.Shaped.GlobalRealizability
import WSC.Props.Shaped.NonVacuity
import WSC.Runs
import WSC.Realizability
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace WSC
namespace RealizableLeaves

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptInfo ScriptHash
                          ScriptPurpose TokenName TxInInfo TxOut findRedeemer
                          validScriptContext validScriptInfo validRewardingContext adaSymbol
                          credentialInWithdrawals)
open CardanoLedgerApi.V1.Value (valueOf)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §1 The SHAPE-T1R shape bridge

Exactly the `WSC/ShapeBridge.lean` pattern, at the re-cut shape: LEVEL 2 by `rfl`
(kernel-checked, no solver), LEVEL 3′ by `blaster`. The right-hand side is the RAW
metered CEK run on the denoted `ScriptContext` — no `#prep_uplc` output and no
optimizer in it at all — which is what `WSC.LR_BUDGET_global` names. -/

/-- **LEVEL 2, SHAPE T1R.** Kernel-checked; `#print axioms` carries no `sorryAx`. -/
theorem exec_T1R
    (ppCS : CurrencySymbol) (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    appliedGlobalShapedT1R.exec ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee
      = Runs.globalRun 4400 ppCS
          (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) := rfl

/-- **LEVEL 3′, SHAPE T1R** — the bridge at the level `WSC.P1R_T1` lives on. -/
theorem bridge_T1R
    (ppCS : CurrencySymbol) (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    isSuccessful (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)
      ↔ isSuccessful
          (Runs.globalRun 4400 ppCS
            (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)) := by blaster

/-! ## §2 The `Shape` predicate

`T1RShape hp ctx` says: `ctx` shares its `TxInfo` with an instance of the RE-CUT
SHAPE T1R, and three of that instance's free leaves are pinned to the deployment's
own parameters.

WHY EACH OF THE THREE IDENTIFICATIONS IS THERE — none is decoration:

* `hp.progLogicCred = .ScriptCredential plc` — without it `WSC.P1R_T1`'s
  `Model.outSum (.ScriptCredential plc) …` is a statement about a DIFFERENT
  credential than the composition's `outAtB hp.progLogicCred`. (`t1_class_is_empty`
  needed the same hypothesis, for the same reason.)
* `hp.globalLogicCred = .ScriptCredential w0` — SHAPE T1R runs at
  `RewardingScript (.ScriptCredential w0)`, and the leaf triggers at
  `RewardingScript hp.globalLogicCred`. Without it the leaf's `ctx'` is not the
  shape's context.
* `hp.directoryNodeCS = dirCS` — `WSC.P1R_T1`'s exemption hypothesis is about the
  `dirCS` published in the params reference datum; the leaf's is about
  `hp.directoryNodeCS`.

WHAT IS **NOT** REQUIRED, deliberately, because the theorem does not need it and
requiring it would shrink the class: the params datum's `glc`/`slc` fields are
left FREE, so the class contains transactions whose published params datum
disagrees with the deployment. `WSC.P1R_T1` holds over all of them. -/
def T1RShape (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  ∃ plc w0, hp.progLogicCred = Credential.ScriptCredential plc ∧
    hp.globalLogicCred = Credential.ScriptCredential w0 ∧
    ∃ cs tn owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
      pHash pCS pTn pAda pQty glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w1 a0 a1 rBase rTls fee,
      ctx.scriptContextTxInfo =
        (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
          pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
          key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo

/-! ## §2W THE SIDE CONDITION wsc-poc PR #112 FORCED INTO THE COMPOSITION

`Composition.top_claim` now also takes `WdrlPairShaped Shape` — *every
transaction of the class has a two-entry, both-script withdrawal map* — because
the post-#112 base validator indexes into `txInfoWdrl` instead of scanning it and
`Composition.p3_lifted` cannot close otherwise (`WSC/Props/P3_BaseWdrl.lean`).

SHAPE T1R has exactly that map already: `WSC.p1ShapedWdrl` is literally
`[(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]`, which is
`WSC.bwWdrl`.  So the new obligation costs the class NOTHING — the two theorems
below are `rfl` on the two withdrawal leaves.  That is not luck; it is why task
N6 cut SHAPE B1W at that map (see that module's header). -/

/-- SHAPE T1R's `txInfoWdrl` IS SHAPE B1W's, definitionally. -/
theorem p1ShapedWdrl_is_bwWdrl (w0 w1 : ByteString) (a0 a1 : Integer) :
    p1ShapedWdrl w0 w1 a0 a1 = WSC.bwWdrl w0 w1 a0 a1 := rfl

/-- **The side condition holds over SHAPE T1R.** -/
theorem t1RShape_wdrlPair (hp : WSC.HonestParams) :
    Composition.WdrlPairShaped (T1RShape hp) := by
  rintro ctx ⟨plc, w0, _, _, cs, tn, owner, inAda, qIn, ext, in2Ada, qIn2, outAda, qOut,
    dest, escAda, qEsc, pHash, pCS, pTn, pAda, pQty, glc, slc, nHash, nCS, nTn, nAda, nQty,
    key, next, tlsH, ilsH, gsCS, w1, a0, a1, rBase, rTls, fee, hti⟩
  exact ⟨w0, w1, a0, a1, by rw [hti]; rfl⟩

/-! ## §3 The two vocabulary lemmas

Both are ordinary Lean; neither uses a solver, `native_decide` or any axiom. -/

/-- ⚠️ **SUPERSEDED — `Composition.coveringRaw` NO LONGER EXISTS.**

This used to prove `Composition.coveringRaw = WSC.Model.coveringNodeExists`, i.e.
that the composition's local duplicate and `P1_Transfer`'s definition were the
SAME function. Both facts about that equality are now obsolete: the duplicate is
deleted, and `ShapedGlobalContainment.contain` states its exemption hypothesis in
`WSC.Model.exemptible` (the bytecode's 2-field node reader,
`WSC/Model/Registry.lean`), which is NOT the same function as
`WSC.Model.coveringNodeExists` — that difference IS defect 2.

The translation `ShapedGlobalContainment` → `WSC.P1R_T1` is therefore no longer an
equality; it is the STRENGTHENING
`WSC.Model.coveringNodeExists_false_of_exemptible_false`, restated here as the
§3 vocabulary lemma. It runs in the sound direction: the field now supplies the
STRONGER `exemptible … = false`, and the shaped theorem consumes the WEAKER
`coveringNodeExists … = false`. -/
theorem coveringNodeExists_false_of_exemptible_false_at
    (dirCS cs : CurrencySymbol) (is : List TxInInfo)
    (h : WSC.Model.exemptible dirCS cs is = false) :
    WSC.Model.coveringNodeExists dirCS cs is = false :=
  WSC.Model.coveringNodeExists_false_of_exemptible_false h

/-- **The off-shape slot lemma.** SHAPE T1R gives every value the canonical
`adaPlusOne` form — ada plus exactly one policy carrying exactly one token name —
so for any `(cs, tn)` that is neither ada nor the shape's own slot, `valueOf`
returns 0. This is what lets the `p1` field be proved for ALL `cs`/`tn` from a
theorem that is about the shape's own `cs`/`tn`. -/
theorem valueOf_adaPlusOne_off (n : Integer) (cs0 tn0 : ByteString) (q : Integer)
    (cs tn : ByteString) (hada : cs ≠ adaSymbol) (hoff : ¬(cs = cs0 ∧ tn = tn0)) :
    valueOf cs tn (Shape.adaPlusOne n cs0 tn0 q) = 0 := by
  have hcs : (Data.B cs == Data.B Shape.adaCS) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; injection h with h; exact hada h
  by_cases hc0 : cs = cs0
  · subst hc0
    have htn : tn ≠ tn0 := fun h => hoff ⟨rfl, h⟩
    simp [valueOf, Shape.adaPlusOne, valueOf.visit, valueOf.find_token, hcs,
      Data.B.injEq, htn]
  · have hcs0 : (Data.B cs == Data.B cs0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; injection h with h; exact hc0 h
    simp [valueOf, Shape.adaPlusOne, valueOf.visit, hcs, hcs0]

/-- `ScriptContext` is a three-field structure; this is its extensionality, used to
identify the leaf's `ctx'` with the shape's own context. -/
theorem scriptContext_ext (c d : ScriptContext)
    (h1 : c.scriptContextTxInfo = d.scriptContextTxInfo)
    (h2 : c.scriptContextRedeemer = d.scriptContextRedeemer)
    (h3 : c.scriptContextScriptInfo = d.scriptContextScriptInfo) : c = d := by
  cases c; cases d; simp_all

/-- The `Rewarding w0` entry of SHAPE T1R's redeemer map is the shape's own
redeemer. Two `findRedeemer` steps: the `Spending` head misses (the constructors
differ before the symbolic `TxOutRef` is inspected), the next entry hits. -/
theorem findRedeemer_T1R_w0 (w0 w1 : ByteString) (rBase rTls : Integer) :
    findRedeemer (ScriptPurpose.Rewarding (.ScriptCredential w0))
        (p1RRedeemers w0 w1 rBase rTls p1ShapedRedeemer) = some p1ShapedRedeemer := by
  rw [p1RRedeemers,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.spending_beq_rewarding _ _),
    Realizability.findRedeemer_cons_hit]

/-! ## §4 `LeafSet.p1` at SHAPE T1R — **the bytecode discharge**

This is the one place in the library where a leaf obligation of the composition is
closed by a theorem about the compiled production bytecode, over a class that is
not empty. The chain, and every link is named:

1. `WSC.LR_CTX` at `ctx'` gives `validScriptContext ctx'`, whose FIRST conjunct
   (`validScriptInfo`) pins `ctx'`'s redeemer to the `Rewarding w0` entry of the
   shape's own redeemer map — so `ctx'` IS the shape's context, redeemer included.
   (Note where this comes from: the redeemer `WSC.LR_WDRL_RUNS_VALIDATOR` hands the
   composition is existentially quantified, so without this step the leaf's `ctx'`
   and the shaped theorem's context would differ in their redeemer field and the
   bridge would not apply. This is exactly the kind of silent mismatch the audit
   exists to catch.)
2. `WithinBudget`'s global clause gives `nodeStepsGlobal … ctx' ≤ K_global = 4400`.
3. `WSC.LR_BUDGET_global` at 4400 — its non-vacuity hypothesis DISCHARGED by
   `WSC.NonVacuity.globalNonVacuous_at_4400` (`native_decide` on the real CEK, no
   project axiom) — turns `NodeAcceptsGlobal` into
   `isSuccessful (Runs.globalRun 4400 …)`.
4. `bridge_T1R` (§1) turns that into the `.prop` term `WSC.P1R_T1` quantifies over.
5. `WSC.P1R_T1` — `✅ Valid`, budget 4400, witness K = 2343 (was 2603 pre-#112) — gives the containment
   inequality at the shape's OWN slot `(cs0, tn0)`.
6. `valueOf_adaPlusOne_off` (§3) gives it at every OTHER slot, where the shape puts
   no tokens at all.

`PropExecFaithful` (audit F8) still binds step 4→5: the hypothesis is on `.prop`
and every witness executes `.exec`. That is unchanged in kind by this module. -/

/-- Off-slot containment: at any `(cs, tn)` that is neither ada nor the shape's own
slot, SHAPE T1R's four values hold nothing, so both sums are 0 and containment is
`0 ≥ 0 + 0`. No bytecode and no acceptance hypothesis is involved — and none is
needed, because there is nothing to contain. -/
theorem outSum_inSum_off (base : Credential) (cs tn : ByteString)
    (hada : cs ≠ adaSymbol) (cs0 tn0 : ByteString) (hoff : ¬(cs = cs0 ∧ tn = tn0))
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer) :
    WSC.Model.outSum base cs tn
        [p1ShapedBaseOut plc outAda cs0 tn0 qOut, p1ShapedEscOut dest escAda cs0 tn0 qEsc] = 0
    ∧ WSC.Model.inSum base cs tn
        [p1ShapedBaseIn plc owner inAda cs0 tn0 qIn, p1ShapedExtIn ext in2Ada cs0 tn0 qIn2] = 0 := by
  have hOut := valueOf_adaPlusOne_off outAda cs0 tn0 qOut cs tn hada hoff
  have hEsc := valueOf_adaPlusOne_off escAda cs0 tn0 qEsc cs tn hada hoff
  have hIn := valueOf_adaPlusOne_off inAda cs0 tn0 qIn cs tn hada hoff
  have hIn2 := valueOf_adaPlusOne_off in2Ada cs0 tn0 qIn2 cs tn hada hoff
  constructor <;>
    simp [WSC.Model.outSum, WSC.Model.inSum, p1ShapedBaseOut, p1ShapedEscOut,
      p1ShapedBaseIn, p1ShapedExtIn, hOut, hEsc, hIn, hIn2]

/-- **`ShapedGlobalContainment` at SHAPE T1R** — `LeafSet.p1`'s content, with the
`NodeAccepts` ↔ bytecode boundary crossed. `WSC/Composition.lean`'s
`leafP1_of_shapedGlobalContainment` turns this into the field itself. -/
theorem shapedGlobalContainment_T1R (hp : WSC.HonestParams) :
    Composition.ShapedGlobalContainment hp (T1RShape hp) := by
  refine ⟨?_⟩
  intro ctx ctx' cs tn hoc hsh hbud hsame hoc' hsi hacc hcs hraw
  obtain ⟨plc, w0, hplc, hw0, cs0, tn0, owner, inAda, qIn, ext, in2Ada, qIn2, outAda, qOut,
    dest, escAda, qEsc, pHash, pCS, pTn, pAda, pQty, glc, slc, nHash, nCS, nTn, nAda, nQty,
    key, next, tlsH, ilsH, gsCS, w1, a0, a1, rBase, rTls, fee, hEq⟩ := hsh
  have hti' : ctx'.scriptContextTxInfo =
      (p1RShapedCtx cs0 tn0 plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo := by
    rw [hsame, hEq]
  -- STEP 1: `LR_CTX` pins `ctx'`'s redeemer, so `ctx'` IS the shape's own context.
  have hvsc : validScriptContext ctx' = true := WSC.LR_CTX ctx' hoc'
  have hvsi : validScriptInfo ctx' = true := by
    simp only [validScriptContext, Bool.and_eq_true] at hvsc; exact hvsc.1
  have hred : ctx'.scriptContextRedeemer = p1ShapedRedeemer := by
    simp only [validScriptInfo, Bool.and_eq_true, beq_iff_eq] at hvsi
    have h1 := hvsi.1
    rw [hsi, hw0, hti'] at h1
    simp only [p1RShapedCtx, ScriptInfo.toScriptPurpose, findRedeemer_T1R_w0] at h1
    exact Option.some.inj h1.symm
  have hctx' : ctx' =
      p1RShapedCtx cs0 tn0 plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee := by
    refine scriptContext_ext _ _ hti' ?_ ?_
    · rw [hred]; rfl
    · rw [hsi, hw0]; rfl
  -- STEP 2 + 3: the budget bridge, at 4400, with its non-vacuity discharged.
  have hsteps : WSC.nodeStepsGlobal hp.protocolParamsCS ctx' ≤ WSC.K_global := hbud.2.2 ctx' hsame
  have hrun : isSuccessful (Runs.globalRun WSC.K_global hp.protocolParamsCS ctx') :=
    (WSC.LR_BUDGET_global WSC.K_global WSC.NonVacuity.globalNonVacuous_at_4400
      hp.protocolParamsCS ctx' hoc' hsteps).mp hacc
  rw [hctx'] at hrun hvsc
  -- STEP 4: the shape bridge.
  have hprop : isSuccessful (appliedGlobalShapedT1R.prop hp.protocolParamsCS cs0 tn0 plc owner
      inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty
      hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 w1 a0 a1 rBase rTls fee) := (bridge_T1R ..).mpr hrun
  -- the ledger-normalization hypothesis, from the same `LR_CTX` verdict
  have hvrc : validRewardingContext
      (p1RShapedCtx cs0 tn0 plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) = true := hvsc
  -- the exemption hypothesis, translated into the shaped theorems' vocabulary
  have hcov : WSC.Model.coveringNodeExists hp.directoryNodeCS cs
      (p1RShapedCtx cs0 tn0 plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo.txInfoReferenceInputs
      = false := by
    exact coveringNodeExists_false_of_exemptible_false_at _ _ _ (by rw [← hEq]; exact hraw)
  -- STEP 5 / 6: the shape's own slot from the bytecode, every other slot from §3.
  rw [hEq, hplc]
  by_cases hslot : cs = cs0 ∧ tn = tn0
  · obtain ⟨h1, h2⟩ := hslot
    subst h1; subst h2
    exact WSC.P1R_T1 hp.protocolParamsCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
      dest escAda qEsc pHash pCS pTn pAda pQty hp.directoryNodeCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee hvrc hcov hprop
  · obtain ⟨hout, hin⟩ := outSum_inSum_off (.ScriptCredential plc) cs tn hcs cs0 tn0 hslot
      plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
    simp only [p1RShapedCtx] at hout hin ⊢
    rw [hout, hin]
    simp only [WSC.mintOf]
    exact Int.le_refl _

/-! ## §5 `LeafSet.p4` and `LeafSet.nopre` — discharged BY THE SHAPE, not by the code

Both are honest discharges and neither is a bytecode result. State them that way when
quoting: a SHAPE-T1R transaction is a pure transfer, so it mints nothing and
registers nothing, and the two obligations that are about minting and about
registration are therefore about something this class does not do.

**THE ACCEPTANCE HYPOTHESES BELOW ARE UNUSED, AND THAT IS DELIBERATELY VISIBLE.**
`p4_on_T1RShape` binds `NodeAcceptsMinting` as `_`, so Lean's own unused-variable
analysis has nothing to report and a reader cannot be misled into thinking the
minting policy's bytecode did any work here. It did not. (Audit §5.4 caught exactly
this pattern in `containedLeaves` via five `unused variable` warnings; the response
is to name the fact, not to hide the warning.) -/

/-- `NoOutputDatum` cannot decode as a directory node. -/
theorem dirNodeKey_eq_none (o : TxOut) (h : o.txOutDatum = .NoOutputDatum) :
    WSC.dirNodeKey o = none := by
  simp [WSC.dirNodeKey, WSC.dirNodeDatum, h]

/-- **`LeafSet.p4` at SHAPE T1R.** SHAPE T1R's `txInfoMint` is `[]`, so the fourth
custody disjunct (`nothing positive is minted under cs`) holds by computation.
No bytecode, no acceptance hypothesis. -/
theorem p4_on_T1RShape (hp : WSC.HonestParams) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (mlh : ScriptHash),
      WSC.Deployed hp → WSC.OnChain ctx → T1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.MintingScript cs →
      WSC.NodeAcceptsMinting hp.protocolParamsCS mlh ctx' →
      cs ≠ adaSymbol →
        WSC.noEscape hp.progLogicCred cs ctx.scriptContextTxInfo.txInfoOutputs = true
        ∨ credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
        ∨ credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
        ∨ WSC.mintPos cs ctx.scriptContextTxInfo.txInfoMint = false := by
  intro ctx _ctx' cs _mlh _hdep _hoc hsh _hbud _hsame _hoc' _hsi _hacc _hcs
  obtain ⟨plc, w0, _, _, cs0, tn0, owner, inAda, qIn, ext, in2Ada, qIn2, outAda, qOut,
    dest, escAda, qEsc, pHash, pCS, pTn, pAda, pQty, glc, slc, nHash, nCS, nTn, nAda, nQty,
    key, next, tlsH, ilsH, gsCS, w1, a0, a1, rBase, rTls, fee, hEq⟩ := hsh
  exact Or.inr (Or.inr (Or.inr (by rw [hEq]; rfl)))

/-- **`LeafSet.nopre` at SHAPE T1R.** Both of SHAPE T1R's outputs carry
`NoOutputDatum`, so neither is a directory node and the field's registration
hypothesis is FALSE — the obligation is discharged by `absurd`. A pure-transfer
transaction registers no policy, so `L-mint-needs-reg` has no instance here.

**READ THE SCOPE, because this is the field the audit calls the weakest leaf.**
This does NOT close `nopre` in general; it observes that the general problem does
not arise in this class. Any `Shape` that admits a registering transaction — which
the minting shapes M1R/L1R/DT1R do — gets the full obligation back. -/
theorem nopre_on_T1RShape (hp : WSC.HonestParams) :
    ∀ (L : Composition.Ledger) (ctx : ScriptContext) (L' : Composition.Ledger)
      (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → Composition.LedgerStep L ctx L' →
      Composition.HonestTx hp (T1RShape hp) ctx →
      ¬ Composition.RegisteredIn hp L cs →
      WSC.registeredIn hp.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoOutputs →
        Composition.OutOfBase hp.progLogicCred cs tn L = 0
        ∧ Composition.NonEscape hp.progLogicCred cs tn ctx := by
  intro _L ctx _L' cs _tn _hdep _hstep htx _hreg hnew
  obtain ⟨_, _, hsh⟩ := htx
  obtain ⟨plc, w0, _, _, cs0, tn0, owner, inAda, qIn, ext, in2Ada, qIn2, outAda, qOut,
    dest, escAda, qEsc, pHash, pCS, pTn, pAda, pQty, glc, slc, nHash, nCS, nTn, nAda, nQty,
    key, next, tlsH, ilsH, gsCS, w1, a0, a1, rBase, rTls, fee, hEq⟩ := hsh
  rw [hEq] at hnew
  simp only [p1RShapedCtx] at hnew
  obtain ⟨o, ho, _, hkey⟩ := hnew
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h <;>
    (rw [h, dirNodeKey_eq_none _ rfl] at hkey; exact absurd hkey (by simp))

/-! ## §6 THE `LeafSet` — three fields discharged, `p2` carried

`p2` is a PARAMETER, not a field this module proves. §7.3 of the header says why,
and the parameter's type is the field's statement verbatim, so a reader can see
exactly what is being assumed. -/

/-- **A `LeafSet` over a class that is NOT empty**, assuming only `p2`.

Contrast, in one line each, with the two `LeafSet` terms that came before:
`ShapeRealizability.t1VacuousLeaves` is over a PROVED-EMPTY class;
`Composition.containedLeaves` is over an inert accounting class and uses no
bytecode. This one is over a class with a machine-checked node-realizable
inhabitant (§8) and its `p1` field is the production bytecode. -/
theorem realizableLeaves (hp : WSC.HonestParams)
    (hp2 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → T1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
      WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
        Composition.Contain hp.progLogicCred cs tn ctx) :
    Composition.LeafSet hp (T1RShape hp) :=
  { p4 := p4_on_T1RShape hp
  , p1 := Composition.leafP1_of_shapedGlobalContainment hp (T1RShape hp)
            (shapedGlobalContainment_T1R hp)
  , p2 := hp2
  , nopre := nopre_on_T1RShape hp }

/-! ## §7 THE COMPOSED RESULT

`WSC.Composition.top_claim` at `Shape := T1RShape hp`, i.e.: *along any trace of
honest SHAPE-T1R transactions from genesis, no UTxO outside the mini-ledger holds a
registered programmable token* — assuming `p2`.

**BUDGETS AND SHAPE, so the bound travels with the claim.** Every step of such a
trace is a transaction whose `TxInfo` is an instance of SHAPE T1R (two inputs — one
at the mini-ledger base credential, one external pubkey; two outputs — one at base,
one escaping to a pubkey; empty mint; two script withdrawals; a THREE-entry redeemer
map covering all three script witnesses; two reference inputs — protocol params and
one directory node), and whose global-validator run halts within `K_global = 4400`
CEK steps. The accepting witness costs **K = 2343** steps (was 2603 pre-#112).

**THE FULL `#print axioms` LIST IS PRINTED AT BUILD TIME IN §9** — it is not
paraphrased here, because the point of this module is that the trust base is
countable. -/

/-- **THE TOP CLAIM OVER A NON-EMPTY SHAPE CLASS, assuming only `p2`.** -/
theorem containment_on_realizable_class_of_p2 (hp : WSC.HonestParams)
    (hdep : WSC.Deployed hp)
    (hp2 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → T1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
      WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
        Composition.Contain hp.progLogicCred cs tn ctx) :
    ∀ (L : Composition.Ledger), Composition.Reachable hp (T1RShape hp) L →
      Composition.I hp L :=
  Composition.top_claim hp (T1RShape hp) (realizableLeaves hp hp2)
    (t1RShape_wdrlPair hp) hdep

/-- The same result in the plain-English form: **no UTxO outside the mini-ledger
holds any registered programmable token.** -/
theorem no_tokens_outside_mini_ledger_on_realizable_class_of_p2
    (hp : WSC.HonestParams) (hdep : WSC.Deployed hp)
    (hp2 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → T1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
      WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
        Composition.Contain hp.progLogicCred cs tn ctx)
    (L : Composition.Ledger) (hR : Composition.Reachable hp (T1RShape hp) L)
    (cs : CurrencySymbol) (tn : TokenName)
    (hcs : cs ≠ adaSymbol) (hreg : Composition.RegisteredIn hp L cs) :
    ∀ u ∈ L, WSC.payCred u.utxoOut ≠ hp.progLogicCred →
      valueOf cs tn u.utxoOut.txOutValue = (0:Int) :=
  Composition.no_programmable_tokens_outside_mini_ledger hp (T1RShape hp)
    (realizableLeaves hp hp2) (t1RShape_wdrlPair hp) hdep L hR cs tn hcs hreg

/-! ## §8 THE CLASS IS NOT EMPTY — the whole point

`ShapeRealizability.t1_class_is_empty` proves that the PRE-re-cut SHAPE T1 class is
empty, unconditionally, and `t1_no_honest_step` proves the corresponding top claim
carries no information. This section is the exact opposite statement for the re-cut
shape, and it is what makes §7 worth stating at all.

`witnessParams` is a coherent honest deployment read off the witness's own leaves:
base credential `PROGLOGIC`, global logic `GLOBAL`, seize logic `SEIZE`, directory
policy `DIRCS`. `WSC.t1R_realizable` (task C1) independently certifies that the same
context satisfies `validRewardingContext`, satisfies **both** halves of Conway's
`hasExactSetOfRedeemers` (`redeemersExactAllPlutus`), is redeemer-covered, and is ACCEPTED by
the real compiled bytecode. -/

/-- A deployment whose parameters are the witness's own leaves. -/
def witnessParams : WSC.HonestParams :=
  { protocolParamsCS := P1ShapedWitness.ppCS
  , directoryNodeCS := ByteString.mk "DIRCS"
  , progLogicCred := .ScriptCredential (ByteString.mk "PROGLOGIC")
  , globalLogicCred := .ScriptCredential (ByteString.mk "GLOBAL")
  , seizeLogicCred := .ScriptCredential (ByteString.mk "SEIZE") }

/-- **THE CLASS IS INHABITED.** `WSC.P1RShapedWitness.ctxOk` — the SHAPE-T1R
accepting witness whose real-CEK cost is 2343 steps — is a member of the very class
§7 quantifies over. -/
theorem t1RShape_witness : T1RShape witnessParams WSC.P1RShapedWitness.ctxOk :=
  ⟨ByteString.mk "PROGLOGIC", ByteString.mk "GLOBAL", rfl, rfl,
   ByteString.mk "MMM", ByteString.mk "TOK", ByteString.mk "OWNER", 200, 5,
   ByteString.mk "EXT", 100, 4, 150, 5, ByteString.mk "DEST", 100, 4,
   ByteString.mk "PANCHOR", ByteString.mk "PARAMS", ByteString.mk "PTOK", 100, 1,
   ByteString.mk "GLOBAL", ByteString.mk "SEIZE",
   ByteString.mk "DIRNODE", ByteString.mk "DIRCS", ByteString.mk "NODETOK", 100, 1,
   ByteString.mk "MMM", ByteString.mk "ZZZ", ByteString.mk "TLS", ByteString.mk "ILS",
   ByteString.mk "GS", ByteString.mk "TLS", 0, 0, 77, 88, 50, rfl⟩

/-- **AND THE INHABITANT IS NODE-REALIZABLE**, which is what SHAPE T1 could not
say. Restated here so the two facts cannot be quoted apart: this class contains a
transaction context that is ledger-valid, redeemer-exact under the Conway rule C3
transcribed, and ACCEPTED by the production bytecode. -/
theorem realizable_inhabitant :
    T1RShape witnessParams WSC.P1RShapedWitness.ctxOk
    ∧ CardanoLedgerApi.V3.validRewardingContext WSC.P1RShapedWitness.ctxOk = true
    ∧ CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus
        WSC.P1RShapedWitness.ctxOk.scriptContextTxInfo = true :=
  ⟨t1RShape_witness, WSC.t1R_realizable.1, WSC.t1R_realizable.2.1⟩

/-! ## §10 CLOSING `p2` (task E1) — and WHY IT NEEDS A REFINEMENT OF THE CLASS

**THE QUESTION E1 ASKS, AND THE ANSWER THIS MODULE MEASURED.** Is `p2`
dischargeable VACUOUSLY-BUT-HONESTLY over `T1RShape`, because a SHAPE-T1R
transaction "has no seize withdrawal at all"? **No — that sentence is FALSE of
`T1RShape` as §2 defines it, and the reason is a genuine finding rather than a
technicality.** SHAPE T1R carries TWO script withdrawals,
`p1ShapedWdrl w0 w1 a0 a1 = [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]`
(`WSC/Shaped/GlobalShapedP1.lean:225`). `§2` pins only the first
(`hp.globalLogicCred = .ScriptCredential w0`, which the leaf's own trigger needs);
`w1` — the per-policy transfer-logic script the directory node names — is left
FREE, and `WSC.Deployed` is an OPAQUE AXIOM, so nothing in the library says the
deployment's `seizeLogicCred` is different from either of them. A `T1RShape`
transaction may therefore have `hp.seizeLogicCred = .ScriptCredential w1` (or even
`= .ScriptCredential w0`), in which case the seize validator really is invoked on
it and `p2` is a real obligation that no theorem in this library discharges: P2 is
proved at SHAPE **S1R**, and a T1R transaction is not an S1R transaction.

**So this is E1's case (b): the composition needs a different class, and below is
the smallest honest variant.** One conjunct is added, stated in the composition's
own ground-truth vocabulary and about the TRANSACTION, not about the proof:

    NoSeizeWdrl hp ctx  :=  credentialInWithdrawals hp.seizeLogicCred
                              ctx.scriptContextTxInfo.txInfoWdrl = false

i.e. *the deployment's seize credential does not appear in this transaction's
withdrawal map* — literally "this transaction does not run the seize validator".
That is the sentence the naive reading attributed to SHAPE T1R for free; it now
has to be said, and it is said where a reader can see it.

**WHY THIS IS NOT ASSUMING THE CONCLUSION.** `NoSeizeWdrl` is a decidable fact
about the withdrawal map alone. It says nothing about value flow, about outputs,
or about what any validator computes; it cannot be used to prove containment of
anything. What it does is make the `p2` leaf's hypotheses CONTRADICTORY, via the
ledger rule and nothing else (§10.1). And it does not empty the class: §10.4
re-certifies the same node-realizable SHAPE-T1R witness in the refined class
(`SEIZE ∉ {GLOBAL, TLS}` at `witnessParams`), so §10.3's composed result is a
statement about a class that still contains a transaction the real compiled
bytecode accepts in 2,603 CEK steps.

**THE HONEST SCORECARD, which is the point of the exercise (§10.3).** Over
`T1RShapeNS` the `LeafSet` is complete — **N = 0**, no leaf hypothesis at all —
and it is complete in this ratio:

| leaf | discharged BY | acceptance hypothesis used? |
|---|---|---|
| `p1` | **THE BYTECODE** — `WSC.P1R_T1`, production `programmableLogicGlobal` @ 4400 | **YES** (`NodeAcceptsGlobal`) |
| `p4` | the SHAPE (T1R mints nothing) | no — bound as `_` |
| `p2` | the SHAPE + the LEDGER RULE (no seize withdrawal ⟹ the seize validator cannot run) | no — bound as `_` |
| `nopre` | the SHAPE (T1R's outputs carry `NoOutputDatum`) | — |

**ONE of four leaves is the bytecode; three are the shape.** Removing the last
leaf HYPOTHESIS did not make the composition say more about the validators — it
made explicit that, in a pure-transfer class, three of the four obligations are
about things the class does not do. Quote the ratio, never just "N = 0". -/

/-- **The added conjunct**: this transaction's withdrawal map does not mention the
deployment's seize credential. Ground truth — CLAB's own `credentialInWithdrawals`
over `TxInfo`, the same function `validScriptInfo`'s rewarding clause uses. -/
def NoSeizeWdrl (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = false

/-! ### §10.1 The ledger rule that discharges `p2`

`CardanoLedgerApi/V3/Contexts.lean:1014` — `validScriptInfo`'s `RewardingScript`
clause is

    V2.isScriptCredential cred && credentialInWithdrawals cred txInfoWdrl

transcribing Conway's rewarding `scriptsNeeded`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/UTxO.hs:375-384`): a rewarding script
runs **only** for a credential the transaction actually withdraws at. So for a
transaction with no seize withdrawal, `WSC.LR_CTX` at the re-purposed context
`ctx'` is already a contradiction — the node cannot have run the seize validator
on it. NOTE that this consumes `WSC.OnChain ctx'`, the hypothesis task A2 added to
the field precisely so a shaped discharge could pin `ctx'`; without it the leaf
would still be open. -/

/-- **`LeafSet.p2` for ANY class that has no seize withdrawal.** Stated over an
arbitrary `Shape` so the argument is reusable and so it is visible that it uses
NOTHING about SHAPE T1R except the one conjunct.

**THE ACCEPTANCE HYPOTHESIS IS UNUSED AND IS BOUND AS `_`.** `WSC.NodeAcceptsSeize`
does no work here and neither does the compiled `programmableSeize` bytecode: the
leaf is discharged because its hypotheses cannot all hold, and a reader must not
read this as the seize validator having been verified. -/
theorem p2_of_noSeizeWdrl (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (hns : ∀ ctx, Shape ctx → NoSeizeWdrl hp ctx) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
      WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
        Composition.Contain hp.progLogicCred cs tn ctx := by
  intro ctx ctx' cs tn _hdep _hoc hsh _hbud hsame hoc' hsi _hacc _hcs
  exfalso
  -- the ledger verdict at the RE-PURPOSED context
  have hvsc : validScriptContext ctx' = true := WSC.LR_CTX ctx' hoc'
  have hvsi : validScriptInfo ctx' = true := by
    simp only [validScriptContext, Bool.and_eq_true] at hvsc; exact hvsc.1
  -- its rewarding clause: the seize credential must be withdrawn at
  have hin : credentialInWithdrawals hp.seizeLogicCred
      ctx'.scriptContextTxInfo.txInfoWdrl = true := by
    rw [validScriptInfo, hsi] at hvsi
    simp only [Bool.and_eq_true] at hvsi
    exact hvsi.2.2
  -- but the class says it is not
  have := hns ctx hsh
  rw [Composition.SameTx] at hsame
  rw [hsame] at hin
  rw [NoSeizeWdrl] at this
  rw [this] at hin
  exact Bool.noConfusion hin

/-! ### §10.2 The refined class -/

/-- **SHAPE T1R, seize-free** — `T1RShape` (§2) plus the one conjunct §10 names.
Every field of the `LeafSet` is now a theorem. -/
def T1RShapeNS (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  T1RShape hp ctx ∧ NoSeizeWdrl hp ctx

/-- `p1` at the refined class — verbatim §4's bytecode discharge, applied to the
first component. Nothing is re-proved and nothing is weakened: `T1RShapeNS` is a
SUB-class of `T1RShape`, so every theorem of §4-§5 applies unchanged. -/
theorem shapedGlobalContainment_T1RNS (hp : WSC.HonestParams) :
    Composition.ShapedGlobalContainment hp (T1RShapeNS hp) :=
  ⟨fun ctx ctx' cs tn hoc hsh hbud hsame hoc' hsi hacc hcs hraw =>
    (shapedGlobalContainment_T1R hp).contain ctx ctx' cs tn hoc hsh.1 hbud hsame hoc'
      hsi hacc hcs hraw⟩

/-- **THE COMPLETE `LeafSet` — no leaf hypothesis (audit F1: N = 0).**

Read the ratio in §10's table with it: `p1` is the production bytecode with its
acceptance hypothesis consumed; `p4`, `p2` and `nopre` are the shape, with their
acceptance hypotheses unused and bound as `_`. -/
theorem realizableLeavesNS (hp : WSC.HonestParams) :
    Composition.LeafSet hp (T1RShapeNS hp) :=
  { p4 := fun ctx ctx' cs mlh hdep hoc hsh hbud hsame hoc' hsi hacc hcsa =>
            p4_on_T1RShape hp ctx ctx' cs mlh hdep hoc hsh.1 hbud hsame hoc' hsi hacc hcsa
  , p1 := Composition.leafP1_of_shapedGlobalContainment hp (T1RShapeNS hp)
            (shapedGlobalContainment_T1RNS hp)
  , p2 := p2_of_noSeizeWdrl hp (T1RShapeNS hp) (fun _ h => h.2)
  , nopre := fun L ctx L' cs tn hdep hstep htx hreg hnew =>
            nopre_on_T1RShape hp L ctx L' cs tn hdep hstep
              ⟨htx.1, htx.2.1, htx.2.2.1⟩ hreg hnew }

/-! ### §10.3 THE COMPOSED RESULT WITH NO LEAF ASSUMPTION

The same two statements as §7, with the `p2` parameter GONE. Everything else in
§7's "BUDGETS AND SHAPE" stanza still applies verbatim, and one line is added to
it: every transaction of the class has no seize withdrawal. -/

/-- **THE TOP CLAIM OVER A NON-EMPTY SHAPE CLASS, ON NO LEAF ASSUMPTION.**
*Along any trace of honest seize-free SHAPE-T1R transactions from genesis, no UTxO
outside the mini-ledger holds a registered programmable token.* One of the four
leaves is the production bytecode; three are the shape (§10). Still bounded by
`K_global = 4400` and by a fixed `Data` skeleton; still 28 project axioms plus
`sorryAx`; still no coverage argument. -/
theorem containment_on_realizable_class (hp : WSC.HonestParams)
    (hdep : WSC.Deployed hp) :
    ∀ (L : Composition.Ledger), Composition.Reachable hp (T1RShapeNS hp) L →
      Composition.I hp L :=
  Composition.top_claim hp (T1RShapeNS hp) (realizableLeavesNS hp)
    (fun ctx h => t1RShape_wdrlPair hp ctx h.1) hdep

/-- The plain-English form, likewise with no leaf assumption. -/
theorem no_tokens_outside_mini_ledger_on_realizable_class
    (hp : WSC.HonestParams) (hdep : WSC.Deployed hp)
    (L : Composition.Ledger) (hR : Composition.Reachable hp (T1RShapeNS hp) L)
    (cs : CurrencySymbol) (tn : TokenName)
    (hcs : cs ≠ adaSymbol) (hreg : Composition.RegisteredIn hp L cs) :
    ∀ u ∈ L, WSC.payCred u.utxoOut ≠ hp.progLogicCred →
      valueOf cs tn u.utxoOut.txOutValue = (0:Int) :=
  Composition.no_programmable_tokens_outside_mini_ledger hp (T1RShapeNS hp)
    (realizableLeavesNS hp) (fun ctx h => t1RShape_wdrlPair hp ctx h.1) hdep
    L hR cs tn hcs hreg

/-! ### §10.4 THE REFINED CLASS IS STILL NOT EMPTY

A refinement that emptied the class would be worthless (audit §4c, and
`ShapeRealizability.t1_class_is_empty` is what that failure looks like). It does
not: `witnessParams`' seize credential is `SEIZE` and the witness withdraws at
`GLOBAL` and `TLS`. -/

/-- The witness has no seize withdrawal — by computation on its own withdrawal
map. -/
theorem witness_noSeizeWdrl : NoSeizeWdrl witnessParams WSC.P1RShapedWitness.ctxOk := by
  rw [NoSeizeWdrl]; rfl

/-- **THE REFINED CLASS IS INHABITED, BY THE SAME CERTIFIED WITNESS.** -/
theorem t1RShapeNS_witness : T1RShapeNS witnessParams WSC.P1RShapedWitness.ctxOk :=
  ⟨t1RShape_witness, witness_noSeizeWdrl⟩

/-- **AND THE INHABITANT IS STILL NODE-REALIZABLE** — ledger-valid, redeemer-exact
under the Conway rule, and accepted by the production bytecode in 2,603 steps. -/
theorem realizable_inhabitant_NS :
    T1RShapeNS witnessParams WSC.P1RShapedWitness.ctxOk
    ∧ CardanoLedgerApi.V3.validRewardingContext WSC.P1RShapedWitness.ctxOk = true
    ∧ CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus
        WSC.P1RShapedWitness.ctxOk.scriptContextTxInfo = true :=
  ⟨t1RShapeNS_witness, WSC.t1R_realizable.1, WSC.t1R_realizable.2.1⟩

/-! ## §9 AXIOM AUDIT, printed at build time -/

#print axioms bridge_T1R
#print axioms exec_T1R
#print axioms shapedGlobalContainment_T1R
#print axioms p4_on_T1RShape
#print axioms nopre_on_T1RShape
#print axioms realizableLeaves
#print axioms containment_on_realizable_class_of_p2
#print axioms no_tokens_outside_mini_ledger_on_realizable_class_of_p2
#print axioms t1RShape_witness
#print axioms realizable_inhabitant

/-! ### §9.1 The E1 results (§10) — the same audit, printed the same way.

`p2_on_T1RShapeNS` is the ONE to read first: no `sorryAx`, no `native_decide`,
and its project axioms are exactly the two the ledger step needs
(`WSC.LR_CTX`, and `WSC.OnChain`/`WSC.Deployed` from the field's own signature).
The composed results' axiom set is IDENTICAL to §7's — closing `p2` cost nothing
in trust base, because the discharge is a ledger rule the library already
assumes. -/

#print axioms p2_of_noSeizeWdrl
#print axioms shapedGlobalContainment_T1RNS
#print axioms realizableLeavesNS
#print axioms containment_on_realizable_class
#print axioms no_tokens_outside_mini_ledger_on_realizable_class
#print axioms witness_noSeizeWdrl
#print axioms t1RShapeNS_witness
#print axioms realizable_inhabitant_NS

end RealizableLeaves
end WSC
