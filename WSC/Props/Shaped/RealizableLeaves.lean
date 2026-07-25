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

/-! ## §3 The two vocabulary lemmas

Both are ordinary Lean; neither uses a solver, `native_decide` or any axiom. -/

/-- `Composition.coveringRaw` and `WSC.Model.coveringNodeExists` are the SAME
function — the composition restates it locally to avoid an import. Proved rather
than assumed, because `WSC.P1R_T1`'s exemption hypothesis is in the second
vocabulary and `ShapedGlobalContainment`'s is in the first. -/
theorem coveringRaw_eq_coveringNodeExists (dirCS cs : CurrencySymbol) (is : List TxInInfo) :
    Composition.coveringRaw dirCS cs is = WSC.Model.coveringNodeExists dirCS cs is := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
      rw [Composition.coveringRaw, WSC.Model.coveringNodeExists, ih]
      rfl

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
5. `WSC.P1R_T1` — `✅ Valid`, budget 4400, witness K = 2603 — gives the containment
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
    rw [← coveringRaw_eq_coveringNodeExists, ← hEq]; exact hraw
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
CEK steps. The accepting witness costs **K = 2603** steps.

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
  Composition.top_claim hp (T1RShape hp) (realizableLeaves hp hp2) hdep

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
    (realizableLeaves hp hp2) hdep L hR cs tn hcs hreg

/-! ## §8 THE CLASS IS NOT EMPTY — the whole point

`ShapeRealizability.t1_class_is_empty` proves that the PRE-re-cut SHAPE T1 class is
empty, unconditionally, and `t1_no_honest_step` proves the corresponding top claim
carries no information. This section is the exact opposite statement for the re-cut
shape, and it is what makes §7 worth stating at all.

`witnessParams` is a coherent honest deployment read off the witness's own leaves:
base credential `PROGLOGIC`, global logic `GLOBAL`, seize logic `SEIZE`, directory
policy `DIRCS`. `WSC.t1R_realizable` (task C1) independently certifies that the same
context satisfies `validRewardingContext`, satisfies **both** halves of Conway's
`hasExactSetOfRedeemers` (`redeemersExact`), is redeemer-covered, and is ACCEPTED by
the real compiled bytecode. -/

/-- A deployment whose parameters are the witness's own leaves. -/
def witnessParams : WSC.HonestParams :=
  { protocolParamsCS := P1ShapedWitness.ppCS
  , directoryNodeCS := ByteString.mk "DIRCS"
  , progLogicCred := .ScriptCredential (ByteString.mk "PROGLOGIC")
  , globalLogicCred := .ScriptCredential (ByteString.mk "GLOBAL")
  , seizeLogicCred := .ScriptCredential (ByteString.mk "SEIZE") }

/-- **THE CLASS IS INHABITED.** `WSC.P1RShapedWitness.ctxOk` — the SHAPE-T1R
accepting witness whose real-CEK cost is 2603 steps — is a member of the very class
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
    ∧ CardanoLedgerApi.V3.Contexts.redeemersExact
        WSC.P1RShapedWitness.ctxOk.scriptContextTxInfo = true :=
  ⟨t1RShape_witness, WSC.t1R_realizable.1, WSC.t1R_realizable.2.1⟩

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

end RealizableLeaves
end WSC
