-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/P5Shaped.lean — **P5, the ESCAPE-CRITICAL property, PROVED at
UPLC level against the real compiled transfer bytecode, over SHAPE G1**
(task Z2 rung 4).

════════════════════════════════════════════════════════════════════════════
⚠ SHAPE-CLASS STATUS (task C1) — READ BEFORE COMPOSING ANYTHING FROM THIS FILE
════════════════════════════════════════════════════════════════════════════
Every theorem below is TRUE and unchanged. But SHAPE G1's class is **EMPTY as a
class of ledger transactions** under Conway UTXOW's `MissingRedeemers` rule —
its withdrawal entry 1 is a script credential with no `Rewarding` redeemer entry
(`WSC.ShapeRealizability.g1_class_is_empty_under_coverage`). **Use
`WSC/Props/Shaped/P5ShapedR.lean` instead**: the same statement
(`P5R_shaped_indexed`, `P5R_shaped_exists`, `P5R_shaped_groundtruth`), same
budget 1600, same witness K = 1541, over the re-cut SHAPE G1R whose class is
proved NON-EMPTY (`WSC.g1R_realizable`).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED
════════════════════════════════════════════════════════════════════════════
`WSC/Props/P5_NonMember.lean`'s "OBLIGATION STATUS" block records the bytecode
obligation over a FULLY SYMBOLIC `ScriptContext` at budget 1600 as **killed at
5,241 s ≈ 87 min with NO verdict**, and its mandatory vacuity probe likewise. The
same obligation over SHAPE G1 — same flat, same budget 1600, same postcondition —
is **Valid in ≈2 s**, with its vacuity probe Falsified at the same shape. Full
ladder in WSC/SHAPING-RESULTS.md.

Everything ABOVE the bytecode step was already proved in
`WSC/Props/P5_NonMember.lean` (`nthFrom_mem`, `coversCS_elim`,
`hasCoveringNode_of_mem`, `authenticDirNode_of_authH`, `dirNodeKeyRaw_of_datum`,
`P5_exists_of_indexed`, `P5_groundtruth_of_indexed`). This module supplies the
missing rung and then composes: `P5_shaped_exists` below is ADDENDUM E3's ∃-form
postcondition, and `P5_shaped_groundtruth` is the same statement in
WSC/Honest.lean's vocabulary.

════════════════════════════════════════════════════════════════════════════
SCOPE — THREE BOUNDS, ALL BINDING
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 1600** (ADDENDUM E1). Bridged to node acceptance by
`LR_BUDGET_global`.

**Bound 2 — SHAPE G1.** Published in full in WSC/Shaped/GlobalShaped.lean's
header. In one line: one non-mini-ledger ada-only input, exactly two reference
inputs (params node then candidate directory node), one non-mini-ledger output,
a one-policy/one-token mint, a 2-entry all-script withdrawal map, one redeemer
entry, empty cert/signatory/datum/vote/proposal lists, and the redeemer fixed to
`TransferAct [] [] [NonMember 1] 0`.

**Bound 2b — ONE NODE INDEX AT A TIME.** SHAPE G1 pins the `NonMember` node index
to 1. Freeing it (SHAPE G3, `WSC/Shaped/GlobalShapedIdx.lean`) with the index-free
`hasCoveringNode` postcondition returns **`Undetermined` after a 906 s Z3 query**,
while the vacuity probe at that shape is `Falsified` — so the class is non-empty
and this is a solver limit, not an empty shape (`WSC/SHAPING-RESULTS.md` §6.2).
The symbolic `dropList` at ProgrammableLogicBase.hs:998 puts the branch structure
back into the residual. Contrast the issuance policy, where the analogous
loosening (SHAPE M2) closes in 2.1 s. Enumerating the index range as separate
shapes would close this gap mechanically; it was not done.

**Bound 3 — P5's strength is DirWF's strength** (ADDENDUM E4, unchanged). What is
proved is the covering-node WITNESS; turning it into "`cs` is not registered" is
the composition-layer lemma `covering_node_excludes_registration`, which consumes
`DIRWF` (ii)/(iii) and `TS4`. Those remain ASSUMED (WSC/Honest.lean); discharging
them is deferred unit U10.

**NEITHER HALF OF THE POSTCONDITION IS SMUGGLED INTO THE SHAPE** — this is the
design point of SHAPE G1 and the reason it is not the golden's shape:
* `coversCS cs node` = `key < cs && cs < next` with `key`, `next`, `cs` three free
  variables;
* `dirNodeAuthH dirCS node` = `nCS == dirCS`, where `nCS` (the directory node's
  first non-ada value policy) and `dirCS` (the directory policy published by the
  params datum at reference index 0) are DIFFERENT free variables. A shape that
  reused one variable for both would have made this conjunct true by construction.
Likewise `pCS ≠ ppCS` as variables, so `pparamsAtRefIdx`'s own `phasCSH` gate
(ProgrammableLogicBase.hs:832) is not pre-satisfied either.

**FINDING — the golden is NOT P5's subject shape** (recorded in
WSC/SHAPING-RESULTS.md and in WSC/Shaped/GlobalShaped.lean's header). The vector
`programmableLogicGlobal.transfer-nonmember-covering-node` has redeemer
`d8799f9f01ff9f01ff8000ff` = `TransferAct [1] [1] [] 0`, i.e. an EMPTY mint-proof
list: its covering-node check happens in the INPUT-side transfer walk
(ProgrammableLogicBase.hs:889-900), and with an empty mint the validator never
even calls the mint walk (:1219-1222) that `nonMemberNodeIdxOf` mirrors. So the
claim in WSC/Prep/Global1600.lean and WSC/STATUS.md that this golden "is exactly
P5's subject shape" is too strong: it witnesses accept-within-1600, not
satisfiability of P5's hypotheses. SHAPE G1's concrete instance below is the
first witness that does both, and it satisfies `validRewardingContext` with ZERO
failing conjuncts. (When this was written no golden did — defect D3. Task Z5 has
since fixed the upstream builder and CLOSED D3, so the accepting goldens now
qualify too; the mint-side point above is unaffected, because no golden exercises
the mint walk's `PNonMember` branch at all.)

════════════════════════════════════════════════════════════════════════════
PRECONDITION AUDIT (arch §4.1)
════════════════════════════════════════════════════════════════════════════
MAY assume, and does: `validRewardingContext (globalShapedCtx …)` — CLAB ledger
normalization only, specialized to the shape. It never inspects the redeemer's
CONTENT (CardanoLedgerApi/V3/Contexts.lean:1197-1246).

MUST NOT assume, and does not: nothing about the reference inputs being
authentic, nothing about the node datum being well formed beyond being an inline
`DirectorySetNode`-shaped list with FREE key/next, nothing about the covering
interval, no `HonestParams`/`Deployed`/`OnChain`/DirWF hypothesis in the bytecode
theorem (they appear only in the clearly-labelled ground-truth corollary).

The `§P5 hypothesis audit` section below proves, by `rfl`/`decide`, that SHAPE G1
really does satisfy every hypothesis of `P5_nonmember_covering_node_indexed` with
`pIdx = 0`, `nodeIdx = 1`, `paramsIn` = reference input 0 and `node` = reference
input 1 — so the theorem here is that statement specialized to the shape, not a
different (weaker) statement.
-/
import WSC.Shaped.GlobalShaped
import WSC.Prep.Global
import WSC.Props.P5_NonMember
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
open P5

/-! ## §P5 hypothesis audit — SHAPE G1 satisfies P5's indexed hypotheses

Each lemma below discharges one hypothesis of
`WSC.P5_nonmember_covering_node_indexed` at the shape, for ALL leaf values. Taken
together they are what licenses reading `P5_shaped_indexed` as "P5's indexed
obligation, specialized to SHAPE G1". -/

/-- The shaped redeemer's `paramsRefIdx` is 0 (concrete: a self-validating hint,
re-checked by `pparamsAtRefIdx`'s `phasCSH` gate). -/
theorem shape_paramsRefIdx : transferParamsRefIdx globalShapedRedeemer = some 0 := by
  native_decide

/-- The shaped redeemer's mint-proof list is exactly one `NonMember 1`. -/
theorem shape_mintProofs :
    transferMintProofs globalShapedRedeemer = some [MintProof.NonMember 1] := rfl

section Leaves
variable (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
         (dest : ByteString) (outAda qOut : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer) (fee : Integer)

private abbrev shCtx : ScriptContext :=
  globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
    dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee

private abbrev shNode : TxInInfo :=
  globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS

private abbrev shParamsIn : TxInInfo :=
  globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc

/-- Reference index 0 of the shape is the protocol-params node. -/
theorem shape_refIdx0 :
    nthFrom (shCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs 0
      = some (shParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc) := rfl

/-- Reference index 1 of the shape is the candidate directory node. -/
theorem shape_refIdx1 :
    nthFrom (shCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs 1
      = some (shNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS) := rfl

/-- The directory policy the params datum publishes at reference index 0 is
`dirCS` — read exactly as the bytecode reads it (position 0 of an inline
`Data.List` datum, `punsafeCoerce`d: ProgrammableLogicBase.hs:834-836). -/
theorem shape_paramsDirCS :
    paramsDatumDirCSRaw
      (shParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc).txInInfoResolved = some dirCS := rfl

/-- The shape positionally classifies `cs` as `NonMember` with node index 1
(ADDENDUM E8: `mintProofFor` walks the proof list in lockstep with the sorted
`txInfoMint` entries, and the shape has exactly one mint entry, for `cs`). -/
theorem shape_nonMemberNodeIdx :
    nonMemberNodeIdxOf cs
      (shCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee) = some 1 := by
  unfold nonMemberNodeIdxOf
  rw [show (shCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 fee).scriptContextRedeemer = globalShapedRedeemer from rfl,
      shape_mintProofs]
  simp [globalShapedCtx, Shape.mintOne, mintProofFor]

end Leaves

/-! ## The bytecode obligation — PROVED -/

/-- **P5 (escape-critical), indexed form, over SHAPE G1 — PROVED AT UPLC.**

*If the real compiled transfer validator accepts a shape-G1 transaction — in
which the redeemer positionally classifies the minted policy `cs` as `NonMember`
with node index 1 — then the reference input at index 1 really is authenticated
as a directory node of the policy `dirCS` that the validator itself read out of
the params datum at reference index 0, and its `(key, next)` interval strictly
covers `cs`.*

The two conclusions are, verbatim, the three `pand'List` conditions of the mint
walk's `PNonMember` branch (ProgrammableLogicBase.hs:1009-1011): `coversCS` is
`nodeKey #< currCS` ∧ `currCS #< nodeNext`, `dirNodeAuthH` is `phasCSH`.

MEASURED: `✅ Valid` (≈2 s). The same obligation over a fully symbolic context
returned no verdict in 87 minutes (WSC/Props/P5_NonMember.lean). -/
theorem P5_shaped_indexed :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      dirNodeAuthH dirCS
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      := by blaster (timeout: 1500)

/-! ## Composition with the already-proved reduction ladder -/

/-- **ADDENDUM E3's ∃-form postcondition, at UPLC, over SHAPE G1.** Obtained by
feeding `P5_shaped_indexed` into `P5_exists_of_indexed`
(WSC/Props/P5_NonMember.lean, proved there) with the index witness
`shape_refIdx1`. This is the statement the composition layer's
`covering_node_excludes_registration` consumes. -/
theorem P5_shaped_exists
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (fee : Integer)
    (hv : validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee))
    (ha : isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) :
    ∃ t ∈ (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
             dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
             w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs,
      dirNodeAuthH dirCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKeyRaw t.txInInfoResolved = some k ∧
             dirNodeNextRaw t.txInInfoResolved = some n ∧ k < cs ∧ cs < n := by
  obtain ⟨hauth, hcov⟩ :=
    P5_shaped_indexed ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee hv ha
  exact P5_exists_of_indexed dirCS cs _ _ 1
    (shape_refIdx1 cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
    hauth hcov

/-- **Ground-truth restatement, at UPLC, over SHAPE G1.** Same conclusion in
WSC/Honest.lean's vocabulary (`authenticDirNode` = ground-truth directory-token
membership; `dirNodeKey`/`dirNodeNext` = the FULL 5-field `DirectorySetNode`
decode), obtained by feeding `P5_shaped_indexed` into the already-proved
`P5_groundtruth_of_indexed`. Consumes exactly one assumption beyond the bytecode:
`TS3` (the node datum decodes as a well-formed `DirectorySetNode`), which cannot
come from this validator because it `punsafeCoerce`s the datum and reads only
positions 0/1. -/
theorem P5_shaped_groundtruth
    (hp0 : HonestParams) (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (fee : Integer)
    (hdep : Deployed hp0)
    (hoc : OnChain
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee))
    (hv : validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee))
    (ha : isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee)) :
    ∃ t ∈ (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
             hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
             w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp0.directoryNodeCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKey t.txInInfoResolved = some k ∧
             dirNodeNext t.txInInfoResolved = some n ∧ k < cs ∧ cs < n := by
  obtain ⟨hauth, hcov⟩ :=
    P5_shaped_indexed ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 w1 a0 a1 fee hv ha
  exact P5_groundtruth_of_indexed hp0 cs _ _ 1 hdep hoc
    (shape_refIdx1 cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 w1 a0 a1 fee)
    hauth hcov

/-! ## Polarity controls (ADDENDUM E9) — the full control set -/

/-- Negative control: a shape-G1 context whose node at the claimed index FAILS
either the directory authentication or the covering interval is REJECTED by the
bytecode. MEASURED: `✅ Valid`.

NOTE (E9, binding): a negative control is also satisfied by budget-`Error`, so it
cannot detect the 1600-step bound by itself; the vacuity probe and the concrete
witness below are what do. -/
theorem P5_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(dirNodeAuthH dirCS
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true) →
    isUnsuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      := by blaster (timeout: 1500)

/-- Tightness stanza: the NEGATION of P5's postcondition under an accepting run
must be FALSIFIABLE. Expected and MEASURED: `Falsified`. -/
def P5_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬(dirNodeAuthH dirCS
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P5_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT THE SHAPE.** "No accepting shape-G1 context
exists within 1600 CEK steps" must be FALSIFIED.

Expected and MEASURED: `Falsified`. Contrast the same probe over a fully symbolic
context, which was killed after 5,241 s with no verdict
(WSC/Props/P5_NonMember.lean `P5_vacuity_probe_1600`), and the budget-600 probe in
WSC/Prep/Global.lean, which is `Valid` (= genuinely vacuous). The concrete witness
below discharges the obligation a second time without the solver. -/
def P5_shaped_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P5_shaped_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE G1 — executable, no SMT

The strongest non-vacuity evidence available for this property, and the first one
in the repository that is simultaneously
(a) a genuine MINT-side `NonMember` claim (which the golden is not — see the
    FINDING in this module's header),
(b) fully `validRewardingContext`-normalized with ZERO failing conjuncts, and
(c) accepted by the REAL compiled bytecode inside the 1600-step budget.

Leaf values: a policy `MMM` is minted (7 of `MMM.TOK`, strictly POSITIVE — the
escape the property is about) and claimed exempt via `NonMember 1`; reference
input 1 is a directory node whose datum has `key = AAA`, `next = ZZZ` (so
`AAA < MMM < ZZZ`) and whose first non-ada value policy is `DIRCS`; reference
input 0 is the params node whose datum publishes `directoryNodeCS = DIRCS` and
whose first non-ada value policy is `PARAMS` = the script parameter. 200 lovelace
in, 150 out, 50 fee; the minted 7 tokens land at a pubkey output. -/

namespace P5ShapedWitness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE G1 at the leaf values described above. -/
def ctx : ScriptContext :=
  globalShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "DEST") 150 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis IN FULL.
(`WSC/Shaped/Probe/G1Witness.lean` additionally evaluates CLAB's per-conjunct
report on it and gets the empty list of failures.) -/
theorem ctx_valid : validRewardingContext ctx = true := by native_decide

/-- The witness satisfies P5's postcondition: the node is authenticated against
the params datum's `dirCS`, and its interval strictly covers the minted policy. -/
theorem ctx_post :
    dirNodeAuthH (ByteString.mk "DIRCS")
        (globalShapedNode (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS")
          (ByteString.mk "NODETOK") 100 1 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
          (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS")).txInInfoResolved = true
    ∧ coversCS (ByteString.mk "MMM")
        (globalShapedNode (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS")
          (ByteString.mk "NODETOK") 100 1 (ByteString.mk "AAA") (ByteString.mk "ZZZ")
          (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS")).txInInfoResolved = true
      := by native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-G1
context at budget 1600, through the SHAPED applied term the theorems above
quantify over. -/
theorem exec_accepts_at_1600 :
    isSuccessful
      (appliedGlobalShaped1600.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "DEST") 150 7
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- …and the UNSHAPED 1600 prep's executable term accepts the same context, so
the shaped and unshaped applied terms agree on it. -/
theorem exec_accepts_at_1600_unshaped :
    isSuccessful (appliedGlobal1600.exec ppCS ctx) :=
  isHaltB_sound _ (by native_decide)

/-- Lower bracket: REJECTED at budget 600 (budget exhaustion ⟹ `Error`). -/
theorem exec_rejects_at_600 :
    isHaltB (appliedGlobal.exec ppCS ctx) = false := by native_decide

/-- **EXACT STEP COUNT.** `K = 1541` for this witness: it halts at 1541 and
budget-errors at 1540. (Measured by binary search in
`WSC/Shaped/Probe/G1K.lean`; pinned here as a theorem.) For comparison, the
cheapest accepting golden of this validator is K = 1554
(WSC/goldens/K-MEASUREMENTS.md §3) — so SHAPE G1 sits in the same step-count
regime as the real off-chain transaction while being a genuine mint-side
`NonMember`. -/
theorem K_is_1541 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 1541) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 1540) = false := by native_decide

end P5ShapedWitness

end WSC
