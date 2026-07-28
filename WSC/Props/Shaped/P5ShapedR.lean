-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/P5ShapedR.lean — **P5 (escape-critical) re-proved over the
NODE-REALIZABLE re-cut SHAPE G1R** (task C1).

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/P5Shaped.lean` proves P5 over SHAPE G1. That theorem is TRUE
and unchanged — but `WSC/Props/Shaped/ShapeRealizability.lean`'s
`g1_class_is_empty_under_coverage` proves SHAPE G1's class is EMPTY as a class of
ledger transactions (its withdrawal entry 1 is a script credential with no
`Rewarding` redeemer entry, which Conway's `MissingRedeemers` forbids), so P5
over SHAPE G1 cannot be composed through a `Shape` restriction.

This module re-states and re-proves the SAME obligation over SHAPE G1R
(WSC/Shaped/GlobalShapedR.lean §1), whose redeemer map covers every script
witness the transaction needs, and whose class is proved NON-EMPTY in
`WSC/Props/Shaped/GlobalRealizability.lean` (`g1R_realizable`, plus
`g1R_class_covered` for the whole class).

WHAT CHANGED FROM SHAPE G1, EXHAUSTIVELY:
* the withdrawal map is ONE entry (`ScriptCredential w0`, the validator's own
  rewarding credential) instead of two — the second entry was never dereferenced,
  because SHAPE G1's redeemer has `transferWdrlIdxs = []`;
* the redeemer map is TWO entries, `[(Minting cs, I rMint), (Rewarding w0, red)]`
  instead of one — the `Minting` entry is the needed script of the mint field;
* the parameters `w1`, `a1` are gone and `rMint` is added.
NOTHING ELSE. The reference inputs, the mint, the input, the output, the
redeemer content, the budget (1600) and the postcondition are identical, and the
two "not smuggled into the shape" facts from P5Shaped's header still hold
verbatim: `key`/`next`/`cs` are three free variables and `nCS` ≠ `dirCS` as
variables.

SCOPE. All three bounds of `WSC/Props/Shaped/P5Shaped.lean` (budget 1600 via
`LR_BUDGET_global`; one shape; one pinned node index; P5's strength is DirWF's
strength) apply here word for word. This module adds nothing to the trust
surface and removes nothing from it — its whole content is that the class the
theorem quantifies over is inhabited by transactions a node would accept.

MEASURED (this task): `✅ Valid`; witness K = 1541 (unchanged from SHAPE G1 —
the redeemer map is not dereferenced by this validator, so the re-cut costs
nothing in CEK steps), budget 1600, headroom 59.
-/
import WSC.Shaped.GlobalShapedRPrep
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

/-! ## §1 Hypothesis audit — SHAPE G1R satisfies P5's indexed hypotheses

The same four lemmas as `WSC/Props/Shaped/P5Shaped.lean`'s audit section, at the
re-cut shape. `shape_paramsRefIdx` and `shape_mintProofs` are about the redeemer
alone and are reused from there unchanged. -/

/-- The shaped redeemer's `paramsRefIdx` is 0 and its mint-proof list is exactly
one `NonMember 1` — the redeemer is SHAPE G1's `globalShapedRedeemer` unchanged,
so these are the same two facts `WSC.shape_paramsRefIdx` / `WSC.shape_mintProofs`
record, restated here so this module does not have to import P5Shaped. -/
theorem shapeR_paramsRefIdx : transferParamsRefIdx globalShapedRedeemer = some 0 := by
  native_decide

theorem shapeR_mintProofs :
    transferMintProofs globalShapedRedeemer = some [MintProof.NonMember 1] := rfl

section Leaves
variable (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
         (dest : ByteString) (outAda qOut : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 : ByteString) (a0 rMint : Integer) (fee : Integer)

private abbrev shRCtx : ScriptContext :=
  globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
    dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee

/-- Reference index 0 of the re-cut shape is the protocol-params node. -/
theorem shapeR_refIdx0 :
    nthFrom (shRCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 a0 rMint fee).scriptContextTxInfo.txInfoReferenceInputs 0
      = some (globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc) := rfl

/-- Reference index 1 of the re-cut shape is the candidate directory node. -/
theorem shapeR_refIdx1 :
    nthFrom (shRCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 a0 rMint fee).scriptContextTxInfo.txInfoReferenceInputs 1
      = some (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS) := rfl

/-- The re-cut shape positionally classifies `cs` as `NonMember` with node index
1 (ADDENDUM E8: one mint entry, one proof, walked in lockstep). -/
theorem shapeR_nonMemberNodeIdx :
    nonMemberNodeIdxOf cs
      (shRCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 a0 rMint fee) = some 1 := by
  unfold nonMemberNodeIdxOf
  rw [show (shRCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
              dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 a0 rMint fee).scriptContextRedeemer = globalShapedRedeemer from rfl,
      shapeR_mintProofs]
  simp [globalRShapedCtx, Shape.mintOne, mintProofFor]

end Leaves

/-! ## §2 The bytecode obligation — RE-PROVED over the realizable shape -/

/-- **P5 (escape-critical), indexed form, over the REALIZABLE SHAPE G1R —
PROVED AT UPLC.**

*If the real compiled transfer validator accepts a shape-G1R transaction — in
which the redeemer positionally classifies the minted policy `cs` as `NonMember`
with node index 1 — then the reference input at index 1 really is authenticated
as a directory node of the policy `dirCS` that the validator itself read out of
the params datum at reference index 0, and its `(key, next)` interval strictly
covers `cs`.*

Identical statement to `WSC.P5_shaped_indexed`, over a shape whose class is
inhabited by node-acceptable transactions (`WSC.g1R_realizable`).

MEASURED: `✅ Valid`. -/
theorem P5R_shaped_indexed :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) →
    isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee) →
      dirNodeAuthH dirCS
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
          (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      := by blaster (timeout: 1500)

/-! ## §3 Composition with the already-proved reduction ladder -/

/-- **ADDENDUM E3's ∃-form postcondition, at UPLC, over the REALIZABLE SHAPE
G1R.** Same derivation as `WSC.P5_shaped_exists`, via `P5_exists_of_indexed`
with the index witness `shapeR_refIdx1`. -/
theorem P5R_shaped_exists
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer) (fee : Integer)
    (hv : validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee))
    (ha : isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee)) :
    ∃ t ∈ (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
             dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
             w0 a0 rMint fee).scriptContextTxInfo.txInfoReferenceInputs,
      dirNodeAuthH dirCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKeyRaw t.txInInfoResolved = some k ∧
             dirNodeNextRaw t.txInInfoResolved = some n ∧ k < cs ∧ cs < n := by
  obtain ⟨hauth, hcov⟩ :=
    P5R_shaped_indexed ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee hv ha
  exact P5_exists_of_indexed dirCS cs _ _ 1
    (shapeR_refIdx1 cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee)
    hauth hcov

/-- **Ground-truth restatement over the REALIZABLE SHAPE G1R.** Same conclusion
in WSC/Honest.lean's vocabulary, via the already-proved
`P5_groundtruth_of_indexed`; consumes exactly `TS3` beyond the bytecode, as
before. -/
theorem P5R_shaped_groundtruth
    (hp0 : HonestParams) (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer) (fee : Integer)
    (hdep : Deployed hp0)
    (hoc : OnChain
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 a0 rMint fee))
    (hv : validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 a0 rMint fee))
    (ha : isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty hp0.directoryNodeCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee)) :
    ∃ t ∈ (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
             hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
             w0 a0 rMint fee).scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp0.directoryNodeCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKey t.txInInfoResolved = some k ∧
             dirNodeNext t.txInInfoResolved = some n ∧ k < cs ∧ cs < n := by
  obtain ⟨hauth, hcov⟩ :=
    P5R_shaped_indexed ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 a0 rMint fee hv ha
  exact P5_groundtruth_of_indexed hp0 cs _ _ 1 hdep hoc
    (shapeR_refIdx1 cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
      hp0.directoryNodeCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 a0 rMint fee)
    hauth hcov

/-! ## §4 Polarity controls (ADDENDUM E9) — the full control set, re-run -/

/-- Negative control at the re-cut shape: a shape-G1R context whose node at the
claimed index FAILS either the directory authentication or the covering interval
is REJECTED by the bytecode. -/
theorem P5R_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) →
    ¬(dirNodeAuthH dirCS
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true) →
    isUnsuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee)
      := by blaster (timeout: 1500)

/-- Tightness stanza at the re-cut shape: the NEGATION of P5's postcondition
under an accepting run must be FALSIFIABLE. Expected: `Falsified`. -/
def P5R_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) →
    isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee) →
    ¬(dirNodeAuthH dirCS
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true
      ∧ coversCS cs
        (globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS).txInInfoResolved = true)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P5R_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT THE RE-CUT SHAPE AND ITS OWN TERM.** "No
accepting shape-G1R context exists within 1600 CEK steps" must be FALSIFIED.
Expected: `Falsified`. This is a NEW obligation — the probe at SHAPE G1 says
nothing about SHAPE G1R, because the term is a different `#prep_uplc` output. -/
def P5R_shaped_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer),
    validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) →
    ¬ isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P5R_shaped_vacuity_probe]

/-! ## §5 CONCRETE accepting witness OF EXACTLY SHAPE G1R — executable, no SMT

`WSC/Props/Shaped/P5Shaped.lean`'s SHAPE-G1 witness with the two re-cut changes
and nothing else: the withdrawal map is the single own-credential entry
(`GLOBAL`, amount 0) and the redeemer map carries the `Minting MMM` entry
(payload `Data.I 99`, an arbitrary symbolic-slot value) ahead of the own
`Rewarding GLOBAL` entry. Leaf values otherwise identical, so the two witnesses
are directly comparable — including their K. -/

namespace P5RShapedWitness

set_option maxRecDepth 1000000

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE G1R at SHAPE G1's witness leaf values. -/
def ctx : ScriptContext :=
  globalRShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "DEST") 150 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") 0 99
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis IN FULL —
now with a redeemer map that also passes `validRedeemerMap` at length 2 and
covers the mint. -/
theorem ctx_valid : validRewardingContext ctx = true := by native_decide

/-- The witness satisfies P5's postcondition. -/
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

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this
shape-G1R context at budget 1600, through the SHAPED applied term the theorems
above quantify over. -/
theorem exec_accepts_at_1600 :
    isSuccessful
      (appliedGlobalShapedG1R.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "DEST") 150 7
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "GLOBAL") 0 99
        50) :=
  isHaltB_sound _ (by native_decide)

/-- …and the UNSHAPED 1600 prep's executable term accepts the same context. -/
theorem exec_accepts_at_1600_unshaped :
    isSuccessful (appliedGlobal1600.exec ppCS ctx) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1402` against the PR #112 bytecode**, pinned
TWO-SIDED (halts at 1402, budget-errors at 1401). Budget 1600, headroom 198.

RE-MEASURED at wsc-poc main @ `2306678` (task N4): it was **1541** against the
pre-#112 global, so this shape got **9.0 % cheaper**. That is the same direction
and rough size as the 6.5-14.7 % reductions unit N2 measured on the global
goldens, and it is the only thing about this witness that PR #112 changed.

The pre-#112 note attached to this measurement still holds and is worth keeping:
`K` is IDENTICAL between SHAPE G1 and SHAPE G1R at any fixed bytecode, because
the transfer path never dereferences `txInfoRedeemers` — it reads its own
redeemer out of `scriptContextRedeemer`. Enlarging the redeemer map to satisfy
Conway's `hasExactSetOfRedeemers` therefore costs ZERO CEK steps, which is what
makes the node-realizable re-cut free. -/
theorem K_is_1402 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 1402) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 1401) = false := by native_decide

end P5RShapedWitness

end WSC
