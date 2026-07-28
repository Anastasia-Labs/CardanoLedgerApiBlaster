-- ⚠️ PRE-#112 (PARTIAL): part of this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Read WSC/IMPACT-PR112.md for the split before quoting anything here.
/-
WSC/Props/Shaped/RealizableShapes.lean — **the task-C2 acceptance ledger: every
re-cut minting/seize shape's realizability theorem in one place, next to the
machine-checked failure of the shape it replaces.**

════════════════════════════════════════════════════════════════════════════
WHAT C2 WAS FOR
════════════════════════════════════════════════════════════════════════════
Audit finding F2 (`WSC/Props/Shaped/ShapeRealizability.lean`): every shape in the
pre-C2 library bakes a redeemer map too small to witness the script witnesses the
same shape bakes, so — by Conway UTXOW's `MissingRedeemers` — each shape class is
EMPTY as a class of ledger transactions. The P-theorems over them are TRUE and
UNCOMPOSABLE.

C2 re-cuts the ISSUANCE POLICY's four arm shapes and the SEIZE validator's shape
so that the redeemer map covers every script witness EXACTLY, and re-proves P4
(all four custody arms, plus the loosened-index rung) and P2 (both conjuncts) over
them. C1 owns the global shapes; C3 owns CLAB and the docs.

════════════════════════════════════════════════════════════════════════════
THE BEFORE / AFTER, MACHINE-CHECKED
════════════════════════════════════════════════════════════════════════════
§1 below is the point of this module: for each pre-C2 shape's own accepting witness
the library already had, `Realizability.redeemerCovered` is **`false`**; for each
re-cut shape's witness it is **`true`**, and the withdrawal/spending/mint coverage
holds at EVERY member of the re-cut class — twice over: §2 in this task's own
∀-form vocabulary, and **§2c in CLAB's, i.e. task C3's
`CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus` over all six `scriptsNeeded`
sources**. §4 adds `redeemersExactAllPlutus` (BOTH halves of Conway's
`hasExactSetOfRedeemers`) at every witness. All of it is `native_decide` /
ordinary Lean — no axiom, no solver, no `sorryAx`.

| property | old shape | old verdict | old realizability | **new shape** | **new verdict** | **new realizability** | witness K |
|---|---|---|---|---|---|---|---|
| P4a (C1) | M1 | Valid | **EMPTY** under coverage | **M1R** | **Valid** | **REALIZABLE** | 784 |
| P4 BurnOnly scan | M1 | Valid | EMPTY | **M1R** | **Valid** | REALIZABLE | 784 |
| P4 BurnOnlyOk | M1 | Valid | EMPTY | **M1R** | **Valid** | REALIZABLE | 784 |
| P4a, index free | M2 | Valid | EMPTY | **M2R** | **Valid** | REALIZABLE | 784 |
| P4 BurnOnly, index free | M2 | Valid | EMPTY | **M2R** | **Valid** | REALIZABLE | 784 |
| P4-Local `noEscape` | L1 | Valid | EMPTY | **L1R** | **Valid** | REALIZABLE | 1681 |
| P4-Local `noEscape`, reg index free | L2 | Valid | EMPTY | **L2R** | **Valid** | REALIZABLE | 1681 |
| P4a on Local | L1 | Valid | EMPTY | **L1R** | **Valid** | REALIZABLE | 1681 |
| P4-Local registration | L1 | Valid | EMPTY | **L1R** | **Valid** | REALIZABLE | 1681 |
| P4 `LocalCustodyOk` | L1 | Valid | EMPTY | **L1R** | **Valid** | REALIZABLE | 1681 |
| P4 4-way disjunction | L1 | Valid | EMPTY | **L1R** | **Valid** | REALIZABLE | 1681 |
| P4 `DelegateTransferOk` | DT1 | Valid | EMPTY | **DT1R** | **Valid** | REALIZABLE | 1257 |
| P4 global-runs | DT1 | Valid | EMPTY | **DT1R** | **Valid** | REALIZABLE | 1257 |
| P4 4-way at DT | DT1 | Valid | EMPTY | **DT1R** | **Valid** | REALIZABLE | 1257 |
| P4 `DelegateSeizeOk` | DS1 | Valid | EMPTY | **DS1R** | **Valid** | REALIZABLE | 1466 |
| P4 4-way at DS | DS1 | Valid | EMPTY | **DS1R** | **Valid** | REALIZABLE | 1466 |
| P2a structure | S1 | Valid | EMPTY | **S1R** | **Valid** | REALIZABLE | 3004 / 3328 |
| P2b containment | S1 | Valid | EMPTY | **S1R** | **Valid** | REALIZABLE | 3004 / 3328 |
| P2 gates earned | S1 | Valid | EMPTY | **S1R** | **Valid** | REALIZABLE | 3004 / 3328 |

Every witness K is UNCHANGED from the shape it replaces, and each still equals its
production golden's measured step count where one exists (M1R 784 =
`mint-burnonly`; L1R 1681 = `mint-local-registered-by-ref`; DT1R 1257 =
`mint-delegate-transfer-topup`). The re-cut is therefore cost-neutral at the CEK
level, for a reason that is structural rather than lucky: the context reaches the
machine as ONE constant term (`CardanoLedgerApi/V3/Contexts.lean:717-726`), and the
only arm that walks the redeemer map at all is `DelegateSeize`.

**EVERY SHAPE IS NOW RE-CUT — CORRECTED AT THE G STAGE (2026-07-25).** This
paragraph used to read *"WHAT IS STILL NOT RE-CUT … SHAPE L2"*, and that is
**false as of `f4486ca`**: SHAPE **L2R** (`WSC/Shaped/MintingLocalShapedRIdx.lean`)
is the re-cut of the free-REGISTRATION-index rung, it is node-realizable, and it
carries the full four-item bar. That is audit finding **F19**, closed; the roster
is **13 of 13** re-cut shapes (T1R, T2R, T6R, T7R, G1R, G6R, M1R, M2R, L1R,
**L2R**, DT1R, DS1R, S1R), with no 3/4 row left.

What remains true is the *statement about the OLD shape*: SHAPE L2
(`WSC/Shaped/MintingLocalShapedIdx.lean`) is still proved empty, so
`WSC.P4_local_noEscape_shapedIdx` — the theorem over it — is still a TRUE and
UNCOMPOSABLE measurement about index-dependence, and it is **superseded by
`WSC.P4_local_noEscape_RIdx`** (`WSC/Props/Shaped/P4LocalShapedR.lean`) over SHAPE
L2R. Both are retained: the pre/post pair is what makes §1's before/after table
machine-checkable.

**NAMING, recorded because an auditor tripped on it.** L2R's realizability theorem
is `WSC.L2RWitness.ctx_realizable` (`P4LocalShapedR.lean`). There is no
`l2r_realizable` in that file; §2 below declares one here, as a plain alias, in the
same shape as the other six roster entries.

**WHAT "REALIZABLE" MEANS HERE, exactly.** `Realizability.Realizable` =
`validScriptContext` (CLAB's strongest ledger predicate) **+** the
`MissingRedeemers` row CLAB is missing **+** the two ∀-forms that block both
emptiness routes of `ShapeRealizability`. It is NOT "a node would accept this
transaction": CLAB models neither fees against a protocol-parameter set, nor
agreement between a withdrawal credential and the script actually supplied in the
witness set, nor the UTxO set the inputs are drawn from. The exact claim is: *the
one defect audit F2 identified is gone, and the classes the C2 theorems quantify
over are non-empty.*
-/
import WSC.Props.Shaped.P4ShapedR
import WSC.Props.Shaped.P4ShapedRIdx
import WSC.Props.Shaped.P4LocalShapedR
import WSC.Props.Shaped.P4DelegateShapedR
import WSC.Props.Shaped.P2ShapedR
-- the PRE-C2 witnesses, so the before/after is one `native_decide` apart
import WSC.Props.Shaped.P4Shaped
import WSC.Props.Shaped.P4LocalShaped
import WSC.Props.Shaped.P4DelegateShaped
import WSC.Shaped.S1Witnesses

namespace WSC.RealizableShapes

open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol ScriptHash TokenName)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! # §1 BEFORE / AFTER, in one theorem per validator

Each statement pairs the OLD shape's own accepting witness — the one its P-theorem
campaign was calibrated on — with the NEW shape's, and shows the coverage bit
flipping from `false` to `true`. The `false` half is the machine-checked form of
audit F2; the `true` half is the machine-checked form of its repair. -/

/-- **ISSUANCE, `BurnOnly` arm.** SHAPE M1's witness is NOT redeemer-covered;
SHAPE M1R's is. -/
theorem burnOnly_before_after :
    Realizability.redeemerCovered WSC.P4ShapedWitness.ctx = false ∧
    Realizability.redeemerCovered WSC.M1RWitness.ctx = true := by native_decide

/-- **ISSUANCE, `Local` arm.** -/
theorem local_before_after :
    Realizability.redeemerCovered WSC.P4LocalShapedWitness.ctx = false ∧
    Realizability.redeemerCovered WSC.L1RWitness.ctx = true := by native_decide

/-- **ISSUANCE, `DelegateTransfer` arm.** -/
theorem delegateTransfer_before_after :
    Realizability.redeemerCovered WSC.P4DelegateShapedWitness.ctxDT = false ∧
    Realizability.redeemerCovered WSC.DelegateRWitness.ctxDT = true := by native_decide

/-- **ISSUANCE, `DelegateSeize` arm.** SHAPE DS1's TWO-entry redeemer map is still
uncovered — it names a `Rewarding` credential that is not one of the two script
withdrawals (`ShapeRealizability.ds1_uncovered_wdrl_exists`); SHAPE DS1R's three
entries cover both withdrawals and the mint. -/
theorem delegateSeize_before_after :
    Realizability.redeemerCovered WSC.P4DelegateShapedWitness.ctxDS = false ∧
    Realizability.redeemerCovered WSC.DelegateRWitness.ctxDS = true := by native_decide

/-- **SEIZE.** All four SHAPE-S1 instances are uncovered; all four SHAPE-S1R
instances are covered — including the two the campaign needs to be REJECTED, which
is what upgrades them from "a context the bytecode refuses" to "a transaction an
attacker could really build and the bytecode refuses". -/
theorem seize_before_after :
    Realizability.redeemerCovered WSC.P2ShapedWitness.ctxAccept = false ∧
    Realizability.redeemerCovered WSC.P2ShapedWitness.ctxResidual = false ∧
    Realizability.redeemerCovered WSC.P2ShapedWitness.ctxEscape = false ∧
    Realizability.redeemerCovered WSC.P2ShapedWitness.ctxStolen = false ∧
    Realizability.redeemerCovered WSC.P2RWitness.ctxAccept = true ∧
    Realizability.redeemerCovered WSC.P2RWitness.ctxResidual = true ∧
    Realizability.redeemerCovered WSC.P2RWitness.ctxEscape = true ∧
    Realizability.redeemerCovered WSC.P2RWitness.ctxStolen = true := by native_decide

/-! # §2 THE ACCEPTANCE CRITERION — one realizability theorem per re-cut shape

Each is `validScriptContext ∧ redeemerCovered ∧ WdrlCovered ∧ SpendCovered ∧
MintCovered` at a concrete member, with the last three supplied by the shape-level
∀-theorems so they hold at every other member of the class as well. -/

/-- SHAPE M1R (`BurnOnly`). -/
theorem m1r_realizable : Realizability.Realizable WSC.M1RWitness.ctx :=
  WSC.M1RWitness.ctx_realizable

/-- SHAPE M2R (`BurnOnly`, withdrawal index symbolic). -/
theorem m2r_realizable : Realizability.Realizable WSC.M2RWitness.ctx :=
  WSC.M2RWitness.ctx_realizable

/-- SHAPE L1R (`Local`). -/
theorem l1r_realizable : Realizability.Realizable WSC.L1RWitness.ctx :=
  WSC.L1RWitness.ctx_realizable

/-- **SHAPE L2R** (`Local`, REGISTRATION index symbolic) — added at the G stage so
that the roster is 13 of 13 and no re-cut shape is missing from it.

A plain alias of `WSC.L2RWitness.ctx_realizable`
(`WSC/Props/Shaped/P4LocalShapedR.lean`), which is the real name; there is no
`l2r_realizable` in that module, and this declaration exists so that nobody has to
invent one.

**READ IT WITH THE CAVEAT L2R'S OWN MODULE CARRIES.** `L2RWitness.ctx` is
`rfl`-equal to `L1RWitness.ctx` (`L2RWitness.ctx_eq_L1R`), i.e. the accepting
witness at L2R IS L1R's witness at `regIdx = 1`. So this row is NOT independent
evidence from `l1r_realizable`; what is genuinely new at SHAPE L2R is the
SYMBOLIC quantification in `WSC.P4_local_noEscape_RIdx` and the REJECTING witness
at `regIdx = 0` (`L2RWitness.exec_rejects_regIdx0`), neither of which is a
realizability fact. Deliberately NOT given a `#print axioms` line in §3: it is a
definitional alias, and this hygiene pass does not move the sealed axiom census of
`WSC/AUDIT.md` §3. -/
theorem l2r_realizable : Realizability.Realizable WSC.L2RWitness.ctx :=
  WSC.L2RWitness.ctx_realizable

/-- SHAPE DT1R (`DelegateTransfer`). -/
theorem dt1r_realizable : Realizability.Realizable WSC.DelegateRWitness.ctxDT :=
  WSC.DelegateRWitness.ctxDT_realizable

/-- SHAPE DS1R (`DelegateSeize`). -/
theorem ds1r_realizable : Realizability.Realizable WSC.DelegateRWitness.ctxDS :=
  WSC.DelegateRWitness.ctxDS_realizable

/-- SHAPE S1R (seize), at the "nothing moves" instance. -/
theorem s1r_realizable : Realizability.Realizable WSC.P2RWitness.ctxAccept :=
  WSC.P2RWitness.ctxAccept_realizable

/-- SHAPE S1R (seize), at the RESIDUAL-OUTPUT instance — the shape every real
accepting seize golden has. -/
theorem s1r_residual_realizable : Realizability.Realizable WSC.P2RWitness.ctxResidual :=
  WSC.P2RWitness.ctxResidual_realizable

/-! # §2c THE SAME COVERAGE, AT CLASS LEVEL, IN CLAB'S OWN VOCABULARY

§2's coverage theorems are stated with this task's `Realizability.*Covered`
predicates. The six below say the same thing with task C3's
`CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus`, i.e. against CLAB's own
transcription of `scriptsNeeded` over ALL SIX sources — so the certificate, vote
and proposal arms are discharged too (empty in every shape here), and the
statement is the class-level one: it holds for EVERY leaf assignment, not only at
the witnesses of §4. Same shape of proof as `WSC.g1R_class_coverage` (task C1). -/

theorem m1r_class_coverage
    (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer) (w0 : ByteString) (a0 : Integer)
    (mlRed : ByteString) (fee : Integer) (txid : ByteString) (oidx lo hi : Integer)
    (tid : ByteString) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid).scriptContextTxInfo = true := by
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.mintRRedeemerMap ownCS w0 mlRed) ≠ none := by
    rw [WSC.mintR_findRewarding]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Minting ownCS) (WSC.mintRRedeemerMap ownCS w0 mlRed) ≠ none := by
    rw [WSC.mintR_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.mintRCtx, WSC.mintRWdrl, WSC.mintRMint, WSC.mintRRedeemerMap]
  exact ⟨Realizability.isSome_of_ne_none h1, Realizability.isSome_of_ne_none h2⟩

theorem m2r_class_coverage
    (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer) (w0 : ByteString) (a0 : Integer)
    (mlRed : ByteString) (fee : Integer) (txid : ByteString) (oidx lo hi : Integer)
    (tid : ByteString) (wIdx : Integer) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
        lo hi tid wIdx).scriptContextTxInfo = true := by
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.mintRRedeemerMapIdx ownCS w0 mlRed wIdx) ≠ none := by
    rw [WSC.mintRIdx_findRewarding]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Minting ownCS) (WSC.mintRRedeemerMapIdx ownCS w0 mlRed wIdx) ≠ none := by
    rw [WSC.mintRIdx_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.mintRCtxIdx, WSC.mintRWdrl, WSC.mintRMint, WSC.mintRRedeemerMapIdx]
  exact ⟨Realizability.isSome_of_ne_none h1, Realizability.isSome_of_ne_none h2⟩

theorem l1r_class_coverage
    (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString) (fee : Integer) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed
        fee).scriptContextTxInfo = true := by
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.localRRedeemerMap ownCS w0 mlRed) ≠ none := by
    rw [WSC.localR_findRewarding]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Minting ownCS) (WSC.localRRedeemerMap ownCS w0 mlRed) ≠ none := by
    rw [WSC.localR_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.localRCtx, WSC.localRWdrl, WSC.localRRedeemerMap,
        WSC.localShapedParamsIn, WSC.localShapedNode, WSC.localShapedOutputs,
        WSC.localShapedOut0, WSC.localShapedOut1]
  exact ⟨Realizability.isSome_of_ne_none h1, Realizability.isSome_of_ne_none h2⟩

theorem dt1r_class_coverage
    (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString) (fee : Integer) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed
        fee).scriptContextTxInfo = true := by
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.dtRRedeemerMap ownCS w0 w1 mlRed glRed) ≠ none := by
    rw [WSC.dtR_findRewarding0]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w1)) (WSC.dtRRedeemerMap ownCS w0 w1 mlRed glRed) ≠ none :=
    WSC.dtR_findRewarding1_ne ownCS w0 w1 mlRed glRed
  have h3 : CardanoLedgerApi.V3.findRedeemer
      (.Minting ownCS) (WSC.dtRRedeemerMap ownCS w0 w1 mlRed glRed) ≠ none := by
    rw [WSC.dtR_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.dtRCtx, WSC.delegateRWdrl, WSC.dtRRedeemerMap,
        WSC.localShapedParamsIn, WSC.localShapedNode, WSC.localShapedOutputs,
        WSC.localShapedOut0, WSC.localShapedOut1]
  exact ⟨Realizability.isSome_of_ne_none h1, Realizability.isSome_of_ne_none h2,
         Realizability.isSome_of_ne_none h3⟩

theorem ds1r_class_coverage
    (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx
        fee).scriptContextTxInfo = true := by
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.dsRRedeemerMap ownCS w0 w1 mlRed sIdx) ≠ none := by
    rw [WSC.dsR_findRewarding0]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w1)) (WSC.dsRRedeemerMap ownCS w0 w1 mlRed sIdx) ≠ none :=
    WSC.dsR_findRewarding1_ne ownCS w0 w1 mlRed sIdx
  have h3 : CardanoLedgerApi.V3.findRedeemer
      (.Minting ownCS) (WSC.dsRRedeemerMap ownCS w0 w1 mlRed sIdx) ≠ none := by
    rw [WSC.dsR_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.dsRCtx, WSC.delegateRWdrl, WSC.dsRRedeemerMap,
        WSC.localShapedParamsIn, WSC.localShapedNode, WSC.localShapedOutputs,
        WSC.localShapedOut0, WSC.localShapedOut1]
  exact ⟨Realizability.isSome_of_ne_none h1, Realizability.isSome_of_ne_none h2,
         Realizability.isSome_of_ne_none h3⟩

theorem s1r_class_coverage
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
    (spRed mtRed ilRed : ByteString) (fee : Integer) :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      (WSC.seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        spRed mtRed ilRed fee).scriptContextTxInfo = true := by
  have h0 : CardanoLedgerApi.V3.findRedeemer
      (.Spending ⟨ByteString.mk "", 0⟩) (WSC.seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed)
        ≠ none := by
    rw [WSC.seizeR_findSpending]; exact Option.noConfusion
  have h1 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w0)) (WSC.seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed)
        ≠ none := by
    rw [WSC.seizeR_findRewarding0]; exact Option.noConfusion
  have h2 : CardanoLedgerApi.V3.findRedeemer
      (.Rewarding (.ScriptCredential w1)) (WSC.seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed)
        ≠ none :=
    WSC.seizeR_findRewarding1_ne mCS w0 w1 spRed mtRed ilRed
  have h3 : CardanoLedgerApi.V3.findRedeemer
      (.Minting mCS) (WSC.seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none := by
    rw [WSC.seizeR_findMinting]; exact Option.noConfusion
  simp [CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus,
        CardanoLedgerApi.V3.Contexts.scriptPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.spendingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.rewardingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.mintingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.votingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessed,
        CardanoLedgerApi.V3.Contexts.coveredBy,
        CardanoLedgerApi.V3.Contexts.certifyingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, WSC.Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        WSC.seizeRCtx, WSC.seizeShapedWdrl, WSC.seizeRRedeemerMap,
        WSC.seizeShapedIn0, WSC.seizeShapedIn1, WSC.seizeShapedParamsIn, WSC.seizeShapedNode,
        WSC.seizeShapedOut0, WSC.seizeShapedOut1]
  exact ⟨Realizability.isSome_of_ne_none h0, Realizability.isSome_of_ne_none h1,
         Realizability.isSome_of_ne_none h2, Realizability.isSome_of_ne_none h3⟩

/-! # §4 AGAINST C3's CLAB PREDICATE — the SECOND, INDEPENDENT transcription

Task C3 landed Conway's `hasExactSetOfRedeemers` inside CLAB while C2 was cutting
the shapes (`CardanoLedgerApi/V3/Contexts.lean`): `scriptPurposesWitnessed` is the
six-source `getConwayScriptsNeeded` (spending inputs at script addresses,
script-credential withdrawals, EVERY mint policy, script-witnessed certificates,
script-credential voters, guardrails proposals), `redeemerCoverageAllPlutus` is the
`MissingRedeemers` half and `noExtraRedeemersAllPlutus` the `ExtraRedeemers` half.

The theorems below are the cross-check, and they are stronger than §1–§2 in two
ways: the predicate is a DIFFERENT transcription of the rule (so agreement is
evidence both are right), and `redeemersExactAllPlutus` demands the EXACT SET, not merely
coverage — the C2 shapes carry no redeemer entry the transaction does not need,
which the `#red = #scriptIn + #mintPol + #scriptWdrl` count they were cut to hit
is exactly the statement of. -/

/-- **EVERY RE-CUT WITNESS SATISFIES CONWAY'S EXACT-SET RULE, both halves**, as
transcribed independently by task C3 in CLAB. -/
theorem all_recut_witnesses_redeemersExact :
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.M1RWitness.ctx.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.M2RWitness.ctx.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.L1RWitness.ctx.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.DelegateRWitness.ctxDT.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.DelegateRWitness.ctxDS.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.P2RWitness.ctxAccept.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.P2RWitness.ctxResidual.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.P2RWitness.ctxEscape.scriptContextTxInfo = true ∧
    CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus WSC.P2RWitness.ctxStolen.scriptContextTxInfo = true := by
  native_decide

/-- **AND EVERY PRE-C2 WITNESS FAILS C3's COVERAGE HALF** — the same verdict §1
reaches through this task's own predicate, now confirmed against CLAB's.

**F18: STATEMENT SURVIVES, INTERPRETATION IS DOWNGRADED (task G2).** This is a
closed `native_decide` about `Bool`s and it stays true verbatim. What it no
longer licenses is the reading "therefore these five witnesses are
unrealizable": `redeemerCoverageAllPlutus` is the ALL-PLUTUS reading of
`MissingRedeemers` and is strictly stronger than the rule
(`CardanoLedgerApi.V3.Contexts.coveredByNonNative_strictly_weaker`), so a
context whose only uncovered purposes are witnessed by NATIVE scripts fails this
predicate while passing Conway. The five witnesses' uncovered purposes are
`Rewarding` purposes at free symbolic hashes, nothing pins them to Plutus
scripts, so the unrealizability reading needs a non-native side condition — see
`WSC/Props/Shaped/ShapeRealizability.lean` §2.3, last row. Nothing in the
campaign's positive results depends on this theorem. -/
theorem all_old_witnesses_fail_c3_coverage :
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus WSC.P4ShapedWitness.ctx.scriptContextTxInfo = false ∧
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      WSC.P4LocalShapedWitness.ctx.scriptContextTxInfo = false ∧
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      WSC.P4DelegateShapedWitness.ctxDT.scriptContextTxInfo = false ∧
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      WSC.P4DelegateShapedWitness.ctxDS.scriptContextTxInfo = false ∧
    CardanoLedgerApi.V3.Contexts.redeemerCoverageAllPlutus
      WSC.P2ShapedWitness.ctxAccept.scriptContextTxInfo = false := by native_decide

/-- The acceptance criterion in its STRONGEST available form, for the two shapes
whose properties carry the most weight: P4-Local's no-escape scan and P2's two
conjuncts. -/
theorem l1r_realizableExact : Realizability.RealizableExact WSC.L1RWitness.ctx :=
  ⟨l1r_realizable, by native_decide⟩

theorem s1r_realizableExact : Realizability.RealizableExact WSC.P2RWitness.ctxAccept :=
  ⟨s1r_realizable, by native_decide⟩

theorem s1r_residual_realizableExact :
    Realizability.RealizableExact WSC.P2RWitness.ctxResidual :=
  ⟨s1r_residual_realizable, by native_decide⟩

theorem m1r_realizableExact : Realizability.RealizableExact WSC.M1RWitness.ctx :=
  ⟨m1r_realizable, by native_decide⟩

theorem dt1r_realizableExact : Realizability.RealizableExact WSC.DelegateRWitness.ctxDT :=
  ⟨dt1r_realizable, by native_decide⟩

theorem ds1r_realizableExact : Realizability.RealizableExact WSC.DelegateRWitness.ctxDS :=
  ⟨ds1r_realizable, by native_decide⟩

/-! # §3 AXIOM CENSUS — printed at build time.

Every statement in this module and every coverage theorem it cites must depend on
NO project axiom: the C2 re-cut may not buy realizability with an assumption.

MEASURED at this revision. The nine ∀-form coverage theorems (§2's backbone) come
out at `[propext, Classical.choice, Quot.sound]` — `mintR_spend_covered` at
`[propext, Quot.sound]` — i.e. ordinary Lean. The witness-level statements add
`Lean.ofReduceBool` and `Lean.trustCompiler`, which is what `native_decide`
contributes and what every concrete witness in this library already carries. **NO
`sorryAx` and no `WSC.LR_*` anywhere in this module** — so the realizability result
does not inherit the `admit`-closure of the `blaster`-proved P-theorems it is
about. -/
#print axioms WSC.RealizableShapes.burnOnly_before_after
#print axioms WSC.RealizableShapes.local_before_after
#print axioms WSC.RealizableShapes.delegateTransfer_before_after
#print axioms WSC.RealizableShapes.delegateSeize_before_after
#print axioms WSC.RealizableShapes.seize_before_after
#print axioms WSC.RealizableShapes.m1r_realizable
#print axioms WSC.RealizableShapes.m2r_realizable
#print axioms WSC.RealizableShapes.l1r_realizable
#print axioms WSC.RealizableShapes.dt1r_realizable
#print axioms WSC.RealizableShapes.ds1r_realizable
#print axioms WSC.RealizableShapes.s1r_realizable
#print axioms WSC.RealizableShapes.s1r_residual_realizable
#print axioms WSC.RealizableShapes.m1r_class_coverage
#print axioms WSC.RealizableShapes.m2r_class_coverage
#print axioms WSC.RealizableShapes.l1r_class_coverage
#print axioms WSC.RealizableShapes.dt1r_class_coverage
#print axioms WSC.RealizableShapes.ds1r_class_coverage
#print axioms WSC.RealizableShapes.s1r_class_coverage
#print axioms WSC.RealizableShapes.all_recut_witnesses_redeemersExact
#print axioms WSC.RealizableShapes.all_old_witnesses_fail_c3_coverage
#print axioms WSC.RealizableShapes.l1r_realizableExact
#print axioms WSC.RealizableShapes.s1r_realizableExact
-- the ∀-form coverage theorems the criterion rests on
#print axioms WSC.mintR_wdrl_covered
#print axioms WSC.mintR_spend_covered
#print axioms WSC.mintR_mint_covered
#print axioms WSC.localR_wdrl_covered
#print axioms WSC.dtR_wdrl_covered
#print axioms WSC.dsR_wdrl_covered
#print axioms WSC.seizeR_wdrl_covered
#print axioms WSC.seizeR_spend_covered
#print axioms WSC.seizeR_mint_covered

end WSC.RealizableShapes
