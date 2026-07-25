-- Root of the `WSC` library: UPLC-level containment proofs for the WSC
-- (CIP-113 programmable tokens) production validators.
-- See WSC/ARCHITECTURE.md and WSC/flats/PROVENANCE.md.
import WSC.Imports
-- Explicit (also reached via WSC.Imports): the global/transfer validator's
-- prep only decodes on the CIP-153-capable PlutusCoreBlaster pinned by
-- lakefile.lean — see ARCHITECTURE.md ADDENDUM E11 "Substrate pins".
import WSC.Prep.Global
-- Second prep of the SAME global validator at CEK budget 1600 (task Y1): the
-- 600 prep above is provably VACUOUS (its own probe returns Valid), while 1600
-- exceeds the cheapest accepting golden's K = 1554, so it is the budget P5 is
-- stated against.  See WSC/Prep/Global1600.lean's header.
import WSC.Prep.Global1600
import WSC.Redeemer
import WSC.Spec
-- ── task A1: the LEDGER SIDE, optimizer-free ────────────────────────────────
-- Four definitions, `XRun K params ctx = cekExecuteProgram <flat>.script
-- (<Prep inputs fn> params ctx) K`.  A leaf module (depends only on WSC/Prep/*)
-- so that BOTH WSC/Honest.lean and WSC/ShapeBridge.lean can name the same four
-- constants; that import cycle is why the four `LR_BUDGET_*` axioms could not be
-- restated against them before (audit F3).  Read its header for what the
-- restatement buys and — more important — what it does not.
import WSC.Runs
import WSC.Honest
import WSC.Props.P3_Base
-- P3 restated with its accept hypothesis on `Runs.baseRun K_base` instead of
-- `appliedBase.prop`, with its OWN vacuity probe at the run term.  This is what
-- WSC/Composition.lean's `p3_lifted` consumes after task A1, so no `#prep_uplc`
-- output appears on the composition's keystone path and `PropExecFaithful` is off
-- it.  Also records, with its health warning, the prop↔run equivalence at this
-- prep.
import WSC.Props.P3_BaseRun
-- P4/P4a (issuance minting policy) at budget 900: statements + the machine-checked
-- budget characterization and both positive witnesses. See the SOLVER COST stanza
-- in that file for what is and is not closed.
import WSC.Props.P4_Minting
-- Golden→Lean bridge + the three Y4 fidelity results (LR-CTX audit, real-suite
-- positive witness, redeemer/datum mirror gate). See WSC/LR-CTX-AUDIT.md.
import WSC.Goldens
-- P5 (escape-critical, NonMember/covering-node) at budget 1600: statement,
-- source-cited mirror of the three PNonMember checks, and the pure-Lean
-- reduction ladder.  READ the OBLIGATION STATUS block in that file: the
-- bytecode obligation is NOT discharged (blaster returned no verdict in 87 min).
import WSC.Props.P5_NonMember
-- Concrete non-vacuity witness for budget 1600 (real bytecode + real golden
-- NonMember ScriptContext: HALT at 1600, budget-ERROR at 1553).
import WSC.Props.P5_Witness1600
-- SOURCE MODEL of the global transfer validator (task Z4, ARCHITECTURE.md §2 B3
-- route): P1 (containment) and P6 (Member self-penalization) are unreachable at
-- UPLC (accepting runs cost 3,262/3,726 CEK steps), so they are proved against a
-- source-cited transcription bridged by ONE axiom.  The model's verdict equals
-- the real bytecode's on 4/4 global goldens, incl. the rejecting containment
-- violation.  READ the OBLIGATION STATUS block at the bottom of
-- WSC/Props/P1_Transfer.lean before citing anything from it.
import WSC.Model.GlobalModel
import WSC.Model.Ground
import WSC.Model.GlobalGoldens
import WSC.Props.P1_Transfer
import WSC.Props.P6_Member
-- P2 (seize) via the SOURCE-MODEL route (B3), task Z3: seize is unreachable at
-- UPLC (cheapest accepting run 2,570 CEK steps; prep at 2,000 unfinished in
-- 77 min; the budgets whose prep completes have vacuity probes returning Valid),
-- so it is proved against a source-cited transcription bridged by ONE axiom,
-- `WSC.SeizeModel.seizeModel_faithful`.  The model's verdict equals the real
-- bytecode's on 13/13 goldens, including the rejecting seize golden.  READ the
-- "HOW TO READ THIS FILE" block at the top of WSC/Props/P2_Seize.lean: conjunct 1
-- (structure preservation) is PROVEN unconditionally about the model, conjunct 2
-- (containment) is stated + verified on the goldens but NOT proven.
import WSC.Model.SeizeModel
import WSC.Model.SeizeDiff
import WSC.Props.P2_Seize
-- ── SHAPED-CONTEXT layer (task Z2) ──────────────────────────────────────────
-- Read WSC/SHAPING-RESULTS.md first.  These modules prove P4a, P4's BurnOnly arm
-- and P5 against the SAME bytecode at the SAME budgets as the UPLC modules above,
-- but over a fixed `Data` SKELETON with symbolic scalar leaves ("shaped
-- contexts").  That breaks the Z3 wall WSC/Props/P4_Minting.lean and
-- WSC/Props/P5_NonMember.lean record: P4a went from Undetermined-after-3,208 s to
-- Valid-in-1 s, and P5 from no-verdict-after-87-min to Valid-in-2 s, against the
-- same flats and the same budgets.  EVERY theorem in this layer is bounded TWICE
-- — by its CEK budget AND by its shape — and each shape's fixed dimensions are
-- published in its prep module's header.  Do not quote one bound without the
-- other.  Unlike the source-model route above, this layer adds NO faithfulness
-- axiom: it is the real compiled bytecode, symbolically executed.
import WSC.Shaped.Shape
import WSC.Shaped.BaseShaped
import WSC.Shaped.Calib.P3Unshaped
import WSC.Shaped.Calib.P3Shaped
import WSC.Shaped.MintingShaped
import WSC.Shaped.MintingShapedIdx
import WSC.Shaped.GlobalShaped
import WSC.Props.Shaped.P4Shaped
import WSC.Props.Shaped.P4ShapedIdx
import WSC.Props.Shaped.P5Shaped
-- ── P1 (CONTAINMENT) AT UPLC, task V1 ───────────────────────────────────────
-- The central property: "when the global validator accepts a transfer, no
-- registered programmable token can leave or vanish from the mini-ledger",
-- in the SIGNED form `outAtBase ≥ inAtBase + mintOf`.  Previously recorded as
-- NOT-REACHABLE-AT-UPLC (symbolic prep at the required budget extrapolated at
-- 7-182 YEARS, WSC/goldens/K-MEASUREMENTS.md §5.2) and proved only on the
-- source model behind `WSC.Model.globalModel_faithful`.  Shaped prep is
-- budget-independent, so it is now PROVED against the real compiled bytecode at
-- budget 4400 over four shapes (T1/T2/T6/T7) with NO faithfulness axiom —
-- `#print axioms` audit in WSC/Shaped/Probe/P1Axioms.lean.  Bounded twice (budget
-- AND shape) like the rest of the shaped layer; read the SCOPE block at the top
-- of WSC/Props/Shaped/P1Shaped.lean before quoting anything from it, including
-- which of the three containment dispatch paths is covered (Path A only, and why).
import WSC.Shaped.GlobalShapedP1
import WSC.Shaped.GlobalShapedP1Prep
import WSC.Shaped.GlobalShapedP1MintPrep
import WSC.Shaped.GlobalShapedP1Out
import WSC.Shaped.GlobalShapedP1OutPrep
import WSC.Props.Shaped.P1Shaped

-- COMPOSITION (task V4): the ledger-level objects, the per-transaction
-- Preservation theorem, and the lift to the top-level claim.  READ the
-- "§9 DISCHARGE STATUS" block at the bottom of that file before citing it: the
-- top theorem is a machine-checked REDUCTION of the claim to four named leaf
-- obligations, none of which is fully discharged today.
import WSC.Composition
-- P2 (seize/clawback) at UPLC over SHAPE S1, budget 3800 (task Z6): BOTH
-- conjuncts, including the containment conjunct that WSC/Props/P2_Seize.lean §5
-- records as unproven on the source model.  READ the SCOPE block: two binding
-- bounds (budget + shape) plus three by-construction equalities forced by the
-- `#prep_uplc` defect D4 documented in WSC/Shaped/SeizeShaped.lean's header.
import WSC.Shaped.SeizeShaped
import WSC.Props.Shaped.P2Shaped
import WSC.Shaped.Probe.S1K
-- ── task V3: the remaining P4 arms, the four-way disjunction, and P6 ─────────
-- SHAPE L1 (Local), DT1 (DelegateTransfer), DS1 (DelegateSeize) complete the
-- arm-by-arm coverage of P4's four-way custody disjunction at UPLC; SHAPE G6
-- (Member) adds P6.  The headline is P4-Local: the issuance policy's OWN
-- no-escape scan over every output is now a theorem about the real bytecode
-- (ground-truth `noEscape`, NOT "the validator's scan returned true"), where the
-- two delegating arms only prove that a sibling validator RUNS.
-- Each shape's concrete witness reproduces its production golden's CEK step count
-- exactly: L1 = 1681, DT1 = 1257 (M1 = 784).  P6's shape needed budget 3300 — at
-- 2500 its vacuity probe was Valid, i.e. genuinely vacuous (witness K = 2837).
-- Read WSC/status-fragments/V3.md for the full ladder including that failure.
import WSC.Shaped.MintingLocalShaped
import WSC.Shaped.MintingLocalShapedIdx
import WSC.Shaped.MintingDelegateShaped
import WSC.Shaped.GlobalMemberShaped
import WSC.Props.Shaped.P4LocalShaped
import WSC.Props.Shaped.P4DelegateShaped
import WSC.Props.Shaped.P6Shaped
-- Bridge from the shaped P6 theorem to WSC/Composition.lean's vocabulary (the two
-- tasks defined the same two ground-truth quantities independently; the bridge is
-- two `rfl`-style inductions and adds no trust).
import WSC.Props.Shaped.P6Bridge
-- ── task A1: every non-vacuity obligation of WSC/Honest.lean, DISCHARGED ─────
-- Five theorems: MintingNonVacuous@2500, GlobalNonVacuous@{1600,3300,4400},
-- SeizeNonVacuous@3800, each `native_decide` on the real CEK from a named shaped
-- witness, each with NO `sorryAx` and NO project axiom.  Closes audit F7 (which
-- recorded GlobalNonVacuous open) and reverses the "MEASURED FALSE at every
-- affordable budget" entry for seize.  Downstream module because Honest.lean
-- cannot import the witnesses (they import it) — the P6Bridge precedent.
-- With Composition's `baseNonVacuous`/`mintingNonVacuous` the set is complete.
import WSC.Props.Shaped.NonVacuity
-- ── the SHAPE BRIDGE (task U1), added to the default target by the U3 audit ──
-- `isSuccessful (appliedXShaped.prop args) ↔ isSuccessful (appliedX.prop (shapedCtx
-- args))` for all 16 shaped preps, plus the kernel-checked `exec`-level form
-- (`XRun K`, no optimizer, `rfl`).  It was NOT in this root module when U1 landed
-- it, so `lake build WSC` did not check it; the U3 clean-room rebuild measured the
-- cost of including it at 36 s and 25 of the 98 solver verdicts, so it is imported
-- here rather than left to a separate invocation.  READ §5 of WSC/SHAPE-BRIDGE.md
-- before quoting Tier B rows: they are stated against `Runs.XRun K`, and the
-- residual `PropExecFaithful` is NOT discharged.
-- TASK A1: the §RUN definitions moved from this module to WSC/Runs.lean and the
-- `LR_BUDGET_*` axioms now name them, so the 16 kernel-checked `exec_*` `rfl`s are
-- the connective between a shaped theorem and the ledger side.  The 25 verdicts
-- here are unchanged in statement and were re-run.
import WSC.ShapeBridge
-- ── task A2: SHAPE REALIZABILITY — why audit F1 cannot be closed by a shaped
-- `Shape` instantiation.  Every shaped context in this library bakes a one-entry
-- redeemer map (two for DS1) while baking two SCRIPT-credential withdrawals, and
-- the Conway `MissingRedeemers` rule needs one entry per script witness.  For
-- SHAPE T1 the resulting class is PROVABLY EMPTY from axioms this library already
-- has (`LR_SPEND_RUNS_VALIDATOR` + `LR_CTX`, no `sorryAx`); for L1/M1/G1/S1/DT1/DS1
-- it is empty under the `MissingRedeemers` rule, stated there as a `Prop` and NOT
-- as an axiom.  The module also builds the VACUOUS `LeafSet` at SHAPE T1 and, next
-- to it, the proof that no honest step can fire in that class — read it before
-- quoting any composition result over a shape.  The NON-vacuous `LeafSet` is
-- `WSC/Composition.lean` §11 (`containedLeaves`).
import WSC.Props.Shaped.ShapeRealizability
-- ── task C1: THE NODE-REALIZABLE RE-CUT OF THE GLOBAL VALIDATOR'S SHAPES, and
-- P1/P5/P6 re-proved over them.  The A2 finding above says the shaped classes are
-- EMPTY as classes of ledger transactions; these modules fix that for the global
-- (transfer) validator by giving each shape a redeemer map that COVERS every
-- script witness the transaction needs — a `Spending` entry per
-- script-payment-credential input, a `Rewarding` entry per script withdrawal, a
-- `Minting` entry per minted policy — at the measured sizes of the real accepting
-- goldens.  Six re-cut shapes (G1R, G6R, T1R, T2R, T6R, T7R), six preps, five
-- re-proved headline theorems with their full control sets, and — the acceptance
-- criterion — a REALIZABILITY theorem per shape: class-level coverage for every
-- leaf assignment plus a concrete `validRewardingContext`-clean, redeemer-covered
-- context the real bytecode accepts.  Measured: every witness K is UNCHANGED, so
-- redeemer coverage costs zero CEK steps for this validator.
import WSC.Shaped.GlobalShapedR
import WSC.Shaped.GlobalShapedRPrep
import WSC.Shaped.GlobalMemberShapedRPrep
import WSC.Shaped.GlobalShapedP1RPrep
import WSC.Shaped.GlobalShapedP1RMintPrep
import WSC.Shaped.GlobalShapedP1ROutPrep
import WSC.Shaped.GlobalShapedP1ROutMintPrep
import WSC.Props.Shaped.P1ShapedR
import WSC.Props.Shaped.P5ShapedR
import WSC.Props.Shaped.P6ShapedR
import WSC.Props.Shaped.GlobalRealizability
