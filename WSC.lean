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
-- ── task N3: P3 after wsc-poc PR #112 ───────────────────────────────────────
-- The post-#112 base validator reads an INDEX out of its redeemer instead of
-- scanning the withdrawal map, and the UNSHAPED P3 goal no longer closes
-- (measured `⚠️ Undetermined` at 600 s, 2400 s, at a redeemer-only shape and at
-- a smaller budget — `WSC/Props/P3_Base.lean` §MEASUREMENT).  P3 is therefore a
-- SHAPED property now, over SHAPES B1RG / B1RS, with the full four-point bar
-- including class- and point-level realizability.  Read the header of
-- WSC/Shaped/BaseShapedR.lean for the cut and what it costs.
import WSC.Props.Shaped.P3ShapedR
-- ── task N6: P3 at SHAPE B1W, and the RESTORED composition keystone ─────────
-- SHAPES B1RG/B1RS freeze the whole `TxInfo`, so they are disjoint from the
-- classes the composed results live over and cannot close branch C of
-- `Composition.nonEscape_of_registered`.  SHAPE B1W freezes ONLY the withdrawal
-- map (two script entries — what SHAPES T1R and S1R already have) and leaves the
-- redeemer, both parameters and every other `TxInfo` field symbolic.  It closes
-- in ≈ 5 s and is what `Composition.p3_lifted` now consumes.
import WSC.Props.P3_BaseWdrl
-- The measured boundary of that cut: withdrawal maps of length 1 and 2 close
-- with the credentials fully symbolic too; length 3 returns no verdict at 900 s.
import WSC.Shaped.Probe.P3WdrlLadder
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
-- Non-vacuity at budget 1600 is discharged downstream, by
-- `WSC.NonVacuity.globalNonVacuous_at_1600` (WSC/Props/Shaped/NonVacuity.lean):
-- `native_decide` on the real CEK over `Runs.globalRun 1600`, no solver and no
-- `sorryAx`.  (The former `WSC/Props/P5_Witness1600.lean`, two `native_decide`
-- theorems over the fully applied golden flat, was deleted as redundant with it —
-- nothing in Lean ever depended on them.  The golden's own K = 1554 remains
-- recorded in WSC/goldens/K-MEASUREMENTS.md §3.)
-- ── THE SOURCE-MODEL LAYER (ARCHITECTURE.md §2 route B3) — **DEAD ROUTE, KEPT
-- ── AS DOCUMENTATION.  NO AXIOM.  NO BRIDGE TO THE BYTECODE.**
--
-- These modules hand-transcribe the PRE-#112 `mkProgrammableLogicGlobal` and
-- `mkProgrammableSeize`.  They were the fallback for a wall that no longer
-- exists: shaped contexts (task V1/Z6, re-cut at N5/H2) put P1, P2, P5 and P6 at
-- UPLC against the compiled production program.  Each model carried ONE
-- faithfulness axiom bridging it to the bytecode; **BOTH AXIOMS ARE FALSE AND
-- BOTH WERE RETRACTED AT TASK R1**, together with every declaration that rested
-- on them (`P1_bytecode`, `P1_bytecode_of_P1_model`, `P6_bytecode`,
-- `P6_bytecode_of_P6_model`, `P2a_bytecode`, `P2b_bytecode`,
-- `P2b_model_implies_bytecode`).  The refutations are machine-checked, in
-- WSC/Model/GlobalModelRefuted.lean and WSC/Model/SeizeModelRefuted.lean.
--
-- HOW TO READ ANYTHING THAT SURVIVES HERE.  Everything is in exactly one of two
-- categories, and neither is a claim about production:
--   * TRUE LEAN FACTS ABOUT A STALE MODEL — `P1.pathC_sound`, `P1.accum_lookup`,
--     `P6_Member.mintWalk_sublist` / `mintWalk_member_retains`,
--     `P2.P2a_seizeModel_preserves_structure`, the two `tokensContain_unsound_*`
--     counterexamples.  Still true; simply not about the deployed script.
--   * SPECIFICATION VOCABULARY that the LIVE UPLC results consume —
--     WSC/Model/Ground.lean's `outSum`/`inSum` (which is NOT a model at all and
--     no longer imports one), `mintSigned`/`mintPosOf`/`coveringNodeExists`/
--     `paramsPinned`, `P2.sumOutAtBase`/`sumInAtBase`, and the seize redeemer
--     projections `seizedPolicyOf`/`pairedOutputsOf`/`progLogicCredDataOf`.
--
-- WSC/Model/SeizeDiff.lean is retained as a CASE STUDY: its 13/13 differential
-- test is still green against the post-#112 bytecode, because no golden in the
-- suite exercises the rule PR #112 changed.  A green differential test over a
-- suite that does not cover the delta is not evidence of fidelity.
import WSC.Model.GlobalModel
import WSC.Model.Ground
import WSC.Model.GlobalGoldens
import WSC.Props.P1_Transfer
import WSC.Props.P6_Member
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
-- SHAPE S1 — the PRE-re-cut seize shape.  `WSC/Props/Shaped/P2Shaped.lean`, which
-- proved P2 over it at budget 3800 (task Z6), was DELETED by task N6: it is
-- REFUTED at wsc-poc `main` @ 2306678 (PR #112) — `P2a_shaped_structure`
-- `❌ Falsified` on the ada top-up #112 legalised, and its K measurement
-- `native_decide`-false because the seize step counts moved.  It is superseded by
-- `WSC/Props/Shaped/P2ShapedR.lean` over the node-realizable SHAPE S1R.  The four
-- SHAPE-S1 witness contexts survive in WSC/Shaped/S1Witnesses.lean, because
-- WSC/Props/Shaped/RealizableShapes.lean's measurement "none of them is
-- redeemer-covered" is the historical justification for the S1 → S1R re-cut.
import WSC.Shaped.SeizeShaped
import WSC.Shaped.S1Witnesses
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
import WSC.Props.Shaped.ShapeRealizability
-- ── task H2: the RE-CUTS that reach the OTHER containment dispatch paths ─────
-- SHAPES T1R/T2R/T6R/T7R/T8R above all carry a SINGLE-asset expected value, so
-- every one takes containment PATH A (the single-asset accumulate-scan).
-- ARCHITECTURE.md Tier 3.1 asks for all three dispatch paths.  SHAPE T3R (two
-- token names per policy) leaves PATH A and runs `checkWholesaleThenBuiltin` —
-- PATH B's wholesale `Data` equality falling through to PATH C's CIP-153
-- `pvalueContains`; SHAPE T4R (two mini-ledger inputs) drives `pvalueFromCred`
-- into its PHASE 3 builtin accumulation.  Both were blocked TWICE — by upstream
-- Blaster defect D6 (fixed at `4d320dd`) and, independently, by the fact that
-- the pre-re-cut SHAPES T3/T4 are provably unbuildable on a node (3 and 4
-- redeemer entries demanded, 1 supplied).  P1ShapedBC proves P1 over both to the
-- four-point bar and BACKS the dispatch-path claim with executable witnesses:
-- PATH A excluded and PATH C's execution PROVED; PATH B's separated by cost
-- (K 1936 vs 2228), because on ledger-valid contexts PATH B implies PATH C and
-- so no accept/reject test can isolate it.
import WSC.Shaped.GlobalShapedP1BC
import WSC.Shaped.GlobalShapedP1BCPrep
import WSC.Props.Shaped.P1ShapedBC
-- ── task C2: NODE-REALIZABLE RE-CUTS of the MINTING and SEIZE shapes ─────────
-- Audit F2 / WSC/Props/Shaped/ShapeRealizability.lean proved every pre-C2 shape
-- EMPTY as a class of ledger transactions: the redeemer map is too small to
-- witness the script witnesses the same shape bakes (Conway `MissingRedeemers`).
-- These modules re-cut the ISSUANCE policy's four arm shapes (M1R, M2R, L1R,
-- DT1R, DS1R) and the SEIZE validator's shape (S1R) so the redeemer map covers
-- every script witness EXACTLY — one `Spending` entry per script input, one
-- `Minting` entry per minted policy, one `Rewarding` entry per script withdrawal,
-- the rule reproduced on 13/13 goldens — and re-prove P4 (all four custody arms,
-- the four-way disjunction, and the loosened-index rung) and P2 (BOTH conjuncts)
-- over them.  Same flats, same budgets, same ground-truth postconditions, and
-- every witness K unchanged (784 / 1681 / 1257 / 1466 / 3004+3328), each still
-- matching its production golden's measured step count where one exists.
-- WSC/Realizability.lean is the missing LR-CTX row as a decidable predicate (a
-- DEFINITION, not an axiom; C3 owns the CLAB-side row).
-- READ WSC/Props/Shaped/RealizableShapes.lean FIRST: it holds the before/after
-- table, the per-shape realizability theorems that are C2's acceptance criterion,
-- the machine-checked `redeemerCovered = false → true` flip for every pre-C2
-- witness, the axiom census, and the one shape NOT re-cut (L2).
--
-- STAGE 11 / TASK G1 UPDATE: L2 **is** now re-cut. `WSC.Shaped.MintingLocalShapedRIdx`
-- (SHAPE L2R) closes audit finding F19, and its four-item bar lives at the foot of
-- `WSC/Props/Shaped/P4LocalShapedR.lean`. `RealizableShapes.lean`'s "one shape NOT
-- re-cut" row is therefore stale — read `P4LocalShapedR.lean`'s header for the
-- current disposition.
import WSC.Realizability
import WSC.Shaped.MintingShapedR
import WSC.Shaped.MintingShapedRIdx
import WSC.Shaped.MintingLocalShapedR
import WSC.Shaped.MintingLocalShapedRIdx
import WSC.Shaped.MintingDelegateShapedR
import WSC.Shaped.SeizeShapedR
import WSC.Props.Shaped.P4ShapedR
import WSC.Props.Shaped.P4ShapedRIdx
import WSC.Props.Shaped.P4LocalShapedR
import WSC.Props.Shaped.P4DelegateShapedR
import WSC.Props.Shaped.P2ShapedR
import WSC.Props.Shaped.RealizableShapes

-- ═══════════════════════════════════════════════════════════════════════════
-- TASK C4 — a `LeafSet` over a shape class that is NOT EMPTY (audit F1).
-- ═══════════════════════════════════════════════════════════════════════════
-- C1/C2 made the shape classes node-realizable; this is what that buys at the
-- composition.  `WSC/Props/Shaped/RealizableLeaves.lean` builds the SHAPE-T1R
-- shape bridge (`exec_T1R` by `rfl`, `bridge_T1R` by `blaster`), instantiates
-- `Shape := T1RShape hp`, and discharges THREE of the four `LeafSet` fields:
--   * `p1`  from `WSC.P1R_T1` — the PRODUCTION BYTECODE at budget 4400, witness
--           K = 2603, reached through `WSC.LR_BUDGET_global` (non-vacuity proved)
--           and the new bridge.  **The acceptance hypothesis is genuinely used**,
--           which is not true of any other leaf discharge in this library;
--   * `p4`  from the SHAPE (T1R mints nothing, so the fourth custody disjunct
--           holds by computation) — acceptance hypothesis UNUSED, and named `_`;
--   * `nopre` from the SHAPE (T1R registers nothing).
-- `p2` is NOT discharged and is carried as the single remaining hypothesis of
-- `containment_on_realizable_class_of_p2`, i.e. an N = 1 obligation gap.
-- The class is PROVED INHABITED by a node-realizable context
-- (`realizable_inhabitant`, 0 project axioms) — the exact contrast with
-- `ShapeRealizability.t1VacuousLeaves`, whose class is proved EMPTY.
import WSC.Props.Shaped.RealizableLeaves

-- ═══════════════════════════════════════════════════════════════════════════
-- TASK E1 — the LAST leaf hypothesis removed, and one composed result PER
-- PURPOSE FAMILY (audit F1 → N = 0).
-- ═══════════════════════════════════════════════════════════════════════════
-- §10 of `RealizableLeaves.lean` measures the question C4 left open and answers
-- it the honest way round: `p2` is NOT vacuous over `T1RShape`, because SHAPE
-- T1R's SECOND script withdrawal `w1` is free and `WSC.Deployed` is opaque, so
-- nothing says the deployment's seize credential is not it.  The smallest honest
-- variant adds ONE decidable conjunct about the transaction —
-- `NoSeizeWdrl` : the seize credential is not in `txInfoWdrl` — over which `p2`
-- is discharged BY THE SHAPE + the ledger rule (`validScriptInfo`'s rewarding
-- clause: a rewarding script runs only where the transaction withdraws), with
-- the acceptance hypothesis unused and bound as `_`.
-- `containment_on_realizable_class` is then the top claim with NO leaf
-- hypothesis at all, over a class that still contains the certified
-- node-realizable SHAPE-T1R witness — at the SAME 28 project axioms.
-- `RealizableLeavesS1R.lean` is the seize-purpose counterpart, where the ratio
-- is the same but the LOAD-BEARING LEAF IS THE OTHER ONE: `p2` from the
-- production `programmableSeize` bytecode at 3800 (`bridge_S1R` +
-- `WSC.LR_BUDGET_seize`, the first use of that bridge anywhere), `p1`/`p4`/
-- `nopre` by the shape.  ONE of four leaves is bytecode on each side.
import WSC.Props.Shaped.RealizableLeavesS1R

-- ═══════════════════════════════════════════════════════════════════════════
-- TASK E4 — THE SHAPE-COVERAGE QUESTION, stated and answered NEGATIVELY (F2).
-- ═══════════════════════════════════════════════════════════════════════════
-- `WSC/Coverage.lean` writes down what it would MEAN for a finite family of
-- shapes to cover all transactions of a bounded size (`Covers`), and then
-- refutes it for the twelve node-realizable shapes of C1/C2 — at SHAPE T1R's
-- OWN size — with three machine-checked witnesses that are
--   * `validRewardingContext` AND `redeemersExactAllPlutus` (the campaign's own bar),
--   * ACCEPTED by the production `programmableLogicGlobal` bytecode, and
--   * halting in exactly 2,603 CEK steps, i.e. indistinguishable from the
--     shape's own certified inhabitant by the machine.
-- It also records the one property that needs NO coverage argument (P3, proved
-- over a fully symbolic context) and the enumeration arithmetic that rules the
-- enumeration route out (3.05 × 10^14 skeletons at that bound).  Prose,
-- costings and the recommendation: `WSC/COVERAGE.md`.
import WSC.Coverage

-- ═══════════════════════════════════════════════════════════════════════════
-- TASK R1 — THE TWO RETRACTION CERTIFICATES.
-- ═══════════════════════════════════════════════════════════════════════════
-- Imported LAST because they are stated against the SHAPED results above (the
-- global one needs `WSC.P1RShapedWitness.ctxSOwnMisindexed`).  Between them they
-- are the machine-checked reason the library declares two fewer axioms than it
-- did, and they are deliberately in the default build so that the reason is a
-- measurement in the log rather than a sentence in a changelog:
--
--   * `WSC/Model/GlobalModelRefuted.lean` — `globalModel_faithful` refuted
--     TWICE.  SEMANTIC (finding F24): the model ACCEPTS `ctxSOwnMisindexed`
--     while the real compiled `programmableLogicGlobal` reaches `State.Error`
--     with 20,000 steps available, so the model is UNSOUND, not conservative,
--     at the indexed owner check PR #112 introduced.  BUDGET: the model accepts
--     `transfer-member-single-policy`, whose run costs K = 2,782 (pinned
--     two-sided here), against the axiom's own 1,600-step meter — a defect of
--     the axiom's statement that predates PR #112.
--   * `WSC/Model/SeizeModelRefuted.lean` — `seizeModel_faithful` refuted by ONE
--     context on which the real `programmableSeize` halts and `seizeModel`
--     rejects, the two differing in a single lovelace leaf (the ada top-up #112
--     legalised), plus `no_faithful_bridge`, which refutes the axiom's
--     proposition outright so it cannot be re-added.
import WSC.Model.GlobalModelRefuted
import WSC.Model.SeizeModelRefuted
