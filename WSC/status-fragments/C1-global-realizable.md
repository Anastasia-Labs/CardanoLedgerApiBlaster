# C1 — node-realizable re-cut of the GLOBAL validator's shapes; P1/P5/P6 re-proved

Status fragment for task C1 (own unit). Written for C3 to fold into
`WSC/STATUS.md` / `WSC/AUDIT.md` / `WSC/SHAPING-RESULTS.md`; nothing in this file
is authoritative over `WSC/AUDIT.md`.

## THE FINDING THIS UNIT FIXES

`WSC/Props/Shaped/ShapeRealizability.lean` (audit F2) proves every shaped class is
EMPTY as a class of ledger transactions: a one-entry `txInfoRedeemers` map next to
script witnesses (two script-credential withdrawals, and for the P1 shapes a
script-credential INPUT) that Conway UTXOW's `MissingRedeemers` requires to carry
redeemer entries.

## WHAT WAS DONE

Six re-cut shapes in `WSC/Shaped/GlobalShapedR.lean`, each with a redeemer map
that covers every needed script, at the redeemer-map sizes of the real accepting
goldens (`AUDIT.md` §4b). Two levers, both used:

* **(i) drop withdrawal entries the validator never dereferences.** On the
  `PTransferAct` path the validator forces `pfstBuiltin # (phead #
  withdrawalEntries)` (ProgrammableLogicBase.hs:1201) and, on a cache miss,
  `pdropList # wdrlIdx # withdrawalEntries` (:913-915). With
  `transferWdrlIdxs = []` (SHAPES G1/G6) only entry 0 is read, so those shapes
  now carry ONE script withdrawal instead of two — their skeleton is no larger
  than before. With `transferWdrlIdxs = [1]` (the P1 shapes) entry 1 must equal
  the node datum's `transferLogicScript`, a `ScriptCredential`, so it stays a
  script withdrawal and gets its own `Rewarding` entry.
* **(ii) symbolic redeemer VALUES** (`Data.I rBase`, `Data.I rMint`,
  `Data.I rTls`): map length and purpose tags frozen, payloads free.

Redeemer maps are written in CLAB's `ltScriptPurpose` order
(`Spending < Minting < Certifying < Rewarding < …`, audit row M); the only side
condition on the leaves is `w0 < w1`, which `validWithdrawals` already forces.

## BEFORE / AFTER

| property | OLD shape | old verdict | old class | NEW shape | new verdict | new class | witness K / budget |
|---|---|---|---|---|---|---|---|
| P1 base (pure transfer, PATH A) | T1 — 2 script wdrl, **1** redeemer | `✅ Valid` (`P1_T1`) | **EMPTY, unconditional** (`ShapeRealizability.t1_class_is_empty`) | **T1R** — 2 script wdrl, **3** redeemers (`Spending ⟨"",0⟩`, `Rewarding w0`, `Rewarding w1`) | `✅ Valid` (`P1R_T1`) | **REALIZABLE** (`t1R_realizable`, `t1R_class_covered`) | K = **2603**, budget 4400 |
| P1 mint/burn (signed form) | T2 | `✅ Valid` (`P1_T2`) | **EMPTY, unconditional** (`t2_class_is_empty`, proved in this unit) | **T2R** — + `Minting cs`, **4** redeemers | `✅ Valid` (`P1R_T2`) | **REALIZABLE** (`t2R_realizable`) | K = **3572**, budget 4400 |
| P1 output aggregation | T6 | `✅ Valid` (`P1_T6`) | **EMPTY, unconditional** (`t6_class_is_empty`, this unit) | **T6R** — 3 redeemers | `✅ Valid` (`P1R_T6`) | **REALIZABLE** (`t6R_realizable`) | K = **3150**, budget 4400 |
| P1 aggregation + mint (strongest) | T7 | `✅ Valid` (`P1_T7`) | **EMPTY, unconditional** (`t7_class_is_empty`, this unit) | **T7R** — 4 redeemers | `✅ Valid` (`P1R_T7`) | **REALIZABLE** (`t7R_realizable`) | K = **3572**, budget 4400 |
| P5 covering-node (mint-side `NonMember`) | G1 — 2 script wdrl, 1 redeemer | `✅ Valid` (`P5_shaped_indexed`) | **EMPTY under `RedeemerCoverage`** (`g1_class_is_empty_under_coverage`) | **G1R** — **1** script wdrl, **2** redeemers (`Minting cs`, `Rewarding w0`) | `✅ Valid` (`P5R_shaped_indexed`) | **REALIZABLE** (`g1R_realizable`) | K = **1541**, budget 1600 |
| P6 `Member` self-penalization | G6 — 2 script wdrl, 1 redeemer | `✅ Valid` (`P6_shaped_member_adds_to_requirement`) | **EMPTY, UNCONDITIONAL** (`g6_class_is_empty`, this unit, via C3's `LR_REDEEMER_COVERAGE`) | **G6R** — 1 script wdrl, 2 redeemers | `✅ Valid` (`P6R_shaped_member_adds_to_requirement`) | **REALIZABLE** (`g6R_realizable`) | K = **2837**, budget 3300 |

Derived forms also re-proved: `P5R_shaped_exists` (ADDENDUM E3 ∃-form),
`P5R_shaped_groundtruth` (Honest.lean vocabulary, `TS3` only),
`P6R_shaped_member_mint_stays_at_base`.

## THE HEADLINE MEASUREMENT

**Every witness K is UNCHANGED by the re-cut.** The transfer path reads its own
redeemer out of `scriptContextRedeemer` and never dereferences
`txInfoRedeemers`, so enlarging the redeemer map changes no CEK step. Shaped prep
is likewise unaffected: the six new preps cost **1.1-1.5 s each**. The predicted
risk ("the enlarged redeemer map re-hits the solver wall") **did not materialise**
— all 18 new solver queries returned a verdict, none `Undetermined`.

## COORDINATION WITH C3 — the rule landed mid-unit and is USED, not deferred

C3's commits `755d75e`/`c10782a` put Conway's `MissingRedeemers`/`ExtraRedeemers`
into CLAB (`scriptPurposesWitnessed` = the `scriptsNeeded` transcription over all
six sources, `redeemerCoverage`, `noExtraRedeemers`, `redeemersExact`) and into
`WSC/Honest.lean` (LR-CTX audit row S, axiom `LR_REDEEMER_COVERAGE`, corollary
`redeemerCoverage_wdrl`). This unit was re-stated against them:

* `{g1R,g6R,t1R,t2R,t6R,t7R}_class_coverage` — **`redeemerCoverage … = true` for
  EVERY leaf assignment of every re-cut shape**, in CLAB's own vocabulary. This
  is the strongest class-level form of the acceptance criterion, and it also
  discharges the certificate / vote / proposal arms (empty in all six shapes).
* each `*_realizable` theorem now also asserts **`redeemersExact … = true`** at
  its witness — BOTH halves of `hasExactSetOfRedeemers`, so the witnesses carry
  no EXTRA redeemer either (`native_decide`).
* `g6_class_is_empty` is discharged from `redeemerCoverage_wdrl`, so it is
  **unconditional** — the first shape-emptiness result to use C3's axiom rather
  than `ShapeRealizability`'s local `Prop`.

`RedeemerCovered` (the local ∀-form, `GlobalRealizability.lean` §1) is kept as a
readable per-arm restatement and as the form the emptiness proofs consume; it is
a consequence of the CLAB coverage theorems, not an extra assumption.

## CONTROL SETS (all re-run at the new terms and shapes)

* negative control: `P1R_T1_negative_control`, `P5R_shaped_negative_control`,
  `P6R_shaped_negative_control` — all `✅ Valid`;
* tightness: `P1R_T1_tightness`, `P5R_shaped_tightness`, `P6R_shaped_tightness` —
  all `✅ Expected Falsified`;
* **vacuity probe at each theorem's OWN term and shape** (mandatory):
  `P1R_T1/T2/T6/T7_vacuity_probe`, `P5R_shaped_vacuity_probe`,
  `P6R_shaped_vacuity_probe` — all `✅ Expected Falsified`;
* concrete accepting instance through the real CEK with its exact K, per shape;
* excluded-case witnesses re-run: `P1RShapedWitness.exec_rejects_escape` (a
  ledger-legal, redeemer-covered containment violation the bytecode REJECTS) and
  `P6RShapedWitness.exec_rejects_escape_under_member`.

## BUILD

Staged on canonical HEAD **7174e3d** (C3's four commits landed mid-unit and were
merged in, not reverted).
`rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*` then
`lake build WSC WSC.ShapeBridge`: **416 jobs / 105.7 s**, maxRSS 1.64 GB,
**119 solver verdicts (75 Valid + 44 Expected Falsified), zero errors, zero
Undetermined** — i.e. the pre-existing 101 (66+35) plus this unit's 18 (9+9).

## AXIOM CENSUS (printed by `WSC/Props/Shaped/GlobalRealizability.lean` §5)

* the six `*_class_covered` theorems: `propext, Classical.choice, Quot.sound` —
  no project axiom, no `sorryAx`;
* the six `*_realizable` theorems: those plus `Lean.ofReduceBool`,
  `Lean.trustCompiler` (`native_decide` over the real CEK) — no project axiom, no
  `sorryAx`;
* the five re-proved headlines (`P1R_T1/T2/T6/T7`, `P5R_shaped_indexed`,
  `P6R_shaped_member_adds_to_requirement`): `propext, sorryAx,
  Classical.choice, Quot.sound` — `sorryAx` is blaster's `admit`, and **no project
  axiom appears**, exactly as for their SHAPE T1/G1/G6 predecessors;
* the four new emptiness theorems: `Deployed, LR_CTX, LR_SPEND_RUNS_VALIDATOR,
  NodeAcceptsBase, OnChain` (T2/T6/T7) and `OnChain` (G6, plus the
  `RedeemerCoverage` hypothesis as an explicit argument) — identical trust cost to
  `t1_class_is_empty` / `g1_class_is_empty_under_coverage`.

No new `axiom` declaration anywhere (library count unchanged at 50), and no
`sorry` written by hand.

## WHAT IS STILL OPEN AFTER THIS UNIT

1. **`ShapeRealizability.lean`'s conditional results can now be made
   unconditional.** Its `RedeemerCoverage` `Prop` is superseded by C3's
   `LR_REDEEMER_COVERAGE` + `redeemerCoverage_wdrl`; `g6_class_is_empty` in this
   unit shows the one-line pattern. That module is not owned by C1, so
   `g1/l1/m1/s1/dt1_class_is_empty_under_coverage` were left as they are.
   **FOLLOW-UP for its owner.**
2. **Coverage is NECESSARY, not sufficient.** A node-accepted transaction of these
   classes must additionally have the sibling scripts succeed (the base spending
   validator on T1R's input 0, the transfer-logic script at withdrawal entry 1,
   the issuance policy behind a `Minting` entry) and satisfy the protocol
   parameters. Those are separate validators/properties; the realizability
   theorems say so in their docstrings.
3. **Composition is NOT re-done here.** The re-cut classes are now non-empty, so a
   `Shape` instantiation over them is no longer vacuous — but building the
   corresponding `LeafSet` needs the MINTING and SEIZE leaves too (task C2's
   shapes: L1/M1/DT1/DS1/S1 are all still empty), so no composition claim is made
   in this unit. The vacuous `LeafSet` at SHAPE T1 (`t1VacuousLeaves`) stays where
   it is, labelled.
4. `PropExecFaithful` still binds the shaped groups, including these six: the
   theorems' hypothesis is `appliedGlobalShaped*R.prop`, while the realizability
   witnesses execute `.exec`. Unchanged by this unit, and unchanged in kind.
5. **SHAPE T3 (two token names → containment dispatch Paths B/C) is still not
   preppable** — Blaster defect D6, reproduction at
   `WSC/Shaped/Probe/T3PrepFAILS.lean`. So the re-cut inherits Bound 2b: PATH A
   only. Likewise SHAPES T4/T5 (two contributing mini-ledger inputs) remain
   blocked by D6.
6. The OLD shapes and their theorems are KEPT (the emptiness proofs are stated
   over them) and each affected module now carries a
   "⚠ SHAPE-CLASS STATUS (task C1)" banner pointing at its re-cut replacement:
   `WSC/Props/Shaped/{P1Shaped,P5Shaped,P6Shaped}.lean` and
   `WSC/Shaped/{GlobalShapedP1,GlobalShaped,GlobalMemberShaped}.lean`.

## FILES

New:
`WSC/Shaped/GlobalShapedR.lean` (six shapes),
`WSC/Shaped/GlobalShapedRPrep.lean` (G1R @1600),
`WSC/Shaped/GlobalMemberShapedRPrep.lean` (G6R @3300),
`WSC/Shaped/GlobalShapedP1RPrep.lean` (T1R @4400),
`WSC/Shaped/GlobalShapedP1RMintPrep.lean` (T2R @4400),
`WSC/Shaped/GlobalShapedP1ROutPrep.lean` (T6R @4400),
`WSC/Shaped/GlobalShapedP1ROutMintPrep.lean` (T7R @4400),
`WSC/Props/Shaped/P1ShapedR.lean`, `P5ShapedR.lean`, `P6ShapedR.lean`,
`WSC/Props/Shaped/GlobalRealizability.lean` (`RedeemerCovered`, §2 class coverage,
§2b the same in CLAB's vocabulary, §3 the six realizability theorems, §4 the four
emptiness theorems for the retired shapes, §5 axiom census), this fragment.

Modified: `WSC.lean` (imports + the task C1 stanza) and the six banners above.
