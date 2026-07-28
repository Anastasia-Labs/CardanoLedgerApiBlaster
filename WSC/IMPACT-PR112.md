# IMPACT OF wsc-poc PR #112 ON THIS LIBRARY — the authoritative classification

Task **N1**, 2026-07-28. Written against CardanoLedgerApiBlaster
`wsc-containment-proofs` @ `e5b08dd` and wsc-poc `main` @
`2306678fb03b615d4e58ae207e3eccf9b3676b9b`.

This file is the single source of truth for *what survives PR #112 and what does
not*. The reprove units work from it. `WSC/AUDIT.md`, `WSC/STATUS.md`,
`WSC/README.md`, `WSC/EXEC-SUMMARY.md`, `WSC/SHAPING-RESULTS.md`,
`WSC/COVERAGE.md`, `WSC/SHAPE-BRIDGE.md` and `WSC/goldens/K-MEASUREMENTS.md` all
still describe the **pre-#112** state and must be read with this file in hand
until the final unit reconciles them.

---

## §0 THE ONE-PARAGRAPH VERSION

wsc-poc PR #112 changed **three of the four** production validators. Minting is
byte-identical; base, global and seize are not. Every UPLC-level result in this
library about base, global or seize — theorem, vacuity probe, CEK witness, K
measurement, shape bridge, golden — is now about bytecode that is not on `main`.
**P4 and P4a survive completely**, with all six of their shapes and every
artifact attached to them; the check that they are genuinely independent of the
three changed validators was run and is recorded in §4.1. Two of the three
changed validators additionally hit **new substrate blockers** that must be
cleared before any reprove can start: the new seize flat **does not decode** and
the new global flat **does not prep at 1600** (§6).

---

## §1 THE BYTECODE DELTA — measured, not assumed

`sha256` of the `cborHex` field of
`generated/scripts/unapplied/prod/<name>.json`:

| validator | `f918ec6` (#110) | `2306678` (#112) | |
|---|---|---|---|
| `programmableLogicBase` | `1881821b7a2c…` | `a9e7364b519a…` | **CHANGED** (260 → 192 hex chars) |
| `programmableLogicGlobal` | `ddd6f7df4278…` | `eed62d595f56…` | **CHANGED** (6880 → 5624) |
| `programmableSeize` | `289e9e8d18b8…` | `350b58d7b322…` | **CHANGED** (3932 → 2594) |
| `programmableTokenMinting` | `7274240514ff…` | `7274240514ff…` | **byte-identical** |

Source of the change, all in
`src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs`
(812 changed lines; `Issuance.hs`, `PTokenDirectory.hs` and `ProtocolParams.hs`
are byte-identical between the two refs, which is why minting is):

* **base** — rewritten AND its **redeemer type is new**. `data BaseSpendRedeemer
  = SpendViaGlobal Integer | SpendViaSeize Integer` (:704-707),
  `makeIsDataIndexed [('SpendViaGlobal,0),('SpendViaSeize,1)]` (:709). The body
  (:712-731) reads the redeemer off the `ScriptContext` by hand, the constructor
  tag selects `globalCred` (tag 0) vs `seizeCred` (any other tag — the selector
  is a `pif`, not an exhaustive match), and the integer field indexes the
  credential-sorted withdrawal map, reached via `pdropList 6` on the `TxInfo`
  fields. Parameters unchanged: `(globalCred, seizeCred, ctx)`.
* **global** — `TransferAct` gained a THIRD field of five, `plgrOwnerWdrlIdxs`
  (:1046; Plutarch `pownerWdrlIdxs` :1148). Parameters unchanged.
* **seize** — the per-pair value delta is now computed with PV11/CIP-153 `Value`
  builtins (`pvalueEqualsDeltaCurrencySymbol`, :1727-1745). `PSeizeAct`'s six
  fields are unchanged.

Line-number remap for existing citations (verified by reading both texts):

| what | at `f918ec6` | at `2306678` |
|---|---|---|
| `mkProgrammableLogicBase` sig / lambda | 722 / 723 | **711 / 712** |
| `mkProgrammableLogicGlobal` sig / lambda | 1176 / 1177 | **1180 / 1181** |
| global's `pisRewardingScript` condition | 1254 | **1276** |
| `mkProgrammableSeize` sig / lambda | 1290 / 1291 | **1307 / 1308** |
| seize's `pisRewardingScript` condition | 1321 | **1338** |
| `MintProof` decl / tags | 1036-1039 / 1041-1043 | **1030-1033 / 1035-1037** |
| `PMintProof` | 948-953 | **943-948** |
| `ProgrammableLogicGlobalRedeemer` decl / tags | 1046-1063 / 1066-1068 | **1039-1064 / 1067-1069** |
| `PProgrammableLogicGlobalRedeemer` | 1135-1159 | **1136-1163** |
| "seize no longer reads `pinputIdxs`" note | 1299-1304 | **1316-1320** |

---

## §2 THE CLASSIFICATION RULE

* **SURVIVES** — the artifact's content is about the minting bytecode or about
  nothing executable at all, and it still means what it said.
* **SURVIVES (BUILD-BLOCKED)** — content survives; the module will not compile
  until a break listed in §7 is fixed. This is a mechanical blockage, not a
  soundness one.
* **INVALIDATED** — the artifact is a statement about, or a measurement of, base
  / global / seize bytecode that no longer exists on `main`. It may still be a
  correct statement about the `f918ec6` bytecode; it is not a statement about
  production.
* **STALE** — a transcription of, or a citation into, pre-#112 source. Not
  wrong-as-Lean, but no longer a mirror of anything shipped.
* **NEEDS-REVIEW** — mixed content, or a decision the reprove unit must make.

Reaching rule used mechanically: a module is INVALIDATED if its transitive
`import` closure contains `WSC.Prep.Base`, `WSC.Prep.Global`,
`WSC.Prep.Global1600` or `WSC.Prep.Seize` **and** it asserts something about the
prepped term. Modules that merely inherit such an import through an aggregate
(and assert nothing about it) are called out individually.

---

## §3 MODULE-BY-MODULE

### 3.1 Substrate / preps (`WSC/Prep/*`)

| module | verdict | note |
|---|---|---|
| `Prep/Minting.lean` (600/…) | **SURVIVES** | flat byte-identical; nothing to do |
| `Prep/Minting800.lean` | **SURVIVES** | ” |
| `Prep/Minting900.lean` | **SURVIVES** | ” — this is the prep every surviving shape uses |
| `Prep/Minting1300.lean` | **SURVIVES** | ” |
| `Prep/Base.lean` | **NEEDS-REVIEW** | re-points at the new flat automatically. MEASURED: decodes ✅, preps at 600 ✅ (`lake build WSC.Prep.Base`, 22.8 s cold). Docstring cites `:722/:723` → must become `:711/:712`, and the "base never reads its redeemer" framing is now FALSE. |
| `Prep/Global.lean` | **NEEDS-REVIEW** | decodes ✅, preps at 600 ✅ (2.5 s). Citations `:1176/:1177/:1254` → `:1180/:1181/:1276`. The 600 prep was already known-vacuous, so nothing is proved on it. |
| `Prep/Global1600.lean` | **BROKEN** | decodes ✅ but the `#prep_uplc` at 1600 **fails in the kernel** — see §6.2. Blocks every `WSC/Shaped/Global*`. |
| `Prep/Seize.lean` | **BROKEN** | the new flat **does not decode** — see §6.1. Blocks everything seize. |

### 3.2 Bytecode-independent leaves

| module | verdict | note |
|---|---|---|
| `Shaped/Shape.lean` | **SURVIVES** | shape helper definitions, no bytecode, no redeemer |
| `Realizability.lean` | **SURVIVES** | Conway exact-redeemer machinery (`redeemerCoverage` etc.); ledger-side only |
| `Redeemer.lean` | **RE-BASED (this task)** | new `BaseSpendRedeemer`; `TransferAct` 4 → 5 fields; `SeizeAct` verified unchanged. Cited at `2306678`. |
| `Spec.lean` | **NEEDS-REVIEW (BUILD-BLOCKED)** | ground-truth vocabulary; unaffected in meaning, but `mintProofsOf` pattern-matches `TransferAct` with 4 fields (`WSC/Spec.lean:91`) and no longer compiles. It also has no vocabulary yet for the new base redeemer. See §7. |

### 3.3 The keystone and the base path

| artifact | verdict | reason |
|---|---|---|
| `Props/P3_Base.lean` — `P3_base_requires_global_or_seize` | **INVALIDATED** | statement about `appliedBase.prop` of the OLD base bytecode |
| `Props/P3_Base.lean` — `P3_base_negative_control` (vacuity probe) | **INVALIDATED** | probe at the old prep term |
| `Props/P3_Base.lean` — `P3Witness.*` (ctx, `exec_accepts`, `prop_accepts`, K = 208) | **INVALIDATED** | the witness context carries redeemer `()`; the new base reads its redeemer and errors on `Constr 0 []` (the `pasConstr`/`phead` walk at `:721`/`:729` has no field to read). Expect the witness to REJECT, not merely to cost differently. |
| `Props/P3_BaseRun.lean` (`…_run`, `P3_run_negative_control`, `propRun_base_600`) | **INVALIDATED** | same statement on `Runs.baseRun 600` |
| `Shaped/BaseShaped.lean` (SHAPE B1) | **INVALIDATED** | shape's redeemer is `()`; see above |
| `Shaped/Calib/P3Shaped.lean`, `Shaped/Calib/P3Unshaped.lean` | **INVALIDATED** | calibration measurements of the old base |
| `Shaped/Probe/B1Accept.lean`, `BasePrepUnshaped.lean`, `BridgeProbe{,3,4,5}.lean`, `BridgeProbe2FAILS.lean`, `BridgeProbe7.lean` | **INVALIDATED** | all probe the old base prep (`BridgeProbe7` also the old global) |
| `Goldens/Witnesses.lean` | **INVALIDATED** | imports `Prep.Base` + `Props.P3_Base`; ties the base goldens to the old prep |

**The base path is the worst-hit, and not only because the bytecode moved: its
REDEEMER TYPE changed.** Every base artifact assumes a `()` redeemer. A reprove
must (a) put a `BaseSpendRedeemer` in the shape, (b) put the corresponding
`Rewarding` entry in the withdrawal map at the index the redeemer names, and
(c) re-derive K. P3's old headline — "an accepted base spend requires the global
or seize credential in `wdrl`" — should still be TRUE of the new base, and is
now *cheaper* to state (one indexed lookup instead of a scan), but it is a new
proof.

### 3.4 The global / transfer path

| artifact | verdict |
|---|---|
| `Props/P1_Transfer.lean` — `P1_bytecode_of_P1_model`, `P6_bytecode_of_P6_model`, `P1_negative_control_model_rejects_violation` | **INVALIDATED** |
| `Props/P1_Transfer.lean` — the pure model lemmas (`accum_lookup`, `pathC_sound`) | **STALE** (model is a pre-#112 transcription; the lemmas are true *of the model*) |
| `Props/P5_NonMember.lean` — `P5_exists_of_indexed`, `P5_groundtruth_of_indexed`, and the `.TransferAct _ _ _ i` reader at `:348` | **INVALIDATED** (+ build-blocked, §7) |
| `Props/P6_Member.lean` | **INVALIDATED** |
| `Props/Shaped/P1Shaped.lean` (`P1_T1`, `P1_T2`, negative control, `P1ShapedWitness.*`, `K_T1_is_2603`, `K_T2_is_3572`) | **INVALIDATED** |
| `Props/Shaped/P1ShapedR.lean` (`P1R_T1`, `P1R_T2`, `P1R_T6`, `P1R_T7`, negative control, all four `exec_accepts_*`, `K_T1R/T2R/T6R/T7R`) | **INVALIDATED** |
| `Props/Shaped/P5Shaped.lean`, `P5ShapedR.lean` | **INVALIDATED** |
| `Props/Shaped/P6Shaped.lean`, `P6ShapedR.lean`, `P6Bridge.lean` | **INVALIDATED** |
| `Props/Shaped/GlobalRealizability.lean` — `g1R/g6R/t1R/t2R/t6R/t7R_class_covered`, `…_class_coverage`, `…_realizable` | **INVALIDATED** — the class-level `redeemerCoverage` halves are ledger-side and could be salvaged, but every point-level inhabitant carries a 4-field `TransferAct`, which the new global cannot decode, and each `…_realizable` conjoins real-CEK acceptance |
| `Shaped/GlobalShaped.lean`, `GlobalShapedIdx.lean`, `GlobalShapedR.lean`, `GlobalShapedRPrep.lean`, `GlobalMemberShaped.lean`, `GlobalMemberShapedRPrep.lean`, `GlobalShapedP1.lean`, `GlobalShapedP1Agg.lean`, `GlobalShapedP1Out.lean`, and the six `GlobalShapedP1*Prep.lean` | **INVALIDATED** (+ build-blocked twice: 4-field `TransferAct`, and `Prep.Global1600`) |
| `Shaped/Probe/G1Witness.lean`, `G1K.lean`, `G2Probe.lean`, `G3Probe.lean`, `G6Diag.lean`, `G6Vacuous2500.lean`, `GPrep2500.lean`, `GPrep4000.lean`, `T1Probe.lean`, `T4Probe.lean`, `T6Probe.lean`, `T3PrepFAILS.lean`, `T4PrepFAILS.lean`, `UnshapedCost.lean` | **INVALIDATED** |
| `Shaped/Probe/P1Axioms.lean`, `V3Axioms.lean` (global half), `Axioms.lean` (base/global halves) | **INVALIDATED** — axiom censuses of dead declarations |

**Every global shape carries a 4-field `TransferAct` and is therefore not merely
un-reproved but UNBUILDABLE against the new bytecode**: PlutusTx's generated
decoder for a 5-field record rejects a 4-field `Constr 0`. A reprove must add
`ownerWdrlIdxs` to each shape's redeemer skeleton *and decide what it should
contain*, because it is now a load-bearing witness — the transfer validator
verifies owner withdrawals at these indices instead of scanning for them, so an
empty list is not a neutral choice for any shape with a script-owned input.

### 3.5 The seize path

| artifact | verdict |
|---|---|
| `Props/P2_Seize.lean` — `P2a_bytecode`, `P2b_model_implies_bytecode`, `seizeRun_gives_walk`, `accepting_goldens_satisfy_both_conjuncts`, `rejecting_golden_is_the_negative_control` | **INVALIDATED** |
| `Props/P2_Seize.lean` — the pure model lemmas (`valueDelta_dropCS`, `seizeWalk_preserves`, `tokensContain_unsound_*`, …) | **STALE** — they are lemmas about `Model/SeizeModel`, which transcribes the OLD hand-rolled sorted walk. #112 replaced that walk with builtin `Value` arithmetic, so the model is no longer a mirror; several of its lemmas (notably the duplicate-name / unsorted unsoundness results) are about a walk the production code no longer performs. |
| `Props/Shaped/P2Shaped.lean` (`P2a_shaped_structure`, `P2b_shaped_containment`, `P2_shaped`, both negative controls, `P2ShapedWitness.*`, K = 3004/3328) | **INVALIDATED** |
| `Props/Shaped/P2ShapedR.lean` (SHAPE S1R) | **INVALIDATED** |
| `Shaped/SeizeShaped.lean`, `SeizeShapedR.lean` | **INVALIDATED** as theorems; **the shape SKELETON is reusable** — `SeizeAct`'s six fields are unchanged, so S1/S1R are the only changed-validator shapes whose `Data` skeleton is still well-typed against `main` |
| `Shaped/Probe/S1K.lean` | **INVALIDATED** |
| `Model/SeizeModel.lean`, `Model/SeizeDiff.lean` | **STALE** (see §4.4) |

### 3.6 The minting path — **SURVIVES, in full**

| artifact | verdict |
|---|---|
| `Props/P4_Minting.lean` (P4, P4a, `P4Witness.*`, `exec_rejects_at_600` / `accepts_at_800` / `accepts_at_900`, the golden pins) | **SURVIVES** |
| `Props/Shaped/P4Shaped.lean`, `P4ShapedIdx.lean`, `P4ShapedR.lean`, `P4ShapedRIdx.lean` (M1/M2, M1R/M2R) | **SURVIVES** |
| `Props/Shaped/P4LocalShaped.lean`, `P4LocalShapedR.lean` (L1/L2, L1R/L2R) | **SURVIVES** |
| `Props/Shaped/P4DelegateShaped.lean`, `P4DelegateShapedR.lean` (DT1/DS1, DT1R/DS1R) | **SURVIVES** |
| `Shaped/MintingShaped.lean`, `MintingShapedIdx.lean`, `MintingShapedR.lean`, `MintingShapedRIdx.lean` | **SURVIVES** |
| `Shaped/MintingLocalShaped.lean`, `MintingLocalShapedIdx.lean`, `MintingLocalShapedR.lean`, `MintingLocalShapedRIdx.lean` | **SURVIVES** |
| `Shaped/MintingDelegateShaped.lean`, `MintingDelegateShapedR.lean` | **SURVIVES** — see §4.1, this is the one that needed checking |
| `Shaped/Probe/M1K.lean`, `MPrep1700.lean`, `MPrep2500.lean`, `L1K.lean`, `L1Probe.lean`, `L2Probe.lean`, `L2Reg.lean`, `L2RProbe.lean`, `DTDSK.lean`, `DTDSProbe.lean`, `DSRK.lean`, `BridgeProbe6.lean` | **SURVIVES** |
| the four `programmableTokenMinting.*` goldens and their `applied` flats | **SURVIVES** |
| `K_mint = 900`, `K_mint_custody = 2500`, and every minting K in `K-MEASUREMENTS.md` | **SURVIVES** |

Caveat, mechanical only: several of these import `WSC.Spec`, which is
build-blocked by §7 until one pattern is widened. Nothing about their content
depends on it.

### 3.7 Aggregates, bridges, composition

| module | verdict | note |
|---|---|---|
| `Runs.lean` | **NEEDS-REVIEW** | the four definitions `baseRun/mintingRun/globalRun/seizeRun` are *definitions* and automatically re-point at the new flats — that is the right behaviour and nothing needs editing. But every FACT proved about `baseRun`/`globalRun`/`seizeRun` elsewhere is invalidated, and `seizeRun` will not elaborate at all until the decode blocker clears. |
| `Honest.lean` | **NEEDS-REVIEW** | the `LR_*` axioms are statements about arbitrary bytecode and survive as axioms. The **published K table** (`Honest.lean:997-1003`) is a measurement table: the `K_mint`/`K_mint_custody` rows survive; `K_base = 600`, `K_global_nonmember = 1600`, `K_global_member = 3300`, `K_global = 4400`, `K_seize = 3800` and every "measured accepting step count" beside them are **INVALIDATED** and must be re-measured. The `DIRWF` axioms are unaffected. |
| `Composition.lean` | **SURVIVES as a reduction, INVALIDATED as a discharge record** | §7's `preservation` and §8's `top_claim` are proved from explicit hypotheses and do not name any bytecode, so the reduction stands. §9's DISCHARGE STATUS — which instantiates each `LeafSet` field with a library theorem — cites P1/P2/P3/P5/P6 results and is now wrong wherever it does. `baseNonVacuous` and the seize/global non-vacuity fields are INVALIDATED; `mintingNonVacuous` survives. |
| `Props/Shaped/NonVacuity.lean` | **SPLIT** | `mintingNonVacuous_at_2500` **SURVIVES**; `globalNonVacuous_at_1600`, `globalNonVacuous_at_3300`, `globalNonVacuous_at_4400`, `seizeNonVacuous_at_3800` **INVALIDATED** |
| `Props/Shaped/RealizableShapes.lean` | **SPLIT** | the P4/P4a shape-realizability results **SURVIVE**; it also imports `P2Shaped`/`P2ShapedR`, so its seize rows are **INVALIDATED** and the module is build-blocked by them |
| `Props/Shaped/ShapeRealizability.lean` | **SPLIT** | the minting-shape emptiness/realizability results survive; the `GlobalShaped*`/`SeizeShaped` rows are INVALIDATED |
| `Props/Shaped/RealizableLeaves.lean` | **INVALIDATED** | consumes `P1ShapedR` + `GlobalRealizability` |
| `Props/Shaped/RealizableLeavesS1R.lean` | **INVALIDATED** | consumes `P2ShapedR` |
| `ShapeBridge.lean` | **SPLIT** — see §5 | |
| `Coverage.lean` | **INVALIDATED** — see §4.3 | |
| `Imports.lean`, `WSC.lean` | **NEEDS-REVIEW** | pure aggregate roots; they will not build while `Prep.Seize`/`Prep.Global1600` are broken |
| `Model/GlobalModel.lean`, `Model/Ground.lean`, `Model/GlobalGoldens.lean`, `Model/SeizeModel.lean`, `Model/SeizeDiff.lean` | **STALE** — see §4.4 | |
| `Goldens/Vectors.lean`, `Decode.lean`, `Terms.lean`, `TermsCheck.lean`, `Audit.lean` | **SPLIT** | the decoders and the audit machinery survive; 9 of the 13 vectors they carry are pre-#112 (§8) |
| `Goldens/RedeemerGate.lean` | **SPLIT (BUILD-BLOCKED)** | the 4 minting gate theorems and the 2 datum gates **SURVIVE**. `base_redeemers_are_unit` (:86) is **INVALIDATED** — the base redeemer is no longer `()`. The three `transfer_*` theorems are **INVALIDATED** and do not compile (4-field `TransferAct`). The three `seize_*` theorems survive *as encoding facts* (`SeizeAct` is unchanged) but their goldens are pre-#112 contexts. |
| `Goldens.lean`, `Goldens/Witnesses.lean` | **INVALIDATED** | `Witnesses` imports `Prep.Base` + `P3_Base` |

---

## §4 THE FOUR CHECKS THE TASK ASKED FOR

### 4.1 (i) Are the P4 / P4a artifacts really independent of the three changed validators? — **YES, verified two ways**

**Import-closure check.** The transitive `import` closure of every P4 artifact
was computed. `Props/P4_Minting.lean`, all eight `Props/Shaped/P4*.lean`, all ten
`Shaped/Minting*.lean`, and the twelve minting probes reach **`WSC.Prep.Minting`,
`Minting800`, `Minting900` and nothing else** — no `Prep.Base`, no `Prep.Global`,
no `Prep.Global1600`, no `Prep.Seize`. So no P4 artifact ever preps or executes
another validator's bytecode; the only bytecode under any of them is the
byte-identical minting flat.

**Redeemer-encoding check** (the non-obvious half, since the minting shapes put
global/seize *credentials* in withdrawal maps and, in one case, a *global
redeemer* in the redeemer map):

* SHAPE **DS1 / DS1R** really do embed a `PLGRedeemer.SeizeAct` value —
  `dsSeizeRedeemer` at `WSC/Shaped/MintingDelegateShaped.lean:180` and
  `MintingDelegateShapedR.lean:200`, both `SeizeAct sIdx [] 0 0 0 0`, audited to
  `Constr 1 [I sIdx, List [], I 0, I 0, I 0, I 0]`. **`SeizeAct`'s six fields are
  unchanged by #112** (verified field by field against `2306678`:1056-1064), so
  these encodings are still exactly right and DS1/DS1R survive intact.
* SHAPE **DT1** has a ONE-entry redeemer map, `[(Minting ownCS,
  dtShapedRedeemer)]` (`MintingDelegateShaped.lean:132`) — no global redeemer at
  all.
* SHAPE **DT1R** has a three-entry map whose two `Rewarding` entries are
  **opaque free bytestrings**, `Data.B mlRed` / `Data.B glRed`
  (`MintingDelegateShapedR.lean:121-123`). They are deliberately not
  `TransferAct` values, so the 4 → 5 field change cannot touch them.
* No minting shape contains a `TransferAct` anywhere. (`grep` over
  `WSC/Shaped/Minting*` finds `TransferAct` only in prose.)

Conclusion: **P4, P4a and their six shapes M1R, M2R, L1R, L2R, DT1R, DS1R —
with every witness, probe, K measurement and realizability theorem attached to
them — SURVIVE UNTOUCHED.** This confirms the expectation in the task brief.

### 4.2 (ii) Which `ShapeBridge` results die?

See §5 — **10 of 16 die, 6 survive.**

### 4.3 (iii) Is `WSC/Coverage.lean`'s refutation invalidated? — **YES**

`Coverage.lean` proves `not_covers_at_T1R_size` and
`not_covers_with_three_reference_inputs`: the thirteen-shape family does not
cover a size bound. Its own header states the load-bearing property of the
witnesses (§"WHAT IS PROVED HERE", item 3): each witness is
`validRewardingContext` **and** `redeemersExactAllPlutus` **and "is ACCEPTED by
the real compiled global validator in `Runs.globalRun 4400`, by `native_decide`
on the CEK machine"**. That third conjunct is a statement about the OLD global
bytecode, and the witnesses are rewarding contexts carrying a 4-field
`TransferAct`, which the new global cannot even decode. So:

* the two `not_covers_*` theorems are **INVALIDATED**;
* the family definition is **INVALIDATED as a family**: 7 of its 13 members
  (`rangeG1R`, `rangeG6R`, `rangeT1R`, `rangeT2R`, `rangeT6R`, `rangeT7R`,
  `rangeS1R`) are ranges of shape builders that must be re-cut, and the first
  six are ranges of contexts the new global rejects by construction;
* the 6 minting members (`rangeM1R`, `rangeM2R`, `rangeL1R`, `rangeL2R`,
  `rangeDT1R`, `rangeDS1R`) and their `inv_*` lemmas **SURVIVE**;
* `p3_lives_over_a_covering_class` / `unshaped_covers` — the module's single
  most-quoted sentence, "P3 needs no coverage argument at all" — is
  **INVALIDATED**, because it is about P3, which is about the old base;
* `wdrl_range_char` **SURVIVES**: it is a pure characterisation of the range of
  `p1ShapedWdrl`, with no bytecode in it. It is the one part of the module a
  reprove can lift unchanged.

Note the direction of the error, which matters for how loudly this must be
flagged: a *refutation* of coverage is not made false by shrinking the family —
but this one is stated over a specific 13-member family and leans on
real-bytecode acceptance, so it must be re-proved rather than re-labelled.

### 4.4 (iv) Are `WSC/Model/*` stale? — **YES. Plainly: they are transcriptions of pre-#112 code.**

* `Model/GlobalModel.lean` is a hand transcription of `mkProgrammableLogicGlobal`
  as it stood at `f918ec6`. It decodes a **4-field** `TransferAct` at
  `WSC/Model/GlobalModel.lean:667` (`| some (.TransferAct proofs wdrlIdxs
  mintProofs paramsRefIdx)`), which is both a compile break and the visible tip
  of the problem: the model has **no notion of `ownerWdrlIdxs`**, so it cannot
  model the owner-withdrawal check the production validator now performs. Every
  "faithfulness" claim resting on it is void.
* `Model/Ground.lean`, `Model/GlobalGoldens.lean` inherit that staleness.
* `Model/SeizeModel.lean` transcribes the OLD hand-rolled sorted lockstep walk.
  #112 replaced it wholesale with builtin `Value` arithmetic
  (`pvalueEqualsDeltaCurrencySymbol`, :1727-1745), and along the way changed the
  *shape* of the check: "only `progCS` may differ" is now the structural
  statement "the canonical difference has at most one entry", plus an explicit
  ada-top-up allowance and a positive-quantity non-contamination shortcut. The
  model does not contain any of that. Its own `:511-516` note about
  `PTransferAct` rejection remains true but is a detail.
* `Model/SeizeDiff.lean` compares the model against goldens that are themselves
  pre-#112.

**Recommendation, stated so the reprove units do not have to re-derive it:** do
not patch the models field by field. `Model/SeizeModel.lean` in particular is
now a model of an algorithm that was deleted. Either re-transcribe from
`2306678` or drop the model route for seize and state P2 directly at UPLC, which
is what `Props/P3_BaseRun.lean` demonstrated is affordable for a keystone-grade
goal.

---

## §5 SHAPES AND SHAPE BRIDGES

`WSC/ShapeBridge.lean` proves 16 `inputs_X` / `exec_X` / `bridge_X` triples.

| shape | validator | verdict |
|---|---|---|
| **B1** | base | **INVALIDATED** (redeemer `()`) |
| **M1**, **M2** | minting | **SURVIVE** |
| **L1**, **L2** | minting | **SURVIVE** |
| **DT1**, **DS1** | minting | **SURVIVE** |
| **G1**, **GIdx**, **GNIdx**, **G6** | global | **INVALIDATED** |
| **T1**, **T2**, **T6**, **T7** | global | **INVALIDATED** |
| **S1** | seize | **INVALIDATED** |

**6 of 16 bridges survive; 10 die.** The three `control_*` definitions for B1 and
T1 die with them; `control_M1_*` survive.

The 13 re-cut node-realizable shapes of `Coverage.lean` / the C1-C2 re-cut:

| shape | verdict | note |
|---|---|---|
| M1R, M2R, L1R, L2R, DT1R, DS1R | **SURVIVE** | minting; §4.1 |
| G1R, G6R, T1R, T2R, T6R, T7R | **INVALIDATED** | global; each carries a 4-field `TransferAct` and is now *unbuildable*, not merely unproved |
| S1R | **INVALIDATED as a theorem, SKELETON REUSABLE** | `SeizeAct` unchanged, so the `Data` skeleton still type-checks against `main`; only the bytecode moved |

Pre-re-cut ancestors (B1, G1, G2, G3, G6, T1-T7, S1) die with their descendants.

---

## §6 TWO NEW SUBSTRATE BLOCKERS — measured in the N1 workspace copy

These are defects in the pinned PlutusCoreBlaster / Blaster, not in this
library, and they gate the reprove work.

### 6.1 (call it **D7**) The new seize flat does not decode

```
$ lake build WSC.Prep.Seize
error: WSC/Prep/Seize.lean:26:0: Decoding error in
       'WSC/flats/programmableSeize.flat': Could not decode program!
error: WSC/Prep/Seize.lean:44:24: unknown constant 'programmableSeize'
```

Cause: PR #112's seize path calls `pscaleValue`, which is
`punsafeBuiltin PLC.ScaleValue` (`Plutarch/Builtin/Value.hs:164-167` in the
pinned plutarch source; used at `ProgrammableLogicBase.hs:1744`). `ScaleValue` is
**not** in PlutusCoreBlaster's `builtinTable`, which ends at `(99, .UnValueData)`
(`PlutusCore/UPLC/FlatEncoding/Basic.lean:296-311`). Fixing it needs (a) the flat
tag read off plutus-core's `instance Flat DefaultFun` — **read it, do not guess
it; the neighbouring 89-91 are present-but-commented in PCB, so "next free
number" is not a safe inference** — and (b) a CEK denotation. Until then **no
seize result of any kind is statable at `2306678`.**

### 6.2 (call it **D8**) The new global flat decodes but does not prep at 1600

```
$ lake build WSC.Prep.Global1600            # 8 m 9 s
info:  WSC/Prep/Global1600.lean:66:0: Successfully decoded double CBOR hex …
error: WSC/Prep/Global1600.lean:88:0: (kernel) application type mismatch
  Blaster.dite' (Bool.true = …eqDataMap tail✝ [(Data.B bs, Data.Map [])])
    (fun x => State.Halt (VCon Const.Unit)) fun x => State.Error
argument has type
  Bool.false = …eqDataMap tail✝ [(Data.B bs, Data.Map [])] → State
but function has type
  (¬Bool.true = …eqDataMap tail✝ [(Data.B bs, Data.Map [])] → State) → State
error: build failed
```

A `Bool.false = _` / `¬ Bool.true = _` polarity mismatch produced by Blaster's
elaboration-time optimizer (`Optimize.main`) on the new bytecode; the error is
raised twice and comes from the KERNEL, i.e. the elaborated `prop` declaration is
ill-typed. The 600 prep of the same flat is fine. Because **every**
`WSC/Shaped/Global*` module imports `WSC.Prep.Global1600`, this blocks the whole
global reprove until it is fixed in Blaster.

---

## §7 COMPILE BREAKS HANDED TO THE REPROVE UNITS

`WSC/Redeemer.lean`'s `TransferAct` now has five fields. Every construction or
pattern with four arguments is a hard compile error. Complete list, from a
`grep` over `WSC/**/*.lean` at `e5b08dd` (docstrings excluded):

| file:line | site | owner |
|---|---|---|
| `WSC/Spec.lean:91` | `\| some (.TransferAct _ _ ms _) => some ms` — needs one more `_` (mintProofs is still the field *before* last) | **UNASSIGNED — see below** |
| `WSC/Model/GlobalModel.lean:667` | `\| some (.TransferAct proofs wdrlIdxs mintProofs paramsRefIdx)` | global reprove unit |
| `WSC/Props/P5_NonMember.lean:348` | `\| some (.TransferAct _ _ _ i) => some i` | global reprove unit |
| `WSC/Shaped/GlobalShaped.lean:101` | `TransferAct [] [] [NonMember 1] 0` | global reprove unit |
| `WSC/Shaped/GlobalShapedIdx.lean:38` | `TransferAct [] [] [NonMember nIdx] pIdx` | global reprove unit |
| `WSC/Shaped/GlobalMemberShaped.lean:117` | `TransferAct [] [] [Member] 0` | global reprove unit |
| `WSC/Shaped/GlobalShapedP1.lean:172, 184` | `TransferAct [1] [1] [] 0`, `TransferAct [1] [1] [Member] 0` | global reprove unit |
| `WSC/Goldens/RedeemerGate.lean:156, 160, 166, 170, 183, 187` | six `TransferAct [..] [..] [] 0` | golden unit (N2) |

**`WSC/Spec.lean:91` needs an owner and has none.** It is not in `WSC/Props`,
`WSC/Shaped` or `WSC/goldens`, so N1 did not touch it, but it is imported by the
**surviving** P4 chain, so the minting results do not build until it is widened.
The fix is forced and is one token:

```lean
  | some (.TransferAct _ _ _ ms _) => some ms
```

Whichever unit reaches it first should apply exactly that and say so. N1
deliberately did not, to keep three parallel units off one line; flagging it here
rather than silently fixing it is the point.

`WSC/Spec.lean` will additionally need NEW vocabulary for the base redeemer
(there is none today, because the old base redeemer was `()`); that is a design
decision for the base reprove unit, not a mechanical fix.

---

## §8 GOLDENS (N2 owns these; classification only)

13 vectors in `WSC/goldens/`, each with a matching `applied/*.flat`:

| vector | verdict |
|---|---|
| `programmableTokenMinting.mint-local-registered-by-ref` | **SURVIVES** |
| `programmableTokenMinting.mint-local-empty-withdrawals-REJECT` | **SURVIVES** |
| `programmableTokenMinting.mint-burnonly` | **SURVIVES** |
| `programmableTokenMinting.mint-delegate-transfer-topup` | **SURVIVES** |
| `programmableLogicBase.base-spend-transfer-tx` | **INVALIDATED** — redeemer `()`; the new base reads its redeemer |
| `programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT` | **INVALIDATED** — same; note it may still REJECT, but for a different reason, which is not the same golden |
| `programmableLogicGlobal.transfer-member-single-policy` | **INVALIDATED** — 4-field `TransferAct` |
| `programmableLogicGlobal.transfer-nonmember-covering-node` | **INVALIDATED** — ” |
| `programmableLogicGlobal.transfer-mixed-many-policies` | **INVALIDATED** — ” |
| `programmableLogicGlobal.transfer-containment-violation-REJECT` | **INVALIDATED** — ” |
| `programmableSeize.seize-1-input` | **INVALIDATED** (context/verdict); the *redeemer encoding* it pins is still correct |
| `programmableSeize.seize-1-input-missing-residual-output-REJECT` | **INVALIDATED** (as above) |
| `programmableSeize.seize-2-inputs-partial-with-noise` | **INVALIDATED** (as above) |

`WSC/goldens/applied/*.flat` for the 9 invalidated vectors are applications of
the OLD scripts and are invalidated with them. `WSC/goldens/pre-fix/` is already
historical. `WSC/goldens/K-MEASUREMENTS.md`: every base / global / seize row is
**INVALIDATED**; every minting row **SURVIVES**.

**A note for N2 on regeneration.** `RedeemerGate`'s strongest field-order test is
`transfer_mixed_many_policies`, which works only because the two `[Integer]`
fields carry DIFFERENT lists (`[1,2,3,4,1]` vs `[1,1,1,1,1]`). There are now
**three** adjacent `[Integer]` fields. A regenerated golden must make all three
pairwise distinct, or the gate silently stops being able to catch a permutation
— which is precisely the failure mode `RedeemerGate.lean`'s own header says it
exists to prevent.

---

## §9 WHAT SURVIVES, IN ONE LIST

Properties: **P4, P4a** (and their negative controls, witnesses and K pins).
Shapes: **M1R, M2R, L1R, L2R, DT1R, DS1R** (and their pre-re-cut ancestors M1,
M2, L1, L2, DT1, DS1).
Bridges: **6 of 16** (`M1`, `M2`, `L1`, `L2`, `DT1`, `DS1`).
Goldens: **4 of 13** (all minting).
K constants: **`K_mint = 900`, `K_mint_custody = 2500`**.
Non-vacuity: **`mintingNonVacuous`, `mintingNonVacuous_at_2500`**.
Bytecode-independent machinery: `Shaped/Shape.lean`, `Realizability.lean`,
`Coverage.lean`'s `wdrl_range_char` and the 6 minting `range*`/`inv_*`,
`Composition.lean`'s reduction (`preservation`, `top_claim`) as a reduction,
`Honest.lean`'s `LR_*` and `DIRWF` axioms, `Goldens/Decode.lean`'s decoders,
`Redeemer.lean`'s `MintProof` / `SeizeAct` / `RegWitness` / `MintRedeemer` /
`DirectorySetNode` / `GlobalParams` mirrors.

Everything else listed above is INVALIDATED or STALE and is retained only as a
template. Each such module carries a `⚠️ PRE-#112` marker on its first line
naming this file. **Do not quote a marked module's theorem as a statement about
production.**

---

## §7 UPDATE FROM UNIT N4 (global reprove: P1 / P5 / P6), 2026-07-28

This section supersedes §6's substrate verdicts for the GLOBAL side. Nothing
here changes §1-§5.

### 7.1 D8 IS CLOSED — it was a duplicate of D6

N1 reported D8 (`Prep/Global1600` fails in the kernel after ~8 min, `dite'`
polarity mismatch) as a NEW blocker distinct from D6. It is not: it is D6, on a
bigger term. Both are `Optimize.main` emitting a `Blaster.dite'` whose branch
binder type was `Not`-normalised without the head's `p` following.

Root cause, fix, and the measured before/after table: `WSC/pr/03-blaster-d6-FIX.md`.
The fix is two files in `Lean-blaster` @ `59db213`; **it is unpushed and lives
only in this task's workspace, so every global result below is unreproducible
until it is upstreamed or vendored.**

After the fix `WSC.Prep.Global1600` builds in **1826 s** (30.4 min), and all
seven global shaped preps build in 2-3 s each.

### 7.2 D6's REACH WAS WIDER THAN RECORDED

Before this unit, D6 was documented as blocking SHAPES T3/T4 only (`COVERAGE.md`,
`STATUS.md`). Against the #112 bytecode it also blocked **every shaped prep with
a nonzero mint field** — G1R, G6R, T2R, T7R — because PR #112 moved the mint
merge onto the CIP-153 `punionValue` builtin. Since P5 and P6 are inherently
mint-side, D6 was blocking two of this unit's three properties outright. That is
now fixed.

Not yet re-tested, and worth someone's time: `Probe/T3PrepFAILS.lean` and
`Probe/T4PrepFAILS.lean` are named for a failure the fix may well have removed.
If they now prep, P1's containment dispatch Paths B/C and the input-side
aggregation axis open up.

### 7.3 D9 — NEW, OPEN. It costs the library P6.

`Unexpected smt error: (error "… Overflow encountered when expanding vector")` on
all four solver stanzas over SHAPE G6R. Two hypotheses (the CIP-153 mint merge;
the prep budget) were tested and BOTH REFUTED. Full write-up, bisections and the
next step: `WSC/pr/05-blaster-issue-d9-bv-overflow.md`.

P6's EXECUTABLE evidence is unaffected and was re-run green. It is the
universally quantified theorem and its probes that have no verdict.

### 7.4 D7 (seize flat does not decode) TRANSITIVELY BLOCKS P1 AND P5

Not obvious and worth recording: `Props/P1_Transfer` and `Props/P5_NonMember`
import `WSC.Honest`, which imports `WSC.Runs`, which imports `WSC.Prep.Seize` for
`seizeRun`. So the seize decode failure takes the two global properties down with
it even though neither mentions seize. Unit N5 owns the PCB `ScaleValue` fix.

### 7.5 STRUCTURAL CHANGES MADE HERE

* **`WSC/Prep/GlobalImport.lean` (new)** — the `#import_uplc` plus
  `globalInputs1600`, split out of `Prep/Global1600.lean` so the shaped preps
  stop inheriting the unshaped prep's failures. The shaped preps never used
  `appliedGlobal1600`; this is an isolation, not a weakening.
* **`WSC/Props/Shaped/P6Vocab.lean` (new)** — P6's ground-truth vocabulary
  (`outAtBaseQty`, `inAtBaseQty`) and witness helpers, split out of `P6Shaped`
  so `P6ShapedR` is not held hostage to the INVALIDATED shape's solver results.
  Both modules import it, which keeps the two postconditions structurally the
  same object.
* **`ownerWdrlIdxs = []` in all pre-existing global shapes** — forced, not
  chosen: every one of them witnesses its mini-ledger owner by SIGNATURE, so the
  script arm at `ProgrammableLogicBase.hs:386-393` is never reached. Corroborated
  by all four regenerated transfer goldens carrying `[]`.
* **SHAPE T8R (new)** — `WSC/Shaped/GlobalShapedR.lean` §7 plus
  `Shaped/GlobalShapedP1SOwnPrep.lean`. A mini-ledger input owned by a SCRIPT,
  no signatories, three script withdrawals, `ownerWdrlIdxs = [2]`. It exists
  because otherwise PR #112's most security-relevant new line would be covered by
  nothing — no golden, no shape, no theorem. N2 flagged the same gap on the
  goldens side.
* **Explicit `(timeout: 1500)` on every solver call** in the six global P-modules.
  They had none, and Blaster's default is infinite — a real hang risk now that
  the bytecode moved. Per house rule this is a hang guard, not a soundness hole.

### 7.6 MEASURED K CHANGE

SHAPE G6R witness: **K = 2837 → 2196** (−22.6 %), two-sided
(`halts 2196 = true`, `halts 2195 = false`). In line with N2's golden
measurements. `K_is_2837` in `P6ShapedR` is therefore false and is the
`native_decide` failure at `:253`.
