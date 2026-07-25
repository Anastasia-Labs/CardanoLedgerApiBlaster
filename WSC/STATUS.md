# WSC containment campaign — AUTHORITATIVE STATUS

**Read this first, then `WSC/AUDIT.md`.** Everything below is machine-checked or
measured *in this repository*, with the file/line or the measurement cited. Where a
result is not there yet, this table says so in those words.

**Revision: this file was rewritten at task A3 (2026-07-25) from an independent
clean-room rebuild at HEAD `80cdac7` on branch `wsc-containment-proofs`, not from any
task report.** It supersedes the U3 revision and the A1/A2 amendments, which are
folded in. The six `WSC/status-fragments/*.md` are merged and superseded (kept as the
per-task record); any disagreement between a fragment and this file is resolved in
favour of this file, and the disagreements are itemised in `WSC/AUDIT.md` §8.

---

## 0. THE SEVEN SENTENCES THAT MUST NEVER BE DROPPED

1. **The top claim is NOT PROVED.** *In an honest deployment, programmable tokens
   cannot exist outside the mini-ledger (the `programmableLogicBase` payment
   credential).* What exists is (a) a machine-checked **reduction** of it to four leaf
   obligations plus **26 project axioms** (`WSC.Composition.top_claim`), and (b) that
   reduction **discharged outright over one class** —
   `WSC.Composition.containment_on_contained_class`, over `ContainedTx`: transactions
   no output of which sends a non-ada policy off-base and which register no policy.
2. **The class in (b) excludes exactly the transactions the claim is about.** Its four
   `LeafSet` fields are proved from ledger accounting (`LR_BALANCE_SLOT` + `WSC.NONNEG`
   + the class); **no UPLC result is used**, the acceptance hypotheses are provably
   unused, and the resulting theorem depends on the **same 26 axioms and the same
   `sorryAx`** as the un-instantiated `top_claim` (`AUDIT.md` §3.1, measured
   set-identical). What is closed end to end is the LEDGER-LEVEL plumbing — branch
   analysis, registry monotonicity, trace induction — against a constructed antecedent.
3. **Everything about the bytecode is BOUNDED BY A CEK BUDGET.** `#prep_uplc … n` bakes
   a finite step budget into the term the theorems quantify over; exceeding it evaluates
   to `Error`, which makes `isSuccessful` false and any `accept → POST` theorem vacuous
   past the bound. Every UPLC result below is bounded-transaction model checking of the
   real bytecode (ADDENDUM E1). **No result covers unboundedly large transactions.**
4. **The shaped results are ALSO bounded by their SHAPE, there is no coverage argument,
   and the shapes are UNREALIZABLE.** A shaped theorem quantifies over the scalar leaves
   (every `ByteString`, every `Integer`) of a *fixed* `Data` skeleton — list lengths,
   constructor tags and `Option`s all pinned. `SHAPE-BRIDGE.md` §10 offers no coverage
   route; `ShapeBridge.M1Covers` is **false as stated**; P2b is provable at SHAPE S1
   *because* S1's one-policy/one-token-name values evade the two counterexamples that
   defeat it in general. And task A2 proved every shape **empty as a class of ledger
   transactions** (one-entry redeemer map vs two script withdrawals; Conway
   `MissingRedeemers`). **Honest label for the whole shaped layer: exhaustive symbolic
   checking of the real compiled code over named bounded families of `Data` skeletons
   whose intersection with node-buildable contexts is currently EMPTY.** Never quote a
   budget without its shape.
5. **`DirWF` / `DIRWF_L` is the single escape-critical assumption.** P5 is exactly as
   strong as it. U10 (`mkDirectoryNodeMP` at UPLC) is what would turn it from ASSUMED
   into PROVEN. Task V4 added its missing fourth (interval) conjunct and made the two
   bridges that consume it PROVED THEOREMS
   (`WSC.covering_node_excludes_registration`,
   `WSC.Composition.covering_excludes_ledger_registration`, both
   `[propext, Classical.choice, Quot.sound]` only), so the surface is the same size but
   discharging it is now an implication rather than a gap.
6. **"`sorry`-free" is FALSE for this library, including for every top-level theorem.**
   64 theorem-position results are closed by `blaster`'s `admit`; what certifies them is
   the `✅ Valid` verdict in the build log, not the Lean kernel. All four top-level
   theorems inherit `sorryAx` through P3. **And the build log's `sorry` warning count is
   not a census** — 27 modules set `set_option warn.sorry false` (16 of them in the
   built set), so use `#print axioms` → `sorryAx`.
7. **`WSC/goldens/K-MEASUREMENTS.md` §5.1's prep-cost table must not be used for
   numbers**, and neither may that file's or `MANIFEST.md`'s cost/K rows for the two
   accepting **seize** goldens. §5.1 prices a module at **2,143 s** that re-measures at
   **45.5 s** isolated (`AUDIT.md` §8 F5, 47×); the seize rows publish pre-fix costs and
   the derived K's 2,570 / 4,647 describe vectors that have since been replaced
   (`AUDIT.md` §8 F13). Time with `lake build`, never `lake env lean`, and re-measure
   before concluding anything is unaffordable.

---

## 1. VERIFIED BUILD STATE (task A3 clean-room rebuild)

| measurement | value |
|---|---|
| command | `rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*` then `lake build WSC WSC.ShapeBridge` |
| exit status / jobs | **0** / **405** |
| wall clock / max RSS | **98.5 s** / **1.65 GB** |
| WSC modules re-elaborated | **67** |
| solver verdicts | **101 — 66 `✅ Valid` + 35 `✅ Expected Falsified`** |
| `⚠️ Undetermined` / `❌` / `error:` | **0 / 0 / 0** |
| expected `sorry` warnings | **20** (19 `ShapeBridge` + 1 pre-existing in PCB) |
| source reconciliation | 35 `(solve-result: 1)` + 2 `(solve-result: 0)` + 64 `by blaster` = **101**, per-file exact |

Delta against the U3 baseline of 98 (64 V + 34 EF): **+4 −1**. `+4` = the new
`WSC/Props/P3_BaseRun.lean` (3 V + 1 EF); `−1` = `Composition.mintingNonVacuous` is now
a term proof, not `by blaster` (which also takes the `sorry` count 21 → 20).
`NonVacuity.lean` and `ShapeRealizability.lean` add **zero** verdicts each.

**Provenance, newly re-verified at A3:** all four `WSC/flats/*.flat` are byte-identical
to the `cborHex` of the named **unapplied** production TextEnvelope JSONs at the
recorded wsc-poc commit `7ae0024b185cf16f17e38c20c9ee97ae1410c51f` (`AUDIT.md` §6.1).
"Proved against production bytecode" is machine-verified, not asserted.

---

## 2. PROPERTY STATUS TABLE

State vocabulary (only these are used; "PROVEN-BY-DESIGN" and any unbounded claim are
banned):

* `PROVEN-AT-UPLC-WITHIN-BUDGET-K` — a `by blaster` theorem over the real bytecode at a
  named budget, with a non-vacuity witness, quantified over **all** `ScriptContext`s.
* `PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE` — the same, but quantified over the scalar
  leaves of a named SHAPE. **BOTH bounds binding, and the shape class is provably not
  node-buildable (§0.4).** Adds no faithfulness axiom. Strictly weaker than the row
  above; versus a source-model result it is stronger on the axiom count and weaker on
  the quantifier — neither dominates.
* `PROVEN-ON-SOURCE-MODEL-modulo-faithfulness-axiom` — a `sorry`-free Lean theorem about
  a clause-by-clause hand transcription (`WSC/Model/*.lean`), with ONE explicit
  `<model>_faithful` axiom bridging to the bytecode, backed by source-line citations and
  a golden differential test.
* `STATED-NOT-PROVED` / `DEFERRED`.

| Prop | Plain English | State | Budget K | SHAPE | Non-vacuity: probe / witness K | Scope caveat |
|---|---|---|---|---|---|---|
| **P1** | Transfers conserve programmable tokens inside the mini-ledger: for a non-exemptable `(cs,tn)`, the amount at base outputs is at least the amount at base inputs plus the **SIGNED** net mint. | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `Props/Shaped/P1Shaped.lean` `P1_T1`:223, `P1_T2`:273, `P1_T6`:794, `P1_T7`:839, all ✅ Valid, **0 project axioms**. The `NOT-REACHABLE-AT-UPLC` verdict of earlier revisions is WITHDRAWN. Source-model route (`Props/P1_Transfer.lean`) retained as the only all-contexts statement; `P1_model` there is STATED-NOT-PROVED. | **4400** | **T1 / T2 / T6 / T7** | probes :380/:403/:861/:884 all Falsified; witnesses **2603 / 3572 / 3150 / 3572**; plus `exec_rejects_escape` — a ledger-legal containment violation the real CEK rejects | Bounded twice. **Only 1 of 3 containment dispatch paths** at UPLC (Path A); Paths B/C and ≥2 mini-ledger inputs blocked by Blaster **D6**. Path C proved at Lean level (`pathC_sound`). Exemption hypothesis carried as `Model.coveringNodeExists … = false`; bridging to ground truth costs `TS3`. **Aggregate containment at the base *payment* credential — not per-holder ownership.** FINDING: ARCHITECTURE §3-P1's `mintPos` form is **REFUTED** against the bytecode (`mintPos_form_REFUTED`); the SIGNED form is correct and is what Preservation consumes. |
| **P2** | An accepted seizure relocates only the seized policy and it stays in the mini-ledger. | **BOTH conjuncts PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `Props/Shaped/P2Shaped.lean` `P2a_shaped_structure`:232, `P2b_shaped_containment`:288, joint `P2_shaped`:370, ✅ Valid, **0 project axioms**. `NOT-REACHABLE-AT-UPLC` WITHDRAWN. Conjunct (a) additionally `PROVEN-ON-SOURCE-MODEL-modulo-faithfulness-axiom` (`P2a_bytecode` + `seizeModel_faithful`) — the version quantifying over all contexts and all step counts. | **3800** | **S1** | probe :630 Falsified; witnesses **3004 / 3328**; two rejecting controls (escaping seize, stolen staking credential). Model fidelity gate: **13/13** golden agreement incl. a rejecting vector. | **Conjunct (b) is the sharpest shape-dependence in the library:** FALSE-in-general on the source model (obligation B1, two machine-checked counterexamples — `ptokenPairsContain` is unsound with duplicate token names or unsorted maps) and closes at S1 only because S1's values are structurally canonical. **Do not generalize it by inspection.** P2 does NOT claim the directory node the redeemer points at is authentic (ARCHITECTURE L2.5). The unshaped prep never completed (77 min @2000, 62 min @9000); 600 and 1000 probes are `Valid`, i.e. **every earlier UPLC P2 statement was provably vacuous**. |
| **P3** | You cannot spend a mini-ledger UTxO unless the global (transfer) or seize validator runs in the same transaction. | **PROVEN-AT-UPLC-WITHIN-BUDGET-K** — the only UNSHAPED leaf, and the only one any top-level theorem consumes. Two forms, both ✅ Valid, both 0 project axioms: the prep form `Props/P3_Base.lean:67` and **the run form `Props/P3_BaseRun.lean:87`, which is what `Composition.p3_lifted` uses** (task A1). | **600** | **none** | prep form: probe :112 Falsified, tightness :100 Falsified, witness accepted at 600 on both `.exec` and `.prop`. Run form: **its own** probe `P3_run_vacuity_probe`:123 Falsified **at the run term**. Production golden halts accepting in **208** steps. | Covers base spends halting within 600 steps. Its conclusion is "the credential is in `txInfoWdrl`"; upgrading that to "the validator actually ran" is `LR_WDRL_RUNS_VALIDATOR`, not part of the proof. **This is the reason every top-level theorem carries `sorryAx`.** |
| **P4** | Every accepted mint routes tokens into the mini-ledger or is a pure burn — Local / DelegateTransfer / DelegateSeize / BurnOnly. | **ALL FOUR ARMS PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE, SHAPE BY SHAPE** — arm 1 `P4LocalShaped.lean` `P4_local_noEscape_shaped`:203, `P4_local_arm_shaped`:299, `P4_disjunction_at_L1`:349, plus index-loosened `P4_local_noEscape_shapedIdx`:407 (SUPERSEDES the L1 form); arm 2 `P4_disjunction_at_DT1`:244; arm 3 `P4_disjunction_at_DS1`:406; arm 4 `P4Shaped.lean:165` + `P4ShapedIdx.lean:59`. All ✅ Valid, **0 project axioms**. | arm 4 **900**; arms 1–3 **2500** | **M1/M2**; **L1/L2, DT1, DS1** | probes at every one of those shapes Falsified (`P4Shaped:247`, `P4ShapedIdx:103`, `P4LocalShaped:455`/`:545`, `P4DelegateShaped:360`/`:530`); witnesses **784 / 1681 / 1257 / 1466** — each EXACTLY the step count of its production golden | Four theorems over four pairwise-disjoint shape classes is **not** one theorem over a symbolic redeemer (that goal returns `Undetermined`). Arm 1 is the strong one: the policy's OWN no-escape scan over every output, in ground-truth `noEscape` vocabulary. **Arms 2 and 3 prove strictly less** — only that a sibling validator RUNS. Registration conjunct at SHAPE L2 is `Undetermined`. |
| **P4a** | Every accepted mint invokes the token's own minting-logic script (the corollary common to all four arms). | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P4Shaped.lean:121` (M1), `P4ShapedIdx.lean:42` (M2 — withdrawal index symbolic, strictly more general), `P4a_local_shaped`:235 (L1). ✅ Valid, 0 project axioms. | as P4's arms | M1 / M2 / L1 | full control set at each shape (negative control Valid, tightness Falsified, vacuity Falsified) | Fully symbolic redeemer: `Undetermined` after 3,208 s. |
| **P5** | A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ the transaction really references an authentic directory node whose interval covers `cs` (`key < cs < next`). | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P5Shaped.lean` `P5_shaped_indexed`:209 ✅ Valid, 0 project axioms; composed with the pure-Lean ladder in `Props/P5_NonMember.lean` this gives ADDENDUM E3's ∃-form `P5_shaped_exists`:239 and the ground-truth `P5_shaped_groundtruth`:276 (**+ `TS3`, `Deployed`, `OnChain` only — `TS5` is NOT needed**). | **1600** | **G1** | probe :398 Falsified; witness **1541** (halts at 1541, budget-`Error` at 1540), on a context with **ZERO** failing `validRewardingContext` conjuncts; accepted by the shaped AND the unshaped executable term | **Escape-critical: P5's strength = `DirWF`'s strength.** The postcondition is the covering-node witness, **not** `¬ IsRegistered`; the bridge is now a proved theorem *given* `DirWF`. Proved **one node index at a time**: freeing the NonMember index (G3) returns `Undetermined` after 906 s on a non-empty class; freeing both redeemer indices (G2) is genuinely **Falsified** with a counterexample naming the wrong object (on chain excluded by `TS2` — deliberately unavailable to a bytecode theorem). Requires the **unpushed** PCB branch. Fully symbolic: no verdict, killed at 5,241 s. |
| **P6** | Claiming Member is self-penalizing: an accepted Member classification *adds* the positive minted amount to the value that must remain at base outputs. | **PROVEN-AT-UPLC-WITHIN-BUDGET-K-AND-SHAPE** — `P6Shaped.lean` `P6_shaped_member_adds_to_requirement`:234, `P6_shaped_member_mint_stays_at_base`:259, ✅ Valid, 0 project axioms; `P6_shaped_noBaseInputs`:209 is pure Lean (**no `sorryAx` at all** — the only headline the kernel fully checks). Bridged to `Composition.lean`'s vocabulary by `P6Bridge.lean`. `NOT-REACHABLE-AT-UPLC` WITHDRAWN. | **3300** | **G6** | probe :363 Falsified; witness **2837**, plus `exec_rejects_escape_under_member` and the discriminating pair `exec_accepts_same_escape_under_nonmember` | **⚠️ THE CAUTIONARY ROW OF THE WHOLE CAMPAIGN.** P6 was first stated at **2500**, returned `✅ Valid`, and was **genuinely VACUOUS** — the shape class was accept-UNSAT and only the mandatory probe caught it (`Shaped/Probe/G6Vacuous2500.lean`, a stanza that *expects* `Valid`). **No accept-hypothesis theorem in this library may be quoted without its probe.** |
| **P2′** | A seized-policy mint cannot bypass the seize: the issuance `DelegateSeize` arm binds that mint to this seize. | **PARTIALLY SUBSUMED, binding claim DEFERRED** — the arm is proved at SHAPE DS1 (`P4_delegateSeize_arm_shaped`) but concludes only `seizeScopedToNodeOf` / "the seize validator runs". | — | DS1 | — | Its postcondition names the seize redeemer, so it needs P2 and P4-arm-3 in the SAME statement; nobody has written it. See also the `LR5` gap in §4. |

---

## 3. COMPOSITION (`WSC/Composition.lean`)

| Item | State | Note |
|---|---|---|
| `top_claim`, `no_programmable_tokens_outside_mini_ledger`, `preservation`, `nonEscape_of_registered` | **PROVED AS A REDUCTION.** Real Lean theorems, green in the A3 rebuild — but stated over an explicit `leaves : LeafSet hp Shape` hypothesis bundle, and they carry `sorryAx` (through P3). **Never quote as "the claim is proved."** | Ledger vocabulary exists: `UTxO`/`Ledger`/`OutOfBase`/`RegisteredIn`/`I`/`Reachable`. Per-theorem `#print axioms` in `AUDIT.md` §3.2. |
| **`containedLeaves : LeafSet hp (ContainedTx hp)`** (§11, task A2) | **CONSTRUCTED — all four fields proved.** `#print axioms`: **11 project axioms, no `sorryAx`, no `blaster` verdict, no `native_decide`, no `<model>_faithful`.** | THE CLASS: no output sends a non-ada policy off-base (`InertOffBase`) **and** no output is an authentic directory node (`NoRegistration`). Unrestricted: input/output counts, spending of mini-ledger UTxOs, mint/burn, redeemer, withdrawals, reference inputs, all quantities, all policy identities. |
| **`containment_on_contained_class`, `no_escape_on_contained_class`** | **THE TOP CLAIM WITH NO `LeafSet` HYPOTHESIS**, over `ContainedTx`. Axiom list measured **set-identical to `top_claim`'s** 26 + `sorryAx`. | **HONEST LIMIT: the class excludes exactly the transactions for which containment is a property of the BYTECODE**, the acceptance hypotheses are provably unused (Lean's own `unused variable` warnings), and no UPLC result is used. What it buys is that the ledger-level half is closed against a *constructed* antecedent. |
| **Class inhabitation** | **PROVED, non-degenerately.** `containedTx_witness` + `contained_witness_moves_tokens`: a two-output transaction whose base output really holds **5 `MMM.TOK`** (`native_decide` on CLAB's `valueOf`), 0 project axioms. | `WSC.OnChain` is an opaque axiom, so no witness in this library can be proved on-chain. Precision (`AUDIT.md` F16): the statement is an implication over the output list, not a closed `∃ ctx`. |
| `containment_on_inert_class_of_nopre` (§11.6) | **PROVED** — drops `NoRegistration` (directory inserts back in) and carries `LeafSet.nopre` as the **single** remaining hypothesis, with p1/p2/p4 proved inline. | The honest way to see how much rests on the field the audit calls the weakest link. |
| **Instantiating the `LeafSet` at a SHAPED class** | **PROVED IMPOSSIBLE (usefully).** `Props/Shaped/ShapeRealizability.lean`: every shaped class is EMPTY as a class of ledger transactions, so such a `LeafSet` is a vacuous theorem. `t1_class_is_empty` is **unconditional** on axioms this library already has (`LR_SPEND_RUNS_VALIDATOR` + `LR_CTX`), no `sorryAx`; L1/DT1/M1/G1/S1 (and T1 by the withdrawal route) are empty under `RedeemerCoverage` — a `def … : Prop`, **NOT an axiom**. `t1VacuousLeaves` + `t1_no_honest_step` exhibit the trap. | Cause: a tractable `#prep_uplc` bakes a **one-entry** redeemer map (two for DS1) while baking a **two-entry** withdrawal map with both entries SCRIPT credentials; Conway UTXOW `MissingRedeemers` needs one redeemer entry per script witness. **This refutes no P-theorem** — it refutes composing a shaped leaf *through* a `Shape` restriction. |
| `LeafSet.p1` (exit via transfer, P6 folded in) — GENERAL class | **INGREDIENT PROVED, RESIDUE OPEN** — `leafP1_of_shapedGlobalContainment` (§10.2) gives the field's exact type from `ShapedGlobalContainment`, whose single field is the shape bridge at the 4400 prep + `LR_BUDGET_global` at 4400. Vocabulary bridges (§10.1) are PROVED. | Costs `TS3`, `Deployed`, `OnChain`, `NodeAcceptsGlobal`. Residue now known to require **re-cut shapes** (§3 row above), not just plumbing. |
| `LeafSet.p4` (entrance) — GENERAL class | **INGREDIENT PROVED, RESIDUE OPEN** — `p4_disjuncts_of_custody` (§10.3) derives the field from the four-way `LocalCustodyOk ∨ DelegateTransferOk ∨ DelegateSeizeOk ∨ BurnOnlyOk`, which is what the four shaped arms conclude. | Residues: shape coverage + realizability, the shape bridge, a minting budget bridge at 2500 (the BRIDGE half now exists — §4). Carries the `LR5` gap. |
| `LeafSet.p2` (exit via seize) — GENERAL class | **OPEN.** The shaped P2 theorems exist; nothing connects them to the field. | Needs the shape bridge plus "structure preserved ⟹ `Contain` for a non-seized policy", an unwritten lemma. |
| `LeafSet.nopre` (`L-mint-needs-reg`) — GENERAL class | **OPEN, the weakest leaf.** Nobody has started it; `ContainedTx` *excludes* it rather than discharging it. | Needs the FULL P4 over a symbolic redeemer plus trace induction. |
| `L-monotone` (registration is insert-only) | **ASSUMED** — `DirWF` conjunct (i) per-tx; `lr_registration_source` + `DIRWF_L` at ledger level. | Discharged by U10. |
| `LR_BALANCE_SLOT` | **AXIOM, but its exact statement is DERIVED** — `LR_BALANCE_SLOT_of_valueAlgebra` proves it from `WSC.LR7` plus two named `CardanoLedgerApi`-only residues (`ValueAlgebra`, 3 fields; `LedgerCanon`). Instantiating both deletes the axiom. | U2 finding: **`valueOf` is NOT additive over `merge`** without canonicity (`merge_not_additive_without_canonicity`, a `native_decide` counterexample), and CLAB has **zero** `Value` algebra — so "mechanical" was wrong. Budget ~330 lines. |

---

## 4. THE SHAPE BRIDGE AND THE BUDGET BRIDGES

| Item | State |
|---|---|
| `isSuccessful (appliedXShaped.prop args) ↔ isSuccessful (appliedX.prop (shapedCtx args))` | **PROVED for all 16 shaped preps, no axiom.** 25 verdicts re-verified in the A3 rebuild (19 Valid + 6 Expected-Falsified controls). The `exec`-level form (`Runs.XRun K`) is **kernel-checked `rfl`** — `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — at EVERY budget; `inputs_M1` "does not depend on any axioms". |
| Tier A (6 shapes: B1@600, M1/M2@900, G1/GIdx/GNIdx@1600) | RHS is the unshaped prep's `prop` at the same budget — complete, no residual. |
| Tier B (10 shapes: G6@3300, L1/L2/DT1/DS1@2500, S1@3800, T1/T2/T6/T7@4400) | RHS is `Runs.XRun K`; **no unshaped prep exists at those budgets and none is affordable.** Inherits `PropExecFaithful` (`SHAPE-BRIDGE.md` §5). |
| **Is the shape bridge consumed?** | **PARTLY — YES by `Honest.lean`, still NO by `Composition.lean`.** Task A1 restated the four `LR_BUDGET_*` axioms against `Runs.XRun K` (definitions moved to the leaf module `WSC/Runs.lean` to break the import cycle), so the ledger side now names exactly the term the 16 `exec_<S>` `rfl`s land on. **No `bridge_<S>` is applied to anything**, because no `LeafSet` field is discharged from a shaped theorem — and §3's realizability row explains why that consumer never arrived. Wiring it in is worthless until the shapes are re-cut. |
| Does the Tier A/B split still matter? | For the LEDGER bridge, no. For OPTIMIZER evidence, yes: Tier A's RHS went through `Optimize.main` on a symbolic context and Tier B's did not, so only Tier A's verdict says anything about shaping-commutes-with-the-optimizer. |
| **Published K constants** | Seven, each ≥ a named witness's measured accepting step count: `K_base` **600** (P3Witness / golden 208), `K_mint` **900** (M1, 784), `K_mint_custody` **2500** (L1, 1681; DT1 1257, DS1 1466 inside), `K_global_nonmember` **1600** (G1, 1541), `K_global_member` **3300** (G6, 2837), `K_global` **4400** (T1 2603; T6 3150; T2/T7 3572), `K_seize` **3800** (S1, 3004; residual 3328). |
| **Non-vacuity of the budget bridges** | **ALL DISCHARGED, none open.** `baseNonVacuous`/`mintingNonVacuous` in `Composition.lean`; `MintingNonVacuous@2500`, `GlobalNonVacuous@1600/3300/4400`, `SeizeNonVacuous@3800` in `Props/Shaped/NonVacuity.lean` — all `native_decide` on the real CEK, **0 project axioms, no `sorryAx`**. |
| **Are the budget bridges consumed?** | **Only `LR_BUDGET_base`, at exactly one instantiation** (`Composition.p3_lifted`, `K := 600`). `LR_BUDGET_minting`, `LR_BUDGET_global` and `LR_BUDGET_seize` are applied by **nothing** — six of the seven published budgets are inert (`AUDIT.md` §8 F15). |
| `WithinBudget` | Quotes `K_base` / `K_mint` / `K_global` only. Deliberately NOT widened to `K_mint_custody` or given a seize clause: that widens `HonestTx`, which strengthens the top claim and correspondingly hardens its open general-class obligations — a composition-core change, not a restatement. |
| In the default build target? | **Yes** — `WSC.lean` imports `Runs`, `P3_BaseRun`, `NonVacuity`, `ShapeBridge`, `ShapeRealizability` (52 imports). |

---

## 5. AXIOM BASE — WHAT IS ASSUMED

**50 `axiom` declarations** by `grep -c '^axiom '`: `Honest.lean` **37**,
`Composition.lean` **10**, `Props/P1_Transfer.lean` **2**, `Model/SeizeModel.lean`
**1**. **Zero `axiom` anywhere in `Prep/*`, `Shaped/*` or `Props/Shaped/*`** — the
shaped layer really does add no assumption, machine-verified and unchanged by A1/A2.
The strongest available claim reaches **26** of the 50; read that as a **floor**, since
any *bytecode-based* discharge of the general-class leaves adds the other 24. Full
per-theorem census: `AUDIT.md` §3. **Read the numbering-collision table at the top of
`WSC/Honest.lean` before citing a name** — the file-local `TS1…TS5` / `LR1…LR7` do not
mean ARCHITECTURE §5.3's.

| Group | Axioms | Reached by the top-level theorems? | Discharged by |
|---|---|---|---|
| Modelling boundary | `OnChain`, `Deployed` | yes | Never — they are the model/chain bridge. |
| TRUSTED-SETUP | `TS1`, `TS2`, `TS_MINTING_IDENTITY`, `mlhPolicyId` | only `mlhPolicyId` | Deployment audit of the one-shot params anchor; U10 for the registration side. `TS_SCRIPT_HASH_BINDING` is **checked, not assumed** (E7; and the whole provenance chain is now re-verified — `AUDIT.md` §6.1). |
| LEDGER-RULE (per-tx) | `LR1`–`LR7`, `LR_CTX` | only `LR_CTX` | Trusting the Cardano ledger; every `LR_CTX` conjunct is mapped to a cited ledger rule (`WSC/LR-CTX-AUDIT.md`). **Known missing row: `MissingRedeemers`** — that gap is what `ShapeRealizability.RedeemerCoverage` states. |
| LEDGER-RULE (triggers) | `LR_MINT_RUNS_POLICY`, `LR_WDRL_RUNS_VALIDATOR`, `LR_SPEND_RUNS_VALIDATOR` | yes | Trusting the ledger (Conway UTXOW scripts-needed). |
| Non-negativity | `NONNEG`, `NONNEG_L` | yes | Trusting the ledger. |
| Node-accept / step abstractions | `NodeAccepts{Base,Minting,Global,Seize}`, `nodeSteps{Base,Minting,Global,Seize}` | all but `nodeStepsSeize` | Never — they ARE the "a node ran this script for this many steps" interface. |
| Budget bridge | `LR_BUDGET_base`, `LR_BUDGET_minting`, `LR_BUDGET_global`, `LR_BUDGET_seize` — all four now `K`-parametric over `Runs.XRun K`, each gated on a **proved** non-vacuity hypothesis | only `LR_BUDGET_base` | A budget-monotonicity meta-theorem about `runSteps` that the substrate does not provide. `GlobalPreppedAt` was **deleted** by A1 (its side condition is now discharged by reading `Runs.globalRun K`'s definition). |
| DIRECTORY | `DIRWF` (**4** conjuncts since V4), `TS3`, `TS4`, `TS5` | none — they enter with the leaves | **U10** — `mkDirectoryNodeMP` at UPLC. **Escape-critical.** Measured: the raw↔ground-truth reconciliation costs `TS3` only, **not** `TS5`. |
| LEDGER-LEVEL (`Composition.lean`) | `LedgerStep`, `Genesis` (declared, not defined); `lr_utxo_semantics`, `lr_inputs_in_ledger`, `lr_registration_source`, `LR_BALANCE_SLOT`, `ts_genesis`, `ts_minting_identity_L`, `NONNEG_L`, `DIRWF_L` | **all 10** | Trusting the ledger (the `lr_*` four + `NONNEG_L`); deployment audit (`Genesis`/`ts_genesis`/`ts_minting_identity_L`); **U10** (`DIRWF_L`, escape-critical). `LR_BALANCE_SLOT` is derivable — §3. |
| FAITHFULNESS (deliberately NOT in `Honest.lean` — a different KIND of assumption) | `Model.globalModel_faithful`, `SeizeModel.seizeModel_faithful` | no | Source-line citations + golden differential (global 4/4, seize 13/13, both including rejecting vectors). Each is a whole-validator model↔bytecode equivalence. |
| NOT EXPRESSIBLE | ARCHITECTURE §5.3 `lr_collateral_pubkey_only` | — | PlutusV3 `TxInfo` has no collateral field; the collateral exit route must be closed outside this model. |

---

## 6. DEFECTS — CURRENT LEDGER

**D1 (`validRedeemerMap` ordering) — ✅ FIXED (Z1), and EXERCISED.** CLAB used the
Plutus constructor order for `ScriptPurpose`; the ledger emits
`ConwayPlutusPurpose AsIx` order and does not re-sort (`Conway/Scripts.hs:202-213`,
`Babbage/TxInfo.hs:217-221`). `ltScriptPurpose` (V3 and V1/V2) now uses the ledger order
with citations. SHAPE **DS1** carries a real 2-entry `[Minting, Rewarding]` redeemer map
that `validMintingContext` accepts, with a Falsified vacuity probe and a concrete
accepted witness. (`P4Shaped.lean`'s D1 stanza is stale on this point.)

**D2 (`validWithdrawals` credential order) — ✅ FIXED (Z1).** `ltCredential` is now
`ScriptCredential < PubKeyCredential` (`Credential.hs:96-99`). Changed no golden
verdict, as predicted, confirming the seize goldens' earlier `validWithdrawals` failure
was a harness artifact.

**D3 (no golden satisfied `validXContext`) — ✅ FIXED (Z5).** All 9 ACCEPTING goldens
satisfy `validXContext` verbatim; 10 of 13 are TRUE and the 3 FALSE are
tamper-intrinsic. Machine-checked in `WSC/Goldens/Audit.lean`. Pre-fix JSONs kept under
`WSC/goldens/pre-fix/`.

**D4 — CLAB does not assert the PV11 rule
`txInfoInputs ∩ txInfoReferenceInputs = ∅`** (`Conway/TxInfo.hs:492, 811-822`). A
*missing* conjunct, i.e. the precondition is weaker than reality, which strengthens the
theorems. Recorded, not a problem. (`SeizeShaped.lean`'s header uses "D4" for an
unrelated `#prep_uplc` limitation — the numbering collides; read in context.)

**D5 — the substrate is not reproducible off this machine, and worse than previously
described.** `lakefile.lean` requires PlutusCoreBlaster from the **absolute local path**
`/home/gumbo/iohk/PlutusCoreBlaster` (branch `cip153-value-builtins`, unpushed), and
`lake-manifest.json` records `"type": "path"` with **no revision at all** — so there is
not even a local commit to re-pin against. Without those CIP-153 `Value` builtins
`programmableLogicGlobal.flat` does not decode (verified negative control against PCB
`main`), so every P1/P5/P6 "proved against production bytecode" claim inherits this.
`Blaster` by contrast *is* pinned (rev `59db213c…`). **Highest operational risk in the
repository.**

**D6 — Blaster `#prep_uplc` emits kernel-ill-typed `Blaster.dite'` terms** when a
CIP-153 `Value` builtin result stays symbolic (the motive is not updated after De Morgan
/ Bool-polarity rewrites). Reproductions
`WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` (deliberately non-building; imported
nowhere — re-verified). **Blocks P1's containment dispatch Paths B/C and input-side
aggregation at UPLC.** Needs an upstream fix.

**D7 — `K-MEASUREMENTS.md` §5.1's prep costs are ~47× pessimistic.** §0.7 and
`AUDIT.md` §8 F5. Not a code defect; a measurement defect that has already misdirected
work.

**D8 — `set_option warn.sorry false` in 27 modules (16 built) makes the build-log
`sorry` census incomplete** (~45 `admit`s hidden). Use `#print axioms` → `sorryAx`;
reproducible in one command via `WSC/Shaped/Probe/U3Census.lean`. (Earlier revisions of
this file said 15 modules; that was wrong.)

**D9 (task A3) — the golden cost tables are stale for the two accepting seize
vectors.** `MANIFEST.md:125-126` and `K-MEASUREMENTS.md:154-155` publish pre-fix costs
(51,571,527 / 96,841,491 CPU) against current JSONs recording 60,231,630 / 105,501,594,
so the derived K's 2,570 / 4,647 describe replaced vectors. No theorem depends on them;
`K_seize = 3800`'s stated limit quotes one, and the direction is conservative
(`AUDIT.md` §8 F13).

**D10 (task A3) — `WSC/flats/PROVENANCE.md`'s closing note is factually false**: it says
`programmableLogicGlobal.flat` does not decode and its `#import_uplc` is commented out.
It decodes and is imported (`Prep/Global.lean:46`, `Prep/Global1600.lean:66`). The
provenance **table** in that file is correct and now re-verified (`AUDIT.md` §6.1).

---

## 7. WHAT WOULD MOVE THE NEEDLE, IN ORDER

1. **RE-CUT THE SHAPES WITH LEDGER-REALISTIC REDEEMER MAPS.** This is now the top item
   and it displaces everything that used to sit above it, because until it is done no
   shaped leaf can be composed at all (§3's realizability row). Sized, with a concrete
   template from a real vector: the cheapest realizable shape is modelled by the golden
   `transfer-nonmember-covering-node` (**one** script withdrawal, **two** redeemer
   entries), so shrink each shape's withdrawal map to the one script credential the
   validator needs, add its matching `Rewarding` entry, and add a `Spending` entry
   wherever the shape spends a script input. Cost: a new `#prep_uplc` per shape
   (≈1–2 s, budget-independent — `AUDIT.md` §8 F5) plus re-verification of every theorem
   over it. Open risk: a multi-entry redeemer map may enlarge the solver residual.
2. **Instantiate the general-class `LeafSet`** on top of item 1. `p1`/`p4` then need
   only their named residues; `p2` needs "structure preserved ⟹ `Contain`"; `nopre`
   needs the full P4 over a symbolic redeemer plus trace induction. Until then the top
   claim is proved only over `ContainedTx`, where the class and not the code does the
   work.
3. **Restate the 14 shaped P-theorem groups on `Runs.XRun K`**, each with a FRESH
   vacuity probe at the run term — that is what deletes `PropExecFaithful` from the
   campaign. Measured feasible at keystone grade in `Props/P3_BaseRun.lean` (✅ Valid,
   3.7 s). Real proving, with real risk that a probe returns `Valid` (i.e. vacuous), as
   happened to P6 at 2500.
4. **U10 — `mkDirectoryNodeMP` at UPLC**, discharging `DirWF`/`DIRWF_L`. The only
   escape-critical assumption; highest assurance ROI.
5. **Push the PCB `cip153-value-builtins` branch and re-pin `lakefile.lean` to a full
   rev** (D5). Cheap, and without it nothing here is independently checkable.
6. **Fix D6 upstream** — that is what would extend P1 to dispatch Paths B/C and to ≥2
   mini-ledger inputs.
7. **Add the `MissingRedeemers` row to the LR-CTX audit** and to `Honest.lean`, and
   strengthen `LR5` with a `Conway/TxInfo.hs transTxRedeemers` audit row. These are two
   directions of the same missing ledger rule, and item 1 will need the first one.
8. **Instantiate `ValueAlgebra` + `LedgerCanon`** to delete `LR_BALANCE_SLOT`; budget it
   as a ~330-line `Value`-algebra development, not a mechanical step.
9. **Re-measure the two accepting seize goldens' K** and correct `MANIFEST.md` /
   `K-MEASUREMENTS.md` (D9).

Items completed and deliberately retired from this list: restating `LR_BUDGET_*` against
the kernel-checked bridge (task A1, and note `AUDIT.md` §7.1 for what it did and did not
buy); discharging every non-vacuity obligation (A1); constructing a `LeafSet` (A2, over
`ContainedTx`).

---

## 8. REPRODUCTION

```bash
# the whole library, clean-room
#   A3: 405 jobs, 98.5 s, 101 ✅ markers, 0 errors, 20 expected `sorry` warnings
cp -a <CLAB checkout> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge

# the axiom census behind §5 and AUDIT.md §3 (2.7 s warm)
lake build WSC.Shaped.Probe.U3Census

# prep-cost re-measurement (D7's repair) -- K-MEASUREMENTS.md §5.1a
for m in Base Minting Minting800 Minting900 Minting1300 Seize Global Global1600; do
  rm -f .lake/build/lib/lean/WSC/Prep/$m.olean .lake/build/lib/lean/WSC/Prep/$m.ilean \
        .lake/build/lib/lean/WSC/Prep/$m.trace .lake/build/lib/lean/WSC/Prep/$m.*.hash
  /usr/bin/time -f "$m %e s %M KB" lake build WSC.Prep.$m > /dev/null
done

# PROVENANCE re-verification (AUDIT.md §6.1)
sha256sum WSC/flats/*.flat        # must match WSC/flats/PROVENANCE.md's table
git -C <wsc-poc worktree> show \
  7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum

# CEK step counts K of the 13 goldens (3.2 s) -- see D9 before quoting the seize rows
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# per-conjunct golden validXContext audit (§6 D1/D2/D3)
python3 WSC/goldens/ctx-audit/GenCtxAudit.py       && lake env lean CtxAudit.lean
python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py && lake env lean CtxAuditDetail.lean
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artefact is the
entire content of D7.

Companion documents: `WSC/AUDIT.md` (the final audit — five censuses, the provenance
re-verification, the honesty-regression checks, the ranked findings, and "what a
reviewer should not believe"), `WSC/README.md` (reviewer-facing summary),
`WSC/EXEC-SUMMARY.md` (one page, no Lean), `WSC/ARCHITECTURE.md` (binding; ADDENDUM v3
overrides the base text), `WSC/SHAPE-BRIDGE.md`, `WSC/SHAPING-RESULTS.md`,
`WSC/SPIKE-FINDINGS.md`, `WSC/LR-CTX-AUDIT.md`,
`WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md` (**read §0.7 before believing their
numbers**).
