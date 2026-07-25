# WSC programmable-token containment — what this formalization establishes

**Audience.** A senior engineer or auditor deciding what to believe. Everything below
is cited to a file, a line, or a measurement in this repository. Where a task report
and `WSC/AUDIT.md` disagree, this document follows the audit.

Revision: branch `wsc-containment-proofs`, HEAD **`80cdac7`**. All numbers here were
re-measured in an independent clean-room rebuild at that revision (task A3).
Companion documents: `WSC/AUDIT.md` (the final audit — five censuses, the provenance
re-verification, the honesty-regression checks on the last two tasks, ranked findings,
and "what a reviewer should not believe"), `WSC/STATUS.md` (authoritative per-property
status), `WSC/ARCHITECTURE.md` (binding design; ADDENDUM v3 overrides the base text),
`WSC/SHAPING-RESULTS.md`, `WSC/SHAPE-BRIDGE.md`, `WSC/LR-CTX-AUDIT.md`,
`WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md`, `WSC/EXEC-SUMMARY.md` (one page, no Lean).

---

## 1. THE CLAIM, and exactly what is established

> **The claim.** *In an honest deployment, programmable tokens cannot exist outside
> the mini-ledger — the `programmableLogicBase` payment credential.*

**What is established: not the claim.** Two things are, and the gap between them and
the claim is the most important paragraph on this page.

**(a) A machine-checked REDUCTION.** `WSC.Composition.top_claim` proves "no reachable
ledger state holds a registered programmable token outside the base payment
credential" *from* a four-field bundle of leaf obligations (`LeafSet`) *plus* **26
project axioms**.

**(b) That reduction DISCHARGED, but only over an accounting class.**
`Composition.containedLeaves` is a constructed `LeafSet` — all four fields proved, no
`sorryAx`, no `blaster` verdict, no `native_decide` — and
`containment_on_contained_class` / `no_escape_on_contained_class` are the top claim
**with no `LeafSet` hypothesis**. The class is `ContainedTx`: transactions no output of
which sends a non-ada policy off-base, and which register no policy. It is proved
inhabited by a transaction that really moves **5 `MMM.TOK`** at a base output, and it
restricts nothing else — not the number of inputs or outputs, not spending mini-ledger
UTxOs, not minting or burning, not the redeemer, withdrawals, reference inputs,
quantities or policy identities.

**The honest limit of (b), and it is not a footnote.** The class excludes exactly the
transactions that put a programmable token at an off-base output — i.e. exactly the
transactions for which containment is a property of the **bytecode**. Its four fields
are proved from `LR_BALANCE_SLOT` + `WSC.NONNEG` + the class definition; **no UPLC
result is used**, and the acceptance hypotheses are *provably unused* (Lean's own
`unused variable` warnings at `Composition.lean:2442-2446` are the tell). The axiom
list is **measured set-identical** to the un-instantiated `top_claim`'s 26 plus
`sorryAx`. So (b) is progress on the **ledger-level plumbing** — branch analysis,
registry monotonicity, trace induction, all now closed against a *constructed*
antecedent — and **not** progress on the bytecode question.

**And the obvious route to closing the gap is proved closed.** Instantiating the
`Shape` parameter with a *shaped* context class — the natural way to plug P1/P2/P4 in —
yields a theorem about an **EMPTY** class: every shape in this library bakes a
one-entry redeemer map while baking two script-credential withdrawals, and Conway
UTXOW requires one redeemer entry per script witness
(`WSC/Props/Shaped/ShapeRealizability.lean`; **unconditional** for SHAPE T1 on axioms
the library already has). This audit corroborates the diagnosis by decoding all 13
production golden contexts: every accepting golden carries **2–5** redeemer entries
against 0–3 withdrawals, i.e. the real vectors *are* redeemer-covered, so the
one-entry map is a `#prep_uplc` tractability truncation and not a defect of the system
(§3.3 item 1 sizes the fix).

Underneath all of that, **six leaf properties are genuinely proved against the real
compiled production bytecode** — the `.flat` files exported from the production build,
whose provenance is now verified end to end (§4.1) — each bounded **twice**: by a
concrete CEK step budget `K`, and (for every property except P3) by a fixed `Data`
**shape**.

Four consequences to carry into any quotation:

1. **Never** write "the containment property is proved". Write: "it reduces, in
   machine-checked form, to four named obligations plus 26 axioms; that reduction is
   discharged over a class in which containment holds for accounting reasons; and the
   six leaf properties are proved on named bounded families of the real bytecode's
   inputs."
2. **Never** quote a budget without its shape, or a shape without its budget — and if
   you quote a shape, say that the shape class is not node-buildable.
3. **Never** write "`sorry`-free". 64 theorem-position results are closed by the
   `blaster` tactic's `admit`, so their certification is a `✅ Valid` Z3 verdict
   recorded in the build log, not a Lean kernel check. All four top-level theorems
   inherit `sorryAx` through P3.
4. **Do** say that the bytecode is the production bytecode: that is machine-verified
   (§4.1), not asserted.

---

## 2. THE SIX PROPERTIES

All budgets are CEK step budgets baked in by `#prep_uplc`; exceeding one yields
`Error`, which is why a *vacuity probe* at the exact prep term and shape is mandatory
for every accept-hypothesis theorem (§4.2). "Witness K" is the measured step count of
a concrete accepting `ScriptContext` run through the real CEK by `native_decide` —
solver-free evidence that the accepting class is non-empty.

| # | Plain English | Lean theorem(s) — file:line | Budget + shape | Non-vacuity (probe / witness K) | Project axioms |
|---|---|---|---|---|---|
| **P1** | Transfers conserve programmable tokens inside the mini-ledger: for a non-exemptable `(cs,tn)`, the amount at base outputs is at least the amount at base inputs plus the **signed** net mint. | `P1_T1` :223, `P1_T2` :273, `P1_T6` :794, `P1_T7` :839 — `WSC/Props/Shaped/P1Shaped.lean` | **K = 4400**, SHAPES T1/T2/T6/T7 | probes :380/:403/:861/:884 all Falsified; witnesses **2603 / 3572 / 3150 / 3572**; plus `exec_rejects_escape` (a ledger-legal violation the bytecode rejects) | **0** |
| **P2** | An accepted seizure relocates only the seized policy, and that policy stays in the mini-ledger. | `P2a_shaped_structure` :232, `P2b_shaped_containment` :288, joint `P2_shaped` :370 — `WSC/Props/Shaped/P2Shaped.lean` | **K = 3800**, SHAPE S1 | probe :630 Falsified; witnesses **3004 / 3328**; two rejecting controls (escaping seize, stolen staking credential) | **0** |
| **P3** | You cannot spend a mini-ledger UTxO unless the global (transfer) or the seize validator runs in the same transaction. | `P3_base_requires_global_or_seize` :67 (`WSC/Props/P3_Base.lean`) and — the form the composition consumes — `P3_base_requires_global_or_seize_run` :87 (`WSC/Props/P3_BaseRun.lean`) | **K = 600**, **no shape** (the only unshaped leaf) | prep form: probe :112 Falsified. Run form: **its own** probe :123 Falsified *at the run term*. Production golden halts accepting in **208** steps | **0** |
| **P4** | Every accepted mint routes tokens into the mini-ledger or is a pure burn — arm by arm: Local / DelegateTransfer / DelegateSeize / BurnOnly. | arm 1 `P4_local_noEscape_shaped` :203, `P4_local_arm_shaped` :299, `P4_disjunction_at_L1` :349, `P4_local_noEscape_shapedIdx` :407 (`P4LocalShaped.lean`); arm 2 `P4_disjunction_at_DT1` :244; arm 3 `P4_disjunction_at_DS1` :406 (`P4DelegateShaped.lean`); arm 4 `P4Shaped.lean:165` + `P4ShapedIdx.lean:59` | arm 4: **K = 900**, SHAPES M1/M2. arms 1–3: **K = 2500**, SHAPES L1/L2, DT1, DS1 | probes at every one of those shapes Falsified (`P4Shaped:247`, `P4ShapedIdx:103`, `P4LocalShaped:455`/`:545`, `P4DelegateShaped:360`/`:530`); witnesses **784 / 1681 / 1257 / 1466** — each exactly the step count of its production golden; `exec_rejects_escaping_output` | **0** |
| **P4a** | Every accepted mint invokes the token's own minting-logic script (the corollary common to all four arms). | `P4Shaped.lean:121` (M1), `P4ShapedIdx.lean:42` (M2 — withdrawal index symbolic, strictly more general), `P4a_local_shaped` `P4LocalShaped.lean:235` (L1) | as P4's arms | as P4's arms | **0** |
| **P5** | A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ the transaction really references an authentic directory node whose interval covers `cs` (`key < cs < next`). | `P5_shaped_indexed` :209, ∃-form `P5_shaped_exists` :239, ground-truth `P5_shaped_groundtruth` :276 — `WSC/Props/Shaped/P5Shaped.lean` | **K = 1600**, SHAPE G1 | probe :398 Falsified; witness **1541** (`K_is_1541` :497 — halts at 1541, budget-errors at 1540), on a context with **zero** failing `validRewardingContext` conjuncts | **0** (the ground-truth corollary: `Deployed`, `OnChain`, `TS3`) |
| **P6** | Claiming Member is self-penalizing: an accepted Member classification *adds* the positive minted amount to the value that must remain at base outputs. | `P6_shaped_member_adds_to_requirement` :234, `P6_shaped_member_mint_stays_at_base` :259, `P6_shaped_noBaseInputs` :209 — `WSC/Props/Shaped/P6Shaped.lean` | **K = 3300**, SHAPE G6 | probe :363 Falsified; witness **2837** (:439); discriminating pair `exec_rejects_escape_under_member` / `exec_accepts_same_escape_under_nonmember` | **0** (`P6_shaped_noBaseInputs` is pure Lean — the only headline the kernel fully checks) |

Precise scope caveats, one per property:

* **P1.** Bounded by K = 4400 and by four shapes. Only **one of the three containment
  dispatch paths** in the validator is covered at UPLC (Path A); Paths B/C and
  input-side aggregation (≥ 2 mini-ledger inputs) are blocked by Blaster defect
  **D6** (§3.3, §5). Path C is proved at Lean level only (`pathC_sound`). The
  exemption hypothesis is carried in raw-decode vocabulary
  (`Model.coveringNodeExists … = false`); bridging it to ground truth costs the axiom
  `TS3`. **P1 is aggregate containment at the base *payment* credential — not
  per-holder ownership**; intra-mini-ledger transfers between holders are enforced by
  per-policy transfer-logic scripts, outside this formalization.
* **P2.** Conjunct (b) is the **sharpest shape-dependence in the library**: it is
  false-in-general on the source model (two machine-checked counterexamples —
  `ptokenPairsContain` is unsound with duplicate token names or unsorted maps) and
  closes at SHAPE S1 only because S1 gives every value exactly one policy and one
  token name. Do not generalize it by inspection. P2 does **not** claim the directory
  node the redeemer points at is authentic. Conjunct (a) additionally holds on the
  source model for all contexts, at the cost of one whole-validator faithfulness
  axiom.
* **P3.** Covers base spends whose run halts within 600 steps. Its conclusion is "the
  credential is in `txInfoWdrl`"; upgrading that to "the validator actually ran" is
  the ledger axiom `LR_WDRL_RUNS_VALIDATOR`, not part of the proof. This is the one
  leaf every top-level theorem actually consumes, and the reason they all carry
  `sorryAx`.
* **P4.** Four theorems over four pairwise-disjoint shape classes is **not** one
  theorem over a symbolic redeemer tag (that goal returns `Undetermined`). Arm 1 is
  the strong one — the policy's *own* no-escape scan over every output of the
  transaction, in ground-truth vocabulary. **Arms 2 and 3 prove strictly less**: only
  that a sibling validator *runs*. The registration conjunct at SHAPE L2 is
  `Undetermined`.
* **P4a.** Same bounds as P4. Fully symbolic: `Undetermined` after 3,208 s.
* **P5.** **Escape-critical: P5 is exactly as strong as the `DirWF` assumption.** Its
  postcondition is the covering-node witness, *not* `¬ IsRegistered`; the bridge to
  "not registered" is a proved theorem (`covering_node_excludes_registration`, no
  `sorryAx`) *given* `DirWF`. P5 is proved **one node index at a time**: freeing the
  NonMember node index (SHAPE G3) returns `Undetermined` after 906 s on a class the
  probe shows is non-empty, and freeing both redeemer indices (SHAPE G2) is genuinely
  **Falsified** with a counterexample that names the wrong object (on chain it is
  excluded by the params-NFT uniqueness axiom `TS2` — deliberately unavailable to a
  bytecode theorem). Requires the unpushed PlutusCoreBlaster branch (§3.3).
* **P6.** **The cautionary result of the whole campaign.** P6 was first stated at
  budget 2500, returned `✅ Valid`, and was **genuinely vacuous** — the shape class was
  accept-UNSAT and only the mandatory probe caught it
  (`WSC/Shaped/Probe/G6Vacuous2500.lean`, a stanza that *expects* `Valid`). No
  accept-hypothesis theorem in this library may be quoted without its probe.
* **P2′** ("a seized-policy mint cannot bypass the seize") is **deferred**: the
  DelegateSeize arm is proved at SHAPE DS1, but it concludes only that the seize
  validator runs. The binding statement needs P2 and P4-arm-3 in one theorem; nobody
  has written it.

**And the bound that applies to all seven rows above except P3:** each shape class is
provably **not node-buildable** (§1). The shaped results are exhaustive symbolic checks
of the real compiled code over named bounded families of `Data` skeletons; the
intersection of those families with contexts a Cardano node would actually construct
is currently empty. That does not make them worthless — they exercise the real
program, and each shape's witness K tracks a real golden's measured K (784 / 1257 /
1466 / 1681 / 1541 / 2837 / 3004 against goldens at 208 / 1554 / 2570 / 3262 / 3726 /
4647) — but it does mean **no shaped result yet constrains the validators' behaviour on
a single realizable transaction**, and closing that needs the shapes re-cut (§3.3
item 1).

---

## 3. PROVED vs ASSUMED vs OPEN

### 3.1 Proved

Verified in an independent clean-room rebuild (`AUDIT.md` §1): **405 jobs, 98.5 s
wall, 1.65 GB peak, 101 solver verdicts — 66 `✅ Valid` + 35 `✅ Expected Falsified`,
zero `⚠️ Undetermined`, zero `❌`, zero errors**, and the 101 reconcile exactly against
the source stanzas (35 + 2 + 64), per file, which is what rules out a silently skipped
proof.

* The **six leaf properties** of §2, against the real compiled bytecode, at the stated
  budgets and shapes, each with a full control set: negative control, tightness
  stanza, mandatory vacuity probe, and (14 of 15 theorem groups) a solver-free
  concrete CEK witness. **No shaped theorem uses any project axiom** —
  machine-verified: there is no `axiom` declaration anywhere under `WSC/Prep/`,
  `WSC/Shaped/` or `WSC/Props/Shaped/`.
* The **composition**, as a reduction: `preservation`, `nonEscape_of_registered`,
  `top_claim`, `no_programmable_tokens_outside_mini_ledger` over an explicit `LeafSet`
  hypothesis bundle — **and** discharged over `ContainedTx` by `containedLeaves`,
  giving `containment_on_contained_class` and `no_escape_on_contained_class` with no
  `LeafSet` hypothesis (§1 for what that does and does not mean), plus
  `containment_on_inert_class_of_nopre`, the variant carrying only the weakest leaf as
  a hypothesis.
* **The class is inhabited**, non-degenerately: `containedTx_witness` +
  `contained_witness_moves_tokens`, 0 project axioms.
* **The negative result that redirected the campaign:** every shaped class is empty as
  a class of ledger transactions (`ShapeRealizability.lean`) — `t1_class_is_empty`
  unconditionally, the rest under the Conway `MissingRedeemers` rule, which is stated
  as a `Prop` and deliberately **not** an axiom.
* The **shape bridge** for all 16 shaped preps (`WSC/ShapeBridge.lean`, 25 verdicts):
  the inputs-level and `exec`-level forms are **kernel-checked `rfl`, no `sorryAx`**
  (`[propext, Classical.choice, Quot.sound]`; `inputs_M1` depends on no axioms at
  all), and the `prop`-level form is `blaster`-proved for 16/16.
* **Every non-vacuity obligation in the library**: `BaseNonVacuous`@600,
  `MintingNonVacuous`@900 and @2500, `GlobalNonVacuous`@1600/3300/4400,
  `SeizeNonVacuous`@3800 — all `native_decide` on the real CEK with **0 project axioms
  and no `sorryAx`** (`Composition.lean` §7, `Props/Shaped/NonVacuity.lean`).
* Supporting theorems that were previously assumed:
  `covering_node_excludes_registration` and `covering_excludes_registeredIn`
  (**proved**, 0 project axioms); the sum vocabulary bridges (`outSum ≡ sumOutsIf`,
  `contain_iff_modelSums`); `LR_BALANCE_SLOT`'s exact statement, derived from `LR7`
  plus two named residues.
* Two **source-model** routes that quantify over *all* contexts and all step counts
  (P1/P6 on the global model, P2a on the seize model), each at the cost of one
  whole-validator hand-transcription axiom, backed by source-line citations and golden
  differential agreement (global 4/4, seize 13/13, including rejecting vectors).
  Neither route dominates the shaped route: the model route trades a transcription for
  the quantifier; the shaped route trades the quantifier for no transcription.

### 3.2 Assumed — the 26 project axioms every top-level theorem depends on

Reproduce the census with `lake build WSC.Shaped.Probe.U3Census` plus the eight
`#print axioms` commands at the end of `WSC/Composition.lean`. Read 26 as a **floor,
not a ceiling**: the library declares **50** axioms, and the 24 that no top-level
theorem reaches (`LR1`–`LR7`, `LR_BUDGET_{minting,global,seize}`, `DIRWF`, `TS1`–`TS5`,
`TS_MINTING_IDENTITY`, `nodeStepsSeize`, and the two faithfulness axioms) are exactly
what a *bytecode-based* discharge of the general-class leaves would add.

From `WSC/Honest.lean` (16):

| Axiom | Plain-English gloss | Discharged by |
|---|---|---|
| `OnChain` | "This Lean `ScriptContext` is one a real node actually built, and its fields faithfully mirror that transaction." | Never — it is the model↔chain bridge. |
| `Deployed` | "These parameters are the audited production deployment's parameters." | Deployment audit. |
| `LR_CTX` | "Every context a real node builds satisfies CLAB's `validScriptContext`" — the per-transaction normalization every leaf takes as its hypothesis. | Trusting the ledger; every conjunct is mapped to a cited ledger rule in `WSC/LR-CTX-AUDIT.md`. **Known missing row: `MissingRedeemers`** — the gap `ShapeRealizability.RedeemerCoverage` states. |
| `NONNEG` | "No UTxO this transaction reads holds a negative quantity of any asset." | Trusting the ledger. |
| `LR_MINT_RUNS_POLICY` | "If a policy id appears in the mint field, the ledger ran that policy and required it to succeed." | Trusting the ledger (Conway UTXOW scripts-needed). |
| `LR_SPEND_RUNS_VALIDATOR` | "Spending a script-payment-credential UTxO runs that spending validator." | Trusting the ledger. |
| `LR_WDRL_RUNS_VALIDATOR` | "A script-credential withdrawal entry — even for zero — means that stake validator ran and succeeded." | Trusting the ledger. This is what makes P3's conclusion mean "the validator ran". |
| `LR_BUDGET_base` | "If the base validator's real run halts within `K` CEK steps, the node's verdict equals the metered term's verdict." Since task A1 the metered term is `Runs.baseRun K` — a two-line definition naming the imported flat, the audited inputs function and the budget, so what is assumed is readable. | A budget-monotonicity meta-theorem about `runSteps` that the substrate does not provide. |
| `NodeAcceptsBase`, `NodeAcceptsMinting`, `NodeAcceptsGlobal`, `NodeAcceptsSeize` | "The real node accepted this invocation of validator X on this transaction." | Never — they *are* the "a node ran this script" interface. |
| `nodeStepsBase`, `nodeStepsMinting`, `nodeStepsGlobal` | "The number of CEK steps the real machine takes on validator X" — abstract, because the model cannot compute it for a symbolic context. | Never (same interface). |
| `mlhPolicyId` | "The policy id of the issuance-policy instance at `(paramsCS, mintingLogicHash)`" — abstract because Lean does not compute blake2b script hashes. | The out-of-band flat-hash gate (E7), now re-verified (§4.1). |

From `WSC/Composition.lean` (all 10):

| Axiom | Plain-English gloss | Discharged by |
|---|---|---|
| `LedgerStep` | Declared, not defined: the per-transaction ledger state transition. Defining it would mean building a Cardano ledger in Lean. | Never — everything used about it is one of the four `lr_*` axioms. |
| `Genesis` | Declared, not defined: the predicate naming the deployment's genesis state. | Deployment audit. |
| `lr_utxo_semantics` | "Out-of-base holdings after the transaction = before − what it spent out of base + what it produced out of base." | Trusting the ledger (it *is* the Conway UTXO rule). |
| `lr_inputs_in_ledger` | "Everything the transaction spends or references was in the pre-state UTxO set." | Trusting the ledger. |
| `lr_registration_source` | "A policy registered after the transaction was registered before it, or by one of its outputs" — makes the quantifier over the growing registry sound. | Trusting the ledger. |
| `LR_BALANCE_SLOT` | Per-`(cs,tn)` value conservation for one transaction, in the composition's vocabulary. | **Derivable, not primitive**: `LR_BALANCE_SLOT_of_valueAlgebra` proves its exact statement from `LR7` plus two uninstantiated `CardanoLedgerApi` residues (`ValueAlgebra`, `LedgerCanon`). |
| `NONNEG_L` | "No UTxO anywhere in the ledger holds a negative quantity." | Trusting the ledger. |
| `DIRWF_L` | Ledger-wide directory well-formedness (four conjuncts: insert-only, key-uniqueness, NFT-name = node-key datum binding, interval non-overlap). | **U10** (`mkDirectoryNodeMP` at UPLC + lift over history). **Escape-critical: the claim is exactly as strong as this.** |
| `ts_genesis` | "The deployment's genesis state satisfies the invariant." | Inspect the genesis transaction. |
| `ts_minting_identity_L` | "Every policy registered in the ledger really is an instance of the issuance policy at the deployed parameters." | Deployment audit / U10. |

Non-project axioms in the same census: `sorryAx` (the `blaster` tactic's `admit` —
every top-level theorem inherits it through P3), `Lean.ofReduceBool` +
`Lean.trustCompiler` (`native_decide`, i.e. the compiler, used by every concrete CEK
witness), and the three Lean-standard `propext` / `Classical.choice` / `Quot.sound`.
**Not expressible at all:** the collateral exit route — PlutusV3 `TxInfo` has no
collateral field, so it must be closed outside this model.

### 3.3 Open

1. **The general-class `LeafSet`, and the shape re-cut it now depends on.**
   `containedLeaves` discharges all four fields over `ContainedTx` using no UPLC
   result (§1). For the general class the four fields stand: ingredients proved for
   two (`leafP1_of_shapedGlobalContainment`, `p4_disjuncts_of_custody`), each with an
   unproved residue; `p2` needs an unwritten "structure preserved ⟹ contained" lemma;
   `nopre` ("no tokens before registration") needs the full P4 over a symbolic
   redeemer plus trace induction. **The blocking prerequisite is a shape re-cut**: the
   shaped route to those fields is closed by class emptiness, not by plumbing.
   *Sized, with a template from a real vector:* the cheapest realizable shape is
   modelled by the golden `transfer-nonmember-covering-node` (**one** script
   withdrawal, **two** redeemer entries), so shrink each shape's withdrawal map to the
   one script credential the validator needs, add its matching `Rewarding` entry, and
   add a `Spending` entry wherever the shape spends a script input. Cost: one new
   `#prep_uplc` per shape (≈1–2 s, budget-independent) plus re-verification of every
   theorem over it; open risk is that a multi-entry redeemer map enlarges the solver
   residual.
2. **No shape-coverage argument.** `SHAPE-BRIDGE.md` §10 enumerates three routes and
   offers none; `ShapeBridge.M1Covers` is recorded **false as stated**. §2's P2b caveat
   shows this is not pedantry, and item 1's emptiness result means any future coverage
   argument must make the classes inhabited first.
3. **The shape bridge is proved and HALF consumed.** `Honest.lean`'s four
   `LR_BUDGET_*` axioms are restated against the kernel-checked `Runs.XRun K` form
   (`WSC/Runs.lean` — a new leaf module, because the definitions had to leave
   `ShapeBridge.lean` to break an import cycle), so the ledger side names exactly the
   term the 16 `exec_<S>` `rfl`s land on, at every budget. `GlobalPreppedAt` is
   deleted. **No `bridge_<S>` is applied to anything**, and item 1 explains why the
   consumer never arrived. Two honest notes a reviewer should have: restating those
   axioms substituted one unproved assumption for another (`appliedX.prop` vs
   `Runs.XRun K` — neither implies the other) and bought *auditability*, not logical
   strength; and only `LR_BUDGET_base` at K = 600 is ever applied, so six of the seven
   published budgets are inert (`AUDIT.md` §7.1, §8 F15).
   **U1's residual**, stated precisely and deliberately *not* axiomatized:
   `PropExecFaithful` — the shaped theorems are about the optimizer's `.prop` term,
   every witness and every measured K runs `.exec`, and `prop = exec` is not
   definitional (`rfl` fails; the failure is kept as evidence). Task A1 removed it from
   ONE path — the base/keystone chain, by restating P3 itself on `Runs.baseRun K_base`
   with a fresh vacuity probe at the run term. Doing the same for all 14 shaped
   theorem groups (each needing its own re-measured probe) is what would delete it
   campaign-wide; that is real proving work and was not done.
4. **Blaster defect D6.** `#prep_uplc` emits kernel-ill-typed `Blaster.dite'` terms
   when a CIP-153 `Value` builtin result stays symbolic (the motive is not updated
   after De Morgan / Bool-polarity rewrites). Reproductions
   `WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` (deliberately non-building,
   imported nowhere). **It blocks SHAPES T3/T4, hence P1's containment dispatch Paths
   B/C and input-side aggregation over ≥ 2 mini-ledger inputs at UPLC.** Needs an
   upstream fix.
5. **Reproducibility: the substrate is not independently checkable.** `lakefile.lean`
   requires PlutusCoreBlaster **by absolute local path** to the **unpushed** branch
   `cip153-value-builtins`, and `lake-manifest.json` records **no revision at all**
   for it — so there is not even a local commit to re-pin against. Without those
   CIP-153 `Value` builtins `programmableLogicGlobal.flat` does not decode (verified
   negative control against PCB `main`: *"Could not decode program!"*), so *every*
   P1/P5/P6 "proved against production bytecode" claim inherits this. Highest
   operational risk in the repository; the fix is to push the branch and pin by full
   rev. (`Blaster` by contrast *is* pinned, rev `59db213c…`.)
6. **`DirWF`/`DIRWF_L` undischarged** (U10) — the single escape-critical assumption,
   and the highest assurance ROI.
7. **Named smaller gaps**: `WSC.LR5` does not entail `seizeCred ∈ txInfoWdrl` from
   `seizeScopedToNodeOf` (isolated as `SeizeWdrlOfScoped`; the *converse* direction of
   the same missing rule is item 1's `RedeemerCoverage`, so one ledger-audit row
   serves both); `ValueAlgebra`/`LedgerCanon` uninstantiated, so `LR_BALANCE_SLOT`
   remains an axiom although its statement is derived; the P2′ obligation; the
   registration conjunct at SHAPE L2; P5 at a free node index (SHAPE G3).
8. **Two documentation defects found by this audit, in files it does not own:** the
   golden cost tables are stale for the two accepting **seize** vectors (§5.3), and
   `WSC/flats/PROVENANCE.md`'s closing note is factually false (§4.1).

---

## 4. WHY THE METHOD IS TRUSTWORTHY — what a skeptic should check, and what we did

### 4.1 The proofs run against the actual production bytecode — now verified end to end

`WSC/flats/*.flat` are the `cborHex` strings copied out of the production TextEnvelope
JSONs (`generated/scripts/unapplied/prod/*.json`) of a `wsc-poc` worktree at a recorded
commit, with **sha256 per file** in `WSC/flats/PROVENANCE.md` (ADDENDUM E7:
script-hash binding is *checked*, not assumed).

**Task A3 re-derived both halves of that chain, which the previous audit had declined
to do.** For all four validators, the sha256 of the `.flat` file equals (i) the value
in `PROVENANCE.md`'s table **and** (ii) the sha256 of the `cborHex` string extracted
from the named production JSON at the recorded commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f`. **4/4 on both counts** (`AUDIT.md` §6.1).
They are the **unapplied** scripts — every deployment parameter is still a lambda and
is supplied Lean-side, so a theorem cannot quietly be about a partially applied term.

The golden vectors were extracted from the same commit and each was verified by
**re-running the actual compiled script** at PV11 through the Haskell ledger evaluator
(`PlutusLedgerApi.V3.evaluateScriptCounting`), requiring `Right budget` for every
accepting vector and `Left CekError` for every rejecting one — and the rejecting
controls double as an **arity proof**, since an under-applied script evaluates to a
lambda and can never produce `Left`.

*Honest gap:* `PROVENANCE.md`'s closing note is stale to the point of being false — it
says `programmableLogicGlobal.flat` does not decode and its `#import_uplc` is commented
out, whereas it is imported and decoded at `WSC/Prep/Global.lean:46` and
`WSC/Prep/Global1600.lean:66`. The table is correct; the note is not.

### 4.2 Vacuity probes are mandatory, and one of them caught a worthless theorem

Every `accept → POST` theorem is vacuous if the accept class is empty — trivially so
past the step budget, and non-trivially when a shape happens to be accept-UNSAT. So
each theorem group ships a probe **at its own prep term and its own shape**.
Re-verified pairing by reading the `applied*.prop` identifier on both sides, not by
trusting docstrings: **15 of 15 groups have a probe, and all 15 report Falsified** (=
non-empty accept class); 14 of 15 also carry a solver-free `native_decide` CEK witness
with a measured K. That includes the group A1 added: `P3_base_requires_global_or_seize_run`
hypothesises `Runs.baseRun K_base` and its probe is stated over the **same run term**,
not over the old prep — a restated theorem needs a restated probe. The two `✅ Valid`
markers that *are* vacuity results are deliberate records, and no theorem is stated at
either term.

The reason this is not ceremony: **SHAPE G6 at budget 2500 returned `✅ Valid` and was
genuinely vacuous.** The probe is the only thing that caught it; the theorem was
restated at 3300 with witness K = 2837.

### 4.3 Ground-truth postconditions (no tautologies)

A hard gate from the start: no postcondition may mention the validator's own computed
accumulator (`expectedValue`, `deltaAccumulator`, …). Independently re-checked line by
line on the three most load-bearing theorems (`AUDIT.md` §5):

* **P1** concludes in `Model.outSum` / `inSum` / `mintSigned` — independent structural
  recursions over the context's own output/input lists, guarded by
  `payCred o == base` and summing CLAB's `valueOf`. The escape route is *real* (SHAPE
  T1 carries a second non-base input and a non-base output, so ledger balance alone
  does not imply the conclusion), with an accepted instance carrying `qEsc = 4 > 0` and
  a ledger-legal violating instance the real CEK rejects.
* **P2b** concludes in `sumOutAtBase` / `sumInAtBase`, again independent recursions;
  nothing from the seize validator's `valueDelta` / `ptokenPairsContain` machinery
  appears. `P2_shaped_gates_are_earned` (✅ Valid) shows the three authentication gates
  are pairs of *distinct* free variables, so the bytecode has to earn them.
* **P4-Local** concludes `noEscape … = true` over a list verified to be *the
  transaction's own output list* (same application, same argument order as the shape's
  `txInfoOutputs`), with both disjuncts live.

The shapes were audited for the same failure mode: e.g. SHAPE G1 keeps the directory
node's authenticating policy and the params datum's published policy as **different**
free variables — reusing one variable would have made half of P5 `rfl`-true.

**The same check applied to `containedLeaves` gives a different, and honestly
reported, answer.** Its four fields are not tautologies (`LR_BALANCE_SLOT`, `NONNEG`
and the trace induction are real content) but they are **not about the validators**:
the class hypothesis is what closes the escape, and the acceptance hypotheses are
provably unused. §1 states the consequence.

### 4.4 Goldens: differential testing against real ledger-evaluated verdicts

13 golden `(validator, params, redeemer, ScriptContext)` vectors — 9 accepting, 4
rejecting — all decoding and round-tripping byte-identically in Lean. They are used
four ways: as anti-vacuity witnesses, as the inputs for K measurement, as the
differential test for the two source models (**global 4/4, seize 13/13 agreement,
including the rejecting vectors** — a model that only agreed on accepting vectors
would be worth much less), and now as the **realizability reference** that told this
audit the shapes' one-entry redeemer maps are a prep artifact rather than a system
defect (§1). All 9 accepting goldens satisfy their matching `validXContext`
**verbatim, no relaxation**, machine-checked in `WSC/Goldens/Audit.lean`; the only 3
FALSE verdicts are the tamper-intrinsic ones. *Honest gap:* these contexts are
**harness-built, not node-captured**, so they corroborate shape, cost and redeemer
coverage, not the `OnChain`/`LR_CTX` axioms; capturing from a running node is the
highest-value remaining fidelity step.

### 4.5 Redeemer-mirror CBOR gates

Every redeemer-conditioned theorem reads the attacker-supplied redeemer through a
hand-written `IsData` mirror. A wrong constructor tag or permuted field order would
leave every such theorem typechecking, proving, and *worthless*. So each mirror is
gated **twice** against off-chain-produced CBOR (`WSC/Goldens/RedeemerGate.lean`): a
byte-identical decode/re-encode round trip (catches shape drift) **and**
`encodesTo <expected value> <golden hex>` (catches a consistently wrong tag, which a
round trip alone cannot see, because it pins the *value*). The two raw-`Data.List`
datum encodings — historically the most error-prone — are gated the same way from the
goldens' inline datums.

### 4.6 Independent cross-validation of the Lean CEK machine

PlutusCoreBlaster's own budget-metered run of each fully applied golden program
reproduces the `ExBudget` recorded by the Haskell ledger evaluator **exactly, to the
unit, CPU and memory, for all 9 accepting goldens** — two independent evaluators (Lean
CEK + PCB cost model vs. `plutus-ledger-api` 1.63) agreeing on 9 programs. CPU-per-step
stays in a narrow 18,132–21,759 band across all four validators, so the step count K is
a measure of the same machine the ledger meters, and the rejecting goldens still `Error`
at 10× budget (so they are not budget starvation). This is the evidence that a CEK step
budget in a `#prep_uplc` is commensurable with real on-chain cost. *Caveat, §5.3:* the
two accepting **seize** rows of that table were measured on vectors that have since been
re-dumped.

### 4.7 Controls, and the discipline about controls

Every property ships a negative control and a `(solve-result: 1)` tightness stanza, and
the shaped layer has real **refutation** power, not just proving power: SHAPE G2
produced a concrete counterexample in 6.6 s on a goal the fully symbolic setting cannot
decide at all, and `mintPos_form_REFUTED` refuted a written specification against the
bytecode (§5.2). One methodological finding is on the record because it bit us: **a
perturbation that looks like a change may be a symmetry of the statement** (swapping two
universally quantified withdrawal credentials returns `Valid`, correctly) — controls must
perturb asymmetrically.

### 4.8 What a skeptic should still refuse to take on trust

`.prop` vs `.exec` for the shaped layer (§3.3 item 3); that a `✅ Valid` build-log line is
a kernel check (it is not — 64 results are `admit`-closed, and 27 modules suppress the
resulting warning so the log count is not a census); the prep-cost figures in
`K-MEASUREMENTS.md` §5.1 (off by ~47× on this substrate, §5.3) and that file's seize
cost/K rows; that the source-model and shaped routes are the same strength; that any
shaped result applies to a transaction a node would build (§1); and that any of this
builds on another machine (§3.3 item 5).

---

## 5. FINDINGS THIS WORK PRODUCED

Formalizing a system finds bugs in the system and in its tooling. These are the ones
this campaign surfaced.

### 5.1 Fixed

* **CardanoLedgerApiBlaster — script-purpose ordering (D1), the most consequential
  one.** CLAB's `validRedeemerMap` used the *Plutus* constructor order for
  `ScriptPurpose`, while the ledger emits `txInfoRedeemers` in
  `ConwayPlutusPurpose AsIx` order and never re-sorts. Consequence:
  `validMintingContext` was **unsatisfiable for any transaction that both spends and
  mints** — i.e. every real programmable-token mint — so *every minting-purpose
  precondition, and therefore every minting-purpose theorem, was vacuous on its own
  target class*. Fixed at the source (`ltScriptPurpose` →
  `Spending < Minting < Certifying < Rewarding < Voting < Proposing`, with a
  `cardano-ledger` citation), and now **exercised**: SHAPE DS1 carries a real 2-entry
  `[Minting, Rewarding]` redeemer map that `validMintingContext` accepts, with a
  Falsified vacuity probe and a concrete accepted witness.
* **CLAB — credential ordering (D2).** `ltCredential` was corrected to the ledger's
  `ScriptCredential < PubKeyCredential` (the *opposite* of PlutusLedgerApi's derived
  order). Predicted to change no golden verdict, and it did not — which confirmed that
  the seize goldens' earlier `validWithdrawals` failures were a harness artifact.
* **wsc-poc — two latent validator-arity bugs spanning four benchmark cases and two
  validators** (branch `fix/benchmark-arity-and-ctx-builder`, commit `c18c525`). Four
  cases applied **2 of a validator's 3 arguments**, with the *context sitting in a
  parameter position*. A partially applied Plutus script evaluates to a **lambda**, and
  the harness scored success as `isRight` — so these cases reported PASS **without
  running a single check**, and their reported cost was the cost of building a closure:
  - `mkProgrammableLogicBase` (3 cases): **560,100 → 4,525,794 CPU (+708%)**, memory
    3,600 → 11,715;
  - `mkProtocolParametersMinting` (catalogue *and* scenario backend):
    **992,100 → 53,932,564 CPU (+5,336%)**, memory 6,300 → 143,435 (+2,177%).
  Cross-checked: the scenario backend's base-spend spec already passed all three
  arguments and already reported exactly 4,525,794, so the broken primary was the only
  outlier; every other application site was audited against its Plutarch signature.
* **wsc-poc — three ScriptContext-builder artifacts** (same commit). The benchmark
  builder emitted contexts no ledger could produce, so the benchmarks were measuring
  impossible transactions and *all 13* extracted goldens failed a ledger-context
  predicate: (a) `txInfoFee = 0` in every context; (b) withdrawal credentials (and the
  matching `Rewarding` redeemer entries) in *insertion* order rather than the ledger's
  `Credential` order; (c) seize residual outputs with **no ada entry**, which min-UTxO
  forbids. The new `buildLedgerShapedScriptContext` entry point fixes all three and
  *errors* rather than emit an impossible context — which caught three further scenarios
  whose inputs exactly matched their outputs, leaving nothing for a fee. This mattered
  for **cost**, not only for shape: the seize path had been under-counting real
  value-parsing and withdrawal-scan work (`SeizeAct1` primary +16.8%, full-transaction
  cost of the 100/150-input seizes +14.2%, and `SeizeAct150` moved from 76.6% to
  **83.5% of the mainnet memory budget**). All 67 wsc-poc unit tests still pass on the
  legacy builder; the 49-case benchmark suite passes on the new one.
* **In-library measurement and hygiene defects**: `K-MEASUREMENTS.md` §5.1's prep-cost
  table is ~47× pessimistic (a `lake env lean` / missing `--load-dynlib` artifact) and
  had already misdirected work — always time with `lake build` (D7);
  `set_option warn.sorry false` in 27 modules makes the build-log `sorry` count a census
  of *unsuppressed warnings only*, so the authoritative instrument is `#print axioms` →
  `sorryAx` (D8); `WSC.ShapeBridge` was outside the default build target, so
  `lake build WSC` had never checked its 25 verdicts; and a defective `LR_BUDGET_seize`
  statement, in which `K` occurred only in the guard so that the axiom collapsed to an
  unbounded claim, was repaired (`AUDIT.md` §7.1(c)).

### 5.2 The two specification corrections the proofs forced

* **P1's `mintPos` form is refuted for burns; the SIGNED form is the correct one.**
  `ARCHITECTURE.md` §3-P1 stated containment with the *positive part* of the mint.
  `P1ShapedWitness.mintPos_form_REFUTED` (`P1Shaped.lean:657`) is a machine-checked
  refutation **against the production bytecode**: a SHAPE-T2 context that burns 4 of a
  registered policy out of a mini-ledger input holding 5, leaving 1 at the mini-ledger
  output, is ledger-legal, is **accepted** by the real CEK at budget 4400 (K = 3572), and
  has `outSum = 1 < 5 = inSum + mintPos`. The signed form (`1 ≥ 5 + (−4)`) holds, and it
  is also the form the Preservation reduction consumes. The specification was wrong; the
  bytecode was right.
* **The directory well-formedness axiom was missing an interval conjunct.** `DirWF` had
  three conjuncts (insert-only, key-uniqueness, NFT-name↔node-key datum binding).
  Key-uniqueness alone does **not** entail that a covering-interval witness
  `key < cs < next` excludes registration, which is exactly what P5's postcondition is
  for. A fourth conjunct — interval **non-overlap** over the transaction's pre-state
  snapshot — was added, and with it the two bridge lemmas became **proved theorems**
  rather than gaps (`covering_node_excludes_registration`,
  `Composition.covering_excludes_ledger_registration`, both with no `sorryAx`). The
  assumption surface is the same size; discharging it is now an implication instead of a
  hole.

### 5.3 Findings about the method itself

* **A shape that is tractable to prep may not be a transaction.** The campaign's
  sharpest self-inflicted finding: to make `#prep_uplc` affordable the redeemer map must
  be baked into the frozen skeleton, and the resulting one-entry map contradicts Conway
  UTXOW's `MissingRedeemers` for any shape that also carries script withdrawals. Proved
  in `ShapeRealizability.lean`, and corroborated here by decoding the production
  goldens, which carry 2–5 redeemer entries. **Anyone using this shaping technique
  elsewhere should check realizability before proving.**
* **A `✅ Valid` verdict can certify an empty theorem.** P6 at budget 2500. Only the
  mandatory probe caught it. The discipline that made the campaign trustworthy is the
  probe requirement, not the verdict count.
* **A measurement artifact can redirect a whole task.** `K-MEASUREMENTS.md` §5.1's 2,143
  s figure for a module that takes 45.5 s caused one task to skip building half the
  library. Measure with the tool you will ship with.

### 5.4 Still open

* **Blaster D6** (§3.3 item 4) — the one blocking tooling defect. Until it is fixed
  upstream, P1 stays on dispatch Path A with a single mini-ledger input at UPLC.
* **The unpushed PlutusCoreBlaster branch, with no recorded revision** (§3.3 item 5).
* **The golden cost tables are stale for the two accepting seize vectors.**
  `WSC/goldens/MANIFEST.md`'s Goldens table and `K-MEASUREMENTS.md` §3 publish
  `seize-1-input` at 51,571,527 CPU / 140,357 mem and
  `seize-2-inputs-partial-with-noise` at 96,841,491 / 251,272, but the current JSONs —
  re-dumped after the builder fix — record **60,231,630 / 163,820** and
  **105,501,594 / 274,735**. Those are exactly the pre-fix values, i.e. the K
  measurement predates the re-dump; every applied golden flat differs byte-wise from
  the one measured, so the "PCB budget = ledger? exact" verdicts and the
  `K = 2,570 / 4,647` step counts in that table describe vectors that have since been
  replaced. Nothing proved depends on them (no theorem consumes a seize golden's K),
  and the direction is favourable — the corrected costs are *higher*, so the true K's
  are lower bounds, which keeps `K_seize = 3800`'s stated limit correct and
  conservative, and makes the corrected ≈3,000 steps for `seize-1-input` *consistent*
  with the shaped P2 witnesses at K = 3004/3328. Re-measure before quoting either.
* **`WSC/flats/PROVENANCE.md`'s closing note is factually false** (§4.1).

---

## 6. HOW TO REPRODUCE

Substrate pins (all four load-bearing):

| Component | Pin |
|---|---|
| Lean | 4.24.0 |
| Z3 | 4.15.2 |
| `Blaster` | git `input-output-hk/Lean-blaster` @ `beta-lambda-cache-optimization`, rev **`59db213ca6396269d2606b7dd9ac2bc26ae7c4ce`** |
| `PlutusCore` (PlutusCoreBlaster) | **local path** `/home/gumbo/iohk/PlutusCoreBlaster`, branch `cip153-value-builtins` — **unpushed, and `lake-manifest.json` records no revision for it** |

```bash
# 1. clean-room rebuild of the whole library
#    expect: 405 jobs, ~98 s wall, 1.65 GB peak, 101 ✅ markers,
#            0 errors, 0 ⚠️/❌, 20 expected `sorry` warnings, 67 WSC modules
cp -a <CLAB checkout> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. the axiom census behind §3.2 (2.7 s warm) — `#print axioms` only, adds no trust surface
lake build WSC.Shaped.Probe.U3Census

# 3. marker / sorry / error census from the log of step 1
grep -o 'WSC/[^ ]*: ✅ [A-Za-z ]*' build.log | wc -l   # expect 101, all ✅
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c      # 66 Valid, 35 Expected Falsified
grep -c "declaration uses 'sorry'" build.log           # expect 20 — NOT a census, see §4.8
grep -c 'error:'                    build.log          # expect 0

# 4. PROVENANCE re-verification (§4.1) — 4/4 on both counts
sha256sum WSC/flats/*.flat
git -C <wsc-poc worktree> show \
  7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum

# 5. CEK step counts of the 13 goldens (3.2 s) — read §5.4 before quoting the seize rows
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# 6. per-conjunct golden validXContext audit
python3 WSC/goldens/ctx-audit/GenCtxAudit.py       && lake env lean CtxAudit.lean
python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py && lake env lean CtxAuditDetail.lean
```

Rules that are not optional:

* **Always time with `lake build`, never `lake env lean`** — the latter omits
  `--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artifact is the
  entire content of defect D7.
* `#prep_uplc` needs `set_option maxHeartbeats 0`, and a `(timeout: n)` caps Z3 only.
* `blaster` closes `Valid` goals via `admit`, so expected `declaration uses 'sorry'`
  warnings are normal; whitelist them, and never add a literal `sorry`.
* Three probe modules (`Shaped/Probe/{T3PrepFAILS,T4PrepFAILS,BridgeProbe2FAILS}.lean`)
  are **deliberately non-building** — the failure *is* the measurement. They are
  imported nowhere; do not "fix" them.
* Any new accept-hypothesis theorem needs a vacuity probe **at its own term and its own
  shape**. A probe at a different term certifies nothing (§4.2).

**E11 reproducibility caveat (binding).** This checkout builds **on one machine only**.
`lakefile.lean` requires PlutusCoreBlaster from an absolute local path on an unpushed
branch, with no revision in the manifest, because the CIP-153 `Value` builtins live only
there and without them `programmableLogicGlobal.flat` does not decode at all (verified
negative control: against PCB `main` the import fails with *"Could not decode
program!"*; against the branch it decodes and the program carries 46 CIP-153 builtin
occurrences out of 282, so the new tags are genuinely consumed). Until the branch is
pushed and the pin changed to a full git rev, **no claim in this document is
independently checkable**, and any external quotation must say so.
