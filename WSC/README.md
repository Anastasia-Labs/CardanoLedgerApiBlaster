# WSC programmable-token containment — what this formalization establishes

**Audience.** A senior engineer or auditor deciding what to believe. Everything
below is cited to a file, a line, or a measurement in this repository. Where a
task report and `WSC/AUDIT.md` disagree, this document follows the audit.

Revision: branch `wsc-containment-proofs`, HEAD `ba72b1e`. Companion documents:
`WSC/AUDIT.md` (independent audit; five censuses and "what a reviewer should not
believe"), `WSC/STATUS.md` (authoritative per-property status),
`WSC/ARCHITECTURE.md` (binding design; ADDENDUM v3 overrides the base text),
`WSC/SHAPING-RESULTS.md`, `WSC/SHAPE-BRIDGE.md`, `WSC/LR-CTX-AUDIT.md`,
`WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md`, `WSC/EXEC-SUMMARY.md` (one page, no
Lean).

---

## 1. THE CLAIM, and exactly what is established

> **The claim.** *In an honest deployment, programmable tokens cannot exist
> outside the mini-ledger — the `programmableLogicBase` payment credential.*

**What is established.** Not the claim. What exists is a machine-checked
**reduction** of it: `WSC.Composition.top_claim` (`WSC/Composition.lean:1608`)
proves "no reachable ledger state holds a registered programmable token outside
the base payment credential" *from* a four-field bundle of leaf obligations
(`LeafSet`) *plus* 26 project axioms — and **no `LeafSet` value is constructed
anywhere in the library** (grep-verified, `AUDIT.md` §3.1), so the top theorem is
an implication with an open antecedent. Underneath it, six leaf properties are
genuinely proved against the **real compiled production bytecode** (the `.flat`
files exported from the production build, decoded and executed by a Lean CEK
machine), each one bounded **twice**: by a concrete CEK step budget `K`, and — for
every property except P3 — by a fixed `Data` **shape** (all list lengths,
constructor tags and `Option`s pinned; every `ByteString`/`Integer` still
symbolic). **There is no shape-coverage argument**, and one shaped result is known
not to generalize past its shape (§3, P2b). The honest description of the leaf
layer is therefore *bounded model checking of the real bytecode, beneath an
axiomatic layer*; the honest description of the whole is *a reduction, with the
leaves proved on named bounded classes and not yet wired into the reduction*.

Three consequences to carry into any quotation:

1. **Never** write "the containment property is proved". Write "it reduces, in
   machine-checked form, to four named obligations plus 26 axioms, and the leaves
   are proved on named bounded transaction classes".
2. **Never** quote a budget without its shape, or a shape without its budget.
3. **Never** write "`sorry`-free". 62 theorem-position results are closed by the
   `blaster` tactic's `admit`, so
   their certification is a `✅ Valid` Z3 verdict recorded in the build log, not a
   Lean kernel check. `top_claim` itself inherits `sorryAx` (through P3).

---

## 2. THE SIX PROPERTIES

All budgets are CEK step budgets baked in by `#prep_uplc`; exceeding one yields
`Error`, which is why a *vacuity probe* at the exact prep term and shape is
mandatory for every accept-hypothesis theorem (§4.2). "Witness K" is the measured
step count of a concrete accepting `ScriptContext` run through the real CEK by
`native_decide` — solver-free evidence that the accepting class is non-empty.

| # | Plain English | Lean theorem(s) — file:line | Budget + shape | Non-vacuity (probe / witness K) | Project axioms |
|---|---|---|---|---|---|
| **P1** | Transfers conserve programmable tokens inside the mini-ledger: for a non-exemptable `(cs,tn)`, the amount at base outputs is at least the amount at base inputs plus the **signed** net mint. | `P1_T1` :223, `P1_T2` :273, `P1_T6` :794, `P1_T7` :839 — `WSC/Props/Shaped/P1Shaped.lean` | **K = 4400**, SHAPES T1/T2/T6/T7 | probes :380/:403/:861/:884 all Falsified; witnesses **2603 / 3572 / 3150 / 3572**; plus `exec_rejects_escape` (a ledger-legal violation the bytecode rejects) | **0** |
| **P2** | An accepted seizure relocates only the seized policy, and that policy stays in the mini-ledger. | `P2a_shaped_structure` :232, `P2b_shaped_containment` :288, joint `P2_shaped` :370 — `WSC/Props/Shaped/P2Shaped.lean` | **K = 3800**, SHAPE S1 | probe :630 Falsified; witnesses **3004 / 3328**; two rejecting controls (escaping seize, stolen staking credential) | **0** |
| **P3** | You cannot spend a mini-ledger UTxO unless the global (transfer) or the seize validator runs in the same transaction. | `P3_base_requires_global_or_seize` :67 — `WSC/Props/P3_Base.lean` | **K = 600**, **no shape** (the only unshaped leaf) | probe :112 Falsified; production golden halts accepting in **208** steps; in-library witness accepted at 600 on both `.exec` :202 and `.prop` :209 | **0** |
| **P4** | Every accepted mint routes tokens into the mini-ledger or is a pure burn — arm by arm: Local / DelegateTransfer / DelegateSeize / BurnOnly. | arm 1 `P4_local_noEscape_shaped` :203, `P4_local_arm_shaped` :299, `P4_disjunction_at_L1` :349, `P4_local_noEscape_shapedIdx` :407 (`P4LocalShaped.lean`); arm 2 `P4_disjunction_at_DT1` :244; arm 3 `P4_disjunction_at_DS1` :406 (`P4DelegateShaped.lean`); arm 4 `P4_burnonly_arm_shaped` `P4Shaped.lean:165`, `P4_burn_only_shapedIdx` `P4ShapedIdx.lean:59` | arm 4: **K = 900**, SHAPES M1/M2. arms 1–3: **K = 2500**, SHAPES L1/L2, DT1, DS1 | probes at every one of those shapes Falsified (`P4Shaped:247`, `P4ShapedIdx:103`, `P4LocalShaped:455`/`:545`, `P4DelegateShaped:360`/`:530`); witnesses **784 / 1681 / 1257 / 1466** — each exactly the step count of its production golden; `exec_rejects_escaping_output` | **0** |
| **P4a** | Every accepted mint invokes the token's own minting-logic script (the corollary common to all four arms). | `P4Shaped.lean:121` (M1), `P4ShapedIdx.lean:42` (M2 — withdrawal index symbolic, strictly more general), `P4a_local_shaped` `P4LocalShaped.lean:235` (L1) | as P4's arms | as P4's arms | **0** |
| **P5** | A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ the transaction really references an authentic directory node whose interval covers `cs` (`key < cs < next`). | `P5_shaped_indexed` :209, ∃-form `P5_shaped_exists` :239, ground-truth `P5_shaped_groundtruth` :276 — `WSC/Props/Shaped/P5Shaped.lean` | **K = 1600**, SHAPE G1 | probe :398 Falsified; witness **1541** (`K_is_1541` :497 — halts at 1541, budget-errors at 1540), on a context with **zero** failing `validRewardingContext` conjuncts | **0** (the ground-truth corollary: `Deployed`, `OnChain`, `TS3`) |
| **P6** | Claiming Member is self-penalizing: an accepted Member classification *adds* the positive minted amount to the value that must remain at base outputs. | `P6_shaped_member_adds_to_requirement` :234, `P6_shaped_member_mint_stays_at_base` :259, `P6_shaped_noBaseInputs` :209 — `WSC/Props/Shaped/P6Shaped.lean` | **K = 3300**, SHAPE G6 | probe :363 Falsified; witness **2837** (:439); discriminating pair `exec_rejects_escape_under_member` / `exec_accepts_same_escape_under_nonmember` | **0** (`P6_shaped_noBaseInputs` is pure Lean — the only headline the kernel fully checks) |

Precise scope caveats, one per property:

* **P1.** Bounded by K = 4400 and by four shapes. Only **one of the three
  containment dispatch paths** in the validator is covered at UPLC (Path A);
  Paths B/C and input-side aggregation (≥ 2 mini-ledger inputs) are blocked by
  Blaster defect **D6** (§3, §5). Path C is proved at Lean level only
  (`pathC_sound`). The exemption hypothesis is carried in raw-decode vocabulary
  (`Model.coveringNodeExists … = false`); bridging it to ground truth costs the
  axiom `TS3` (`Composition.lean` §7.1). **P1 is aggregate containment at the base
  *payment* credential — not per-holder ownership**; intra-mini-ledger transfers
  between holders are enforced by per-policy transfer-logic scripts, outside this
  formalization.
* **P2.** Conjunct (b) is the **sharpest shape-dependence in the library**: it is
  false-in-general on the source model (two machine-checked counterexamples —
  `ptokenPairsContain` is unsound with duplicate token names or unsorted maps) and
  closes at SHAPE S1 only because S1 gives every value exactly one policy and one
  token name. Do not generalize it by inspection. P2 does **not** claim the
  directory node the redeemer points at is authentic. Conjunct (a) additionally
  holds on the source model for all contexts, at the cost of one
  whole-validator faithfulness axiom.
* **P3.** Covers base spends whose run halts within 600 steps. Its conclusion is
  "the credential is in `txInfoWdrl`"; upgrading that to "the validator actually
  ran" is the ledger axiom `LR_WDRL_RUNS_VALIDATOR`, not part of the proof. This
  is the one leaf `top_claim` actually consumes, and the reason `top_claim`
  carries `sorryAx`.
* **P4.** Four theorems over four pairwise-disjoint shape classes is **not** one
  theorem over a symbolic redeemer tag (that goal returns `Undetermined`). Arm 1
  is the strong one — the policy's *own* no-escape scan over every output of the
  transaction, in ground-truth vocabulary. **Arms 2 and 3 prove strictly less**:
  only that a sibling validator *runs*. The registration conjunct at SHAPE L2 is
  `Undetermined`. **Budget-bridge gap:** the published minting bridge is at 900
  only, below the 1257/1466/1681 that arms 1–3 cost.
* **P4a.** Same bounds as P4. Fully symbolic: `Undetermined` after 3,208 s.
* **P5.** **Escape-critical: P5 is exactly as strong as the `DirWF` assumption.**
  Its postcondition is the covering-node witness, *not* `¬ IsRegistered`; the
  bridge to "not registered" is a proved theorem
  (`covering_node_excludes_registration`, no `sorryAx`) *given* `DirWF`. P5 is
  proved **one node index at a time**: freeing the NonMember node index (SHAPE G3)
  returns `Undetermined` after 906 s on a class the probe shows is non-empty, and
  freeing both redeemer indices (SHAPE G2) is genuinely **Falsified** with a
  counterexample that names the wrong object (on chain it is excluded by the
  params-NFT uniqueness axiom `TS2` — deliberately unavailable to a bytecode
  theorem). Requires the unpushed PlutusCoreBlaster branch (§3).
* **P6.** **The cautionary result of the whole campaign.** P6 was first stated at
  budget 2500, returned `✅ Valid`, and was **genuinely vacuous** — the shape class
  was accept-UNSAT and only the mandatory probe caught it
  (`WSC/Shaped/Probe/G6Vacuous2500.lean`, a stanza that *expects* `Valid`). No
  accept-hypothesis theorem in this library may be quoted without its probe.
* **P2′** ("a seized-policy mint cannot bypass the seize") is **deferred**: the
  DelegateSeize arm is proved at SHAPE DS1, but it concludes only that the seize
  validator runs. The binding statement needs P2 and P4-arm-3 in one theorem;
  nobody has written it.

---

## 3. PROVED vs ASSUMED vs OPEN

### 3.1 Proved

Verified in an independent clean-room rebuild (`AUDIT.md` §1): 401 jobs, **93.7 s**
wall, **98 solver verdicts — 64 `✅ Valid` + 34 `✅ Expected Falsified`, zero
`⚠️ Undetermined`, zero `❌`, zero errors**, and the 98 reconcile exactly against
the source stanzas (34 + 2 + 62), which is what rules out a silently skipped
proof.

* The **six leaf properties** of §2, against the real compiled bytecode, at the
  stated budgets and shapes, each with a full control set: negative control,
  tightness stanza, mandatory vacuity probe, and (13 of 14 theorem groups) a
  solver-free concrete CEK witness. **No shaped theorem uses any project axiom** —
  machine-verified: there is no `axiom` declaration anywhere under `WSC/Prep/`,
  `WSC/Shaped/` or `WSC/Props/Shaped/`.
* The **composition**, as a reduction: `preservation`, `nonEscape_of_registered`,
  `top_claim`, `no_programmable_tokens_outside_mini_ledger`
  (`WSC/Composition.lean`), over an explicit `LeafSet` hypothesis bundle.
* The **shape bridge** for all 16 shaped preps (`WSC/ShapeBridge.lean`, 25
  verdicts): the inputs-level and `exec`-level forms are **kernel-checked `rfl`,
  no `sorryAx`** (`[propext, Classical.choice, Quot.sound]`; `inputs_M1` depends on
  no axioms at all), and the `prop`-level form is `blaster`-proved for 16/16.
* Supporting theorems that were previously assumed:
  `covering_node_excludes_registration` and `covering_excludes_registeredIn`
  (**proved**, 0 project axioms); the sum vocabulary bridges
  (`outSum ≡ sumOutsIf`, `contain_iff_modelSums`); `LR_BALANCE_SLOT`'s exact
  statement, derived from `LR7` plus two named residues;
  `Composition.baseNonVacuous` and `mintingNonVacuous`.
* Two **source-model** routes that quantify over *all* contexts and all step
  counts (P1/P6 on the global model, P2a on the seize model), each at the cost of
  one whole-validator hand-transcription axiom, backed by source-line citations
  and golden differential agreement (global 4/4, seize 13/13, including rejecting
  vectors). Neither route dominates the shaped route: the model route trades a
  transcription for the quantifier; the shaped route trades the quantifier for no
  transcription.

### 3.2 Assumed — the 26 project axioms `top_claim` depends on

Reproduce the census with `lake build WSC.Shaped.Probe.U3Census`. Read 26 as a
**floor, not a ceiling**: the library declares **47** axioms, and the 21 that
`top_claim` does not reach (`LR1`–`LR7`, `LR_BUDGET_{minting,global,seize}`,
`GlobalPreppedAt`, `DIRWF`, `TS1`–`TS5`, `TS_MINTING_IDENTITY`, `nodeStepsSeize`,
and the two faithfulness axioms) are exactly what instantiating the open leaves
would add.

From `WSC/Honest.lean` (16):

| Axiom | Plain-English gloss | Discharged by |
|---|---|---|
| `OnChain` | "This Lean `ScriptContext` is one a real node actually built, and its fields faithfully mirror that transaction." | Never — it is the model↔chain bridge. |
| `Deployed` | "These parameters are the audited production deployment's parameters." | Deployment audit. |
| `LR_CTX` | "Every context a real node builds satisfies CLAB's `validScriptContext`" — the per-transaction normalization every leaf takes as its hypothesis. | Trusting the ledger; every conjunct is mapped to a cited ledger rule in `WSC/LR-CTX-AUDIT.md`. |
| `NONNEG` | "No UTxO this transaction reads holds a negative quantity of any asset." | Trusting the ledger. |
| `LR_MINT_RUNS_POLICY` | "If a policy id appears in the mint field, the ledger ran that policy and required it to succeed." | Trusting the ledger (Conway UTXOW scripts-needed). |
| `LR_SPEND_RUNS_VALIDATOR` | "Spending a script-payment-credential UTxO runs that spending validator." | Trusting the ledger. |
| `LR_WDRL_RUNS_VALIDATOR` | "A script-credential withdrawal entry — even for zero — means that stake validator ran and succeeded." | Trusting the ledger. This is what makes P3's conclusion mean "the validator ran". |
| `LR_BUDGET_base` | "If the base validator's real run halts within 600 CEK steps, the node's verdict equals the budgeted term's verdict." | A budget-monotonicity meta-theorem about `runSteps` that the substrate does not provide. |
| `NodeAcceptsBase`, `NodeAcceptsMinting`, `NodeAcceptsGlobal`, `NodeAcceptsSeize` | "The real node accepted this invocation of validator X on this transaction." | Never — they *are* the "a node ran this script" interface. |
| `nodeStepsBase`, `nodeStepsMinting`, `nodeStepsGlobal` | "The number of CEK steps the real machine takes on validator X" — abstract, because the model cannot compute it for a symbolic context. | Never (same interface). |
| `mlhPolicyId` | "The policy id of the issuance-policy instance at `(paramsCS, mintingLogicHash)`" — abstract because Lean does not compute blake2b script hashes. | The out-of-band flat-hash gate (E7). |

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
`top_claim` inherits it through P3), `Lean.ofReduceBool` + `Lean.trustCompiler`
(`native_decide`, i.e. the compiler, used by every concrete CEK witness), and the
three Lean-standard `propext` / `Classical.choice` / `Quot.sound`. **Not
expressible at all:** the collateral exit route — PlutusV3 `TxInfo` has no
collateral field, so it must be closed outside this model.

### 3.3 Open

1. **The `LeafSet` is never instantiated** — the gap between "reduction" and
   "proof". Ingredients exist for two of four fields
   (`leafP1_of_shapedGlobalContainment`, `p4_disjuncts_of_custody`), each with an
   unproved residue; `p2` needs an unwritten "structure preserved ⟹ contained"
   lemma; `nopre` ("no tokens before registration") needs the full P4 over a
   symbolic redeemer plus trace induction and is untouched.
2. **No shape-coverage argument.** `SHAPE-BRIDGE.md` §10 enumerates three routes
   and offers none; `ShapeBridge.M1Covers` is recorded **false as stated**. §2's
   P2b caveat shows this is not pedantry.
3. **The shape bridge is proved and now HALF consumed (task A1).** `Honest.lean`'s
   four `LR_BUDGET_*` axioms are restated against the kernel-checked
   `Runs.XRun K` form (`WSC/Runs.lean` — a new leaf module, because the definitions
   had to leave `ShapeBridge.lean` to break an import cycle), so the ledger side
   names exactly the term the 16 `exec_<S>` `rfl`s land on, at every budget.
   `GlobalPreppedAt` is deleted, all five previously-open non-vacuity obligations
   are theorems, and three new K constants (2500 / 3300 / 3800) are published with
   proved non-vacuity. **`Composition.lean`'s `LeafSet` is still un-instantiated**,
   so no `bridge_<S>` is applied to anything — item 1 above is the binding gap, not
   this one. **U1's residual**, stated precisely and deliberately *not*
   axiomatized: `PropExecFaithful` — the theorems are about the optimizer's
   `.prop` term, every witness and every measured K runs `.exec`, and
   `prop = exec` is not definitional (`rfl` fails; the failure is kept as
   evidence). Tier A (6 shapes at the three published budgets) does not need it;
   Tier B (10 shapes at 2500/3300/3800/4400, where no unshaped prep is
   affordable) does. Mitigation in place: every vacuity probe is stated on
   `.prop`. **A1 removed this residual from ONE path only** — the base/keystone
   chain, by restating P3 itself on `Runs.baseRun K_base`
   (`WSC/Props/P3_BaseRun.lean`, `✅ Valid`, with a fresh vacuity probe at the run
   term, also green). Restating the axiom does NOT remove the residual, because the
   shaped P-theorems are still stated on `.prop`; doing the same for all 14 shaped
   theorem groups (each needing its own re-measured vacuity probe) is what would
   delete it campaign-wide, and it is real proving work that was not done.
4. **Blaster defect D6.** `#prep_uplc` emits kernel-ill-typed `Blaster.dite'`
   terms when a CIP-153 `Value` builtin result stays symbolic (the motive is not
   updated after De Morgan / Bool-polarity rewrites). Reproductions:
   `WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` (deliberately non-building,
   imported nowhere). **It blocks SHAPES T3/T4, hence P1's containment dispatch
   Paths B/C and input-side aggregation over ≥ 2 mini-ledger inputs at UPLC.**
   Needs an upstream fix.
5. **Reproducibility: the substrate is not independently checkable.**
   `lakefile.lean` pins PlutusCoreBlaster **by absolute local path** to the
   **unpushed** branch `cip153-value-builtins` @ `9f9ca8c` (ARCHITECTURE E11).
   Without those CIP-153 `Value` builtins the global validator's flat does not
   even decode, so *every* P1/P5/P6 "proved against production bytecode" claim
   inherits this. Highest operational risk in the repository; the fix is to push
   the branch and re-pin by full rev.
6. **`DirWF`/`DIRWF_L` undischarged** (U10) — the single escape-critical
   assumption, and the highest assurance ROI.
7. **Budget bridges incomplete**: the minting bridge is published at 900 while
   P4's arms 1–3 cost 1257/1466/1681; `LR_BUDGET_seize` carries no `K` and is
   unusable by construction; `GlobalNonVacuous` at the unshaped 1600 prep is
   *proved* in `ShapeBridge` but still recorded open in `Honest.lean` (a
   one-`:=` repair blocked only by an import cycle).
8. **Named smaller gaps**: `WSC.LR5` does not entail `seizeCred ∈ txInfoWdrl` from
   `seizeScopedToNodeOf` (isolated as `SeizeWdrlOfScoped`, needs a strengthened
   ledger axiom with a `Conway/TxInfo.hs` audit row); `ValueAlgebra`/`LedgerCanon`
   uninstantiated, so `LR_BALANCE_SLOT` remains an axiom although its statement is
   derived; `LR_BALANCE_SLOT` should be a theorem; the P2′ obligation; the
   registration conjunct at SHAPE L2; P5 at a free node index (SHAPE G3).
9. **Documentation drift found while writing this file** (see §5.3): the golden
   cost tables in `WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md` still publish
   pre-fix numbers for the two accepting **seize** goldens.

---

## 4. WHY THE METHOD IS TRUSTWORTHY — what a skeptic should check, and what we did

### 4.1 The proofs run against the actual production bytecode

`WSC/flats/*.flat` are the `cborHex` strings copied verbatim out of the
production TextEnvelope JSONs (`generated/scripts/unapplied/prod/*.json`) of a
`wsc-poc` worktree at a recorded commit, with **sha256 per file** in
`WSC/flats/PROVENANCE.md` (ADDENDUM E7: script-hash binding is *checked*, not
assumed). They are the **unapplied** scripts — every deployment parameter is still
a lambda and is supplied Lean-side, so a theorem cannot quietly be about a
partially applied term. The golden vectors were extracted from the same commit and
each was verified by **re-running the actual compiled script** at PV11 through the
Haskell ledger evaluator (`PlutusLedgerApi.V3.evaluateScriptCounting`), requiring
`Right budget` for every accepting vector and `Left CekError` for every rejecting
one — and the rejecting controls double as an **arity proof**, since an
under-applied script evaluates to a lambda and can never produce `Left`.
*Honest gap:* the U3 audit did **not** re-verify the provenance chain itself
(`AUDIT.md` §5.4), and `PROVENANCE.md`'s closing note is stale (§5.3).

### 4.2 Vacuity probes are mandatory, and one of them caught a worthless theorem

Every `accept → POST` theorem is vacuous if the accept class is empty — trivially
so past the step budget, and non-trivially when a shape happens to be
accept-UNSAT. So each theorem group ships a probe **at its own prep term and its
own shape**. Re-verified pairing by reading the `applied*.prop` identifier on both
sides, not by trusting docstrings: **14 of 14 groups have a probe, and all 14
report Falsified** (= non-empty accept class); 13 of 14 also carry a solver-free
`native_decide` CEK witness with a measured K. The two `✅ Valid` markers that *are*
vacuity results are deliberate records, and no theorem is stated at either term.
The reason this is not ceremony: **SHAPE G6 at budget 2500 returned `✅ Valid` and
was genuinely vacuous.** The probe is the only thing that caught it; the theorem
was restated at 3300 with witness K = 2837.

### 4.3 Ground-truth postconditions (no tautologies)

A hard gate from the start: no postcondition may mention the validator's own
computed accumulator (`expectedValue`, `deltaAccumulator`, …). Independently
re-checked line by line on the three most load-bearing theorems (`AUDIT.md` §5):

* **P1** concludes in `Model.outSum` / `inSum` / `mintSigned` — independent
  structural recursions over the context's own output/input lists, guarded by
  `payCred o == base` and summing CLAB's `valueOf`. The escape route is *real*
  (SHAPE T1 carries a second non-base input and a non-base output, so ledger
  balance alone does not imply the conclusion), with an accepted instance carrying
  `qEsc = 4 > 0` and a ledger-legal violating instance the real CEK rejects.
* **P2b** concludes in `sumOutAtBase` / `sumInAtBase`, again independent
  recursions; nothing from the seize validator's `valueDelta` /
  `ptokenPairsContain` machinery appears. `P2_shaped_gates_are_earned` (✅ Valid)
  shows the three authentication gates are pairs of *distinct* free variables, so
  the bytecode has to earn them.
* **P4-Local** concludes `noEscape … = true` over a list verified to be *the
  transaction's own output list* (same application, same argument order as the
  shape's `txInfoOutputs`), with both disjuncts live.

The shapes were audited for the same failure mode: e.g. SHAPE G1 keeps the
directory node's authenticating policy and the params datum's published policy as
**different** free variables — reusing one variable would have made half of P5
`rfl`-true.

### 4.4 Goldens: differential testing against real ledger-evaluated verdicts

13 golden `(validator, params, redeemer, ScriptContext)` vectors — 9 accepting, 4
rejecting — all decoding and round-tripping byte-identically in Lean. They are
used three ways: as anti-vacuity witnesses, as the inputs for K measurement, and
as the differential test for the two source models (**global 4/4, seize 13/13
agreement, including the rejecting vectors** — a model that only agreed on
accepting vectors would be worth much less). All 9 accepting goldens satisfy their
matching `validXContext` **verbatim, no relaxation**, machine-checked in
`WSC/Goldens/Audit.lean`; the only 3 FALSE verdicts are the tamper-intrinsic ones.
*Honest gap:* these contexts are **harness-built, not node-captured**, so they
corroborate shape, not the `OnChain`/`LR_CTX` axioms; capturing from a running
node is the highest-value remaining fidelity step.

### 4.5 Redeemer-mirror CBOR gates

Every redeemer-conditioned theorem reads the attacker-supplied redeemer through a
hand-written `IsData` mirror. A wrong constructor tag or permuted field order
would leave every such theorem typechecking, proving, and *worthless*. So each
mirror is gated **twice** against off-chain-produced CBOR
(`WSC/Goldens/RedeemerGate.lean`): a byte-identical decode/re-encode round trip
(catches shape drift) **and** `encodesTo <expected value> <golden hex>` (catches a
consistently wrong tag, which a round trip alone cannot see, because it pins the
*value*). The two raw-`Data.List` datum encodings — historically the most
error-prone — are gated the same way from the goldens' inline datums.

### 4.6 Independent cross-validation of the Lean CEK machine

PlutusCoreBlaster's own budget-metered run of each fully applied golden program
reproduces the `ExBudget` recorded by the Haskell ledger evaluator **exactly, to
the unit, CPU and memory, for all 9 accepting goldens** — two independent
evaluators (Lean CEK + PCB cost model vs. `plutus-ledger-api` 1.63) agreeing on 9
programs. CPU-per-step stays in a narrow 18,132–21,759 band across all four
validators, so the step count K is a measure of the same machine the ledger
meters, and the rejecting goldens still `Error` at 10× budget (so they are not
budget starvation). This is the evidence that a CEK step budget in a `#prep_uplc`
is commensurable with real on-chain cost.

### 4.7 Controls, and the discipline about controls

Every property ships a negative control and a `(solve-result: 1)` tightness
stanza, and the shaped layer has real **refutation** power, not just proving
power: SHAPE G2 produced a concrete counterexample in 6.6 s on a goal the fully
symbolic setting cannot decide at all. One methodological finding is on the record
because it bit us: **a perturbation that looks like a change may be a symmetry of
the statement** (swapping two universally quantified withdrawal credentials
returns `Valid`, correctly) — controls must perturb asymmetrically.

### 4.8 What a skeptic should still refuse to take on trust

`.prop` vs `.exec` (§3.3 item 3); the `.flat` provenance chain (not re-audited);
that a `✅ Valid` build-log line is a kernel check (it is not — 62 results are
`admit`-closed); the prep-cost figures in `K-MEASUREMENTS.md` §5.1 (off by ~49× on
this substrate, §5.2); that the source-model and shaped routes are the same
strength; and that any of this builds on another machine (§3.3 item 5).

---

## 5. FINDINGS THIS WORK PRODUCED

Formalizing a system finds bugs in the system and in its tooling. These are the
ones this campaign surfaced.

### 5.1 Fixed

* **CardanoLedgerApiBlaster — script-purpose ordering (D1), the most consequential
  one.** CLAB's `validRedeemerMap` used the *Plutus* constructor order for
  `ScriptPurpose`, while the ledger emits `txInfoRedeemers` in
  `ConwayPlutusPurpose AsIx` order and never re-sorts. Consequence:
  `validMintingContext` was **unsatisfiable for any transaction that both spends
  and mints** — i.e. every real programmable-token mint — so *every minting-purpose
  precondition, and therefore every minting-purpose theorem, was vacuous on its own
  target class*. Fixed at the source (`ltScriptPurpose` →
  `Spending < Minting < Certifying < Rewarding < Voting < Proposing`, with a
  `cardano-ledger` citation), and now **exercised**: SHAPE DS1 carries a real
  2-entry `[Minting, Rewarding]` redeemer map that `validMintingContext` accepts,
  with a Falsified vacuity probe and a concrete accepted witness.
* **CLAB — credential ordering (D2).** `ltCredential` was corrected to the
  ledger's `ScriptCredential < PubKeyCredential` (the *opposite* of
  PlutusLedgerApi's derived order). Predicted to change no golden verdict, and it
  did not — which confirmed that the seize goldens' earlier `validWithdrawals`
  failures were a harness artifact, not a real order violation.
* **wsc-poc — two latent validator-arity bugs spanning four benchmark cases and
  two validators** (branch `fix/benchmark-arity-and-ctx-builder`, commit
  `c18c525`). Four cases applied **2 of a validator's 3 arguments**, with the
  *context sitting in a parameter position*. A partially applied Plutus script
  evaluates to a **lambda**, and the harness scored success as `isRight` — so
  these cases reported PASS **without running a single check**, and their reported
  cost was the cost of building a closure:
  - `mkProgrammableLogicBase` (3 cases): **560,100 → 4,525,794 CPU (+708%)**,
    memory 3,600 → 11,715;
  - `mkProtocolParametersMinting` (catalogue *and* scenario backend):
    **992,100 → 53,932,564 CPU (+5,336%)**, memory 6,300 → 143,435 (+2,177%).
  Cross-checked: the scenario backend's base-spend spec already passed all three
  arguments and already reported exactly 4,525,794, so the broken primary was the
  only outlier; every other application site was audited against its Plutarch
  signature.
* **wsc-poc — three ScriptContext-builder artifacts** (same commit). The
  benchmark builder emitted contexts no ledger could produce, so the benchmarks
  were measuring impossible transactions and *all 13* extracted goldens failed a
  ledger-context predicate: (a) `txInfoFee = 0` in every context; (b) withdrawal
  credentials (and the matching `Rewarding` redeemer entries) in *insertion* order
  rather than the ledger's `Credential` order; (c) seize residual outputs with **no
  ada entry**, which min-UTxO forbids. The new `buildLedgerShapedScriptContext`
  entry point fixes all three and *errors* rather than emit an impossible context —
  which caught three further scenarios whose inputs exactly matched their outputs,
  leaving nothing for a fee. This mattered for **cost**, not only for shape: the
  seize path had been under-counting real value-parsing and withdrawal-scan work
  (`SeizeAct1` primary +16.8%, full-transaction cost of the 100/150-input seizes
  +14.2%, and `SeizeAct150` moved from 76.6% to **83.5% of the mainnet memory
  budget**). All 67 wsc-poc unit tests still pass on the legacy builder; the
  49-case benchmark suite passes on the new one.
* **In-library measurement and hygiene defects**: `K-MEASUREMENTS.md` §5.1's
  prep-cost table is ~49× pessimistic (a `lake env lean` / missing `--load-dynlib`
  artifact) and had already misdirected work — always time with `lake build`
  (D7); `set_option warn.sorry false` in 15 modules makes the build-log `sorry`
  count a census of *unsuppressed warnings only*, so the authoritative instrument
  is `#print axioms` → `sorryAx` (D8); `WSC.ShapeBridge` was outside the default
  build target, so `lake build WSC` had never checked its 25 verdicts.

### 5.2 The two specification corrections the proofs forced

* **P1's `mintPos` form is refuted for burns; the SIGNED form is the correct one.**
  `ARCHITECTURE.md` §3-P1 stated containment with the *positive part* of the mint.
  `P1ShapedWitness.mintPos_form_REFUTED` (`P1Shaped.lean:657`) is a machine-checked
  refutation **against the production bytecode**: a SHAPE-T2 context that burns 4
  of a registered policy out of a mini-ledger input holding 5, leaving 1 at the
  mini-ledger output, is ledger-legal, is **accepted** by the real CEK at budget
  4400 (K = 3572), and has `outSum = 1 < 5 = inSum + mintPos`. The signed form
  (`1 ≥ 5 + (−4)`) holds, and it is also the form the Preservation reduction
  consumes. The specification was wrong; the bytecode was right.
* **The directory well-formedness axiom was missing an interval conjunct.**
  `DirWF` had three conjuncts (insert-only, key-uniqueness, NFT-name↔node-key
  datum binding). Key-uniqueness alone does **not** entail that a covering-interval
  witness `key < cs < next` excludes registration, which is exactly what P5's
  postcondition is for. A fourth conjunct — interval **non-overlap** over the
  transaction's pre-state snapshot — was added, and with it the two bridge lemmas
  became **proved theorems** rather than gaps
  (`covering_node_excludes_registration`,
  `Composition.covering_excludes_ledger_registration`, both with no `sorryAx`). The
  assumption surface is the same size; discharging it is now an implication instead
  of a hole.

### 5.3 Still open

* **Blaster D6** (§3.3 item 4) — the one blocking defect. Until it is fixed
  upstream, P1 stays on dispatch Path A with a single mini-ledger input at UPLC.
* **The unpushed PlutusCoreBlaster branch** (§3.3 item 5).
* **New, found while writing this file:** the golden cost tables are stale for the
  two accepting **seize** goldens. `WSC/goldens/MANIFEST.md`'s Goldens table and
  `K-MEASUREMENTS.md` §3 publish `seize-1-input` at 51,571,527 CPU / 140,357 mem
  and `seize-2-inputs-partial-with-noise` at 96,841,491 / 251,272, but the current
  JSONs — re-dumped after the builder fix — record **60,231,630 / 163,820** and
  **105,501,594 / 274,735**. Those are exactly the pre-fix values, i.e. the K
  measurement predates the re-dump; every applied golden flat differs byte-wise
  from the one measured, so the "PCB budget = ledger? exact" verdicts and the
  `K = 2,570 / 4,647` step counts in that table describe vectors that have since
  been replaced. Nothing proved depends on them (no theorem consumes a seize
  golden's K), and the corrected cost implies ≈ 3,000 steps for `seize-1-input`,
  which is *consistent* with the shaped P2 witnesses at K = 3004/3328 — but the
  tables and every downstream quotation of "seize K = 2,570" should be
  re-measured before being used.

---

## 6. HOW TO REPRODUCE

Substrate pins (all four load-bearing):

| Component | Pin |
|---|---|
| Lean | 4.24.0 |
| Z3 | 4.15.2 |
| `Blaster` | git `input-output-hk/Lean-blaster` @ `beta-lambda-cache-optimization` (`59db213`) |
| `PlutusCore` (PlutusCoreBlaster) | **local path** `/home/gumbo/iohk/PlutusCoreBlaster`, branch `cip153-value-builtins` @ `9f9ca8c` — **unpushed** |

```bash
# 1. clean-room rebuild of the whole library
#    expect: 401 jobs, ~94 s wall, 98 ✅ markers, 0 errors, 21 expected `sorry` warnings
cp -a <CLAB checkout> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge

# 2. the axiom census behind §3.2 (2.7 s warm) — `#print axioms` only, adds no trust surface
lake build WSC.Shaped.Probe.U3Census

# 3. marker / sorry / error census from the log of step 1
grep -o 'WSC/[^ ]*: ✅ [A-Za-z ]*' <log>   # expect 98, all ✅
grep -c "declaration uses 'sorry'"  <log>   # expect 21
grep -c '^error:'                   <log>   # expect 0

# 4. CEK step counts of the 13 goldens (3.2 s) — see §5.3 before quoting the seize rows
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure   # git log -1 == 9f9ca8c
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# 5. per-conjunct golden validXContext audit
python3 WSC/goldens/ctx-audit/GenCtxAudit.py       && lake env lean CtxAudit.lean
python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py && lake env lean CtxAuditDetail.lean
```

Rules that are not optional:

* **Always time with `lake build`, never `lake env lean`** — the latter omits
  `--load-dynlib`, runs Blaster interpreted, and is 15–53× slower. That artifact
  is the entire content of defect D7.
* `#prep_uplc` needs `set_option maxHeartbeats 0`, and a `(timeout: n)` caps Z3
  only.
* `blaster` closes `Valid` goals via `admit`, so expected `declaration uses
  'sorry'` warnings are normal; whitelist them, and never add a literal `sorry`.
* Two probe modules (`Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`, plus
  `BridgeProbe2FAILS.lean`) are **deliberately non-building** — the failure *is*
  the measurement. They are imported nowhere; do not "fix" them.

**E11 reproducibility caveat (binding).** This checkout builds **on one machine
only**. `lakefile.lean` requires PlutusCoreBlaster from an absolute local path on
an unpushed branch, because the CIP-153 `Value` builtins live only there and
without them `programmableLogicGlobal.flat` does not decode at all (verified
negative control: against PCB `main` the import fails with *"Could not decode
program!"*; against the branch it decodes and the program carries 46 CIP-153
builtin occurrences out of 282, so the new tags are genuinely consumed). Until the
branch is pushed and the pin changed to a full git rev, **no claim in this
document is independently checkable**, and any external quotation must say so.
