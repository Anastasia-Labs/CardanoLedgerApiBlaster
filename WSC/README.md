# WSC programmable-token containment — what this formalization establishes

**Audience.** A senior engineer or auditor deciding what to believe. Everything below
is cited to a file, a line, or a measurement in this repository. Where a task report
and `WSC/AUDIT.md` disagree, this document follows the audit.

Revision: branch `wsc-containment-proofs`, HEAD = the **C4** commit (stage 9). All
numbers here were re-measured in an independent clean-room rebuild at that revision
(task C4): **429 jobs, 90–103 s wall (two independent runs), 158 solver verdicts
(101 `✅ Valid` + 57 `✅ Expected Falsified`), 0 errors, 0 `⚠️`/`❌`.**

Companion documents: `WSC/AUDIT.md` (**authoritative** — the clean-room re-audit, five
censuses, the provenance re-verification, honesty-regression checks on stage 9, ranked
findings, and "what a reviewer should not believe"), `WSC/STATUS.md` (per-property
status), `WSC/ARCHITECTURE.md` (binding design; ADDENDUM v3 overrides the base text),
`WSC/SHAPING-RESULTS.md`, `WSC/SHAPE-BRIDGE.md`, `WSC/LR-CTX-AUDIT.md`,
`WSC/goldens/{MANIFEST,K-MEASUREMENTS}.md`, `WSC/EXEC-SUMMARY.md` (one page, no Lean).

---

## 1. THE CLAIM, and exactly what is established

> **The claim.** *In an honest deployment, programmable tokens cannot exist outside
> the mini-ledger — the `programmableLogicBase` payment credential.*

**What is established: not the claim.** Three things are, and the gap between them and
the claim is the most important section on this page.

**(a) A machine-checked REDUCTION.** `WSC.Composition.top_claim` proves "no reachable
ledger state holds a registered programmable token outside the base payment
credential" *from* a four-field bundle of leaf obligations (`LeafSet` —
`p1`/`p2`/`p4`/`nopre`) *plus* **26 project axioms**. The reduction itself is real
content: a trace induction, a four-branch case analysis on how a policy can enter or
leave the mini-ledger, and the ledger-balance and non-negativity slots.

**(b) SIX SAFETY PROPERTIES OF THE PRODUCTION BYTECODE**, proved by exhaustive
symbolic execution over named, bounded, **node-realizable** families of transaction
contexts (§2). "Production bytecode" is machine-verified, not asserted: all four
`.flat` files are byte-identical to the `cborHex` of the named unapplied production
scripts at wsc-poc commit `7ae0024b…` (§4.1).

**(c) THE REDUCTION DISCHARGED THREE-QUARTERS OF THE WAY OVER ONE NON-EMPTY CLASS**
— new in stage 9, and the first time a bytecode result does load-bearing work in a
composed result. `WSC.RealizableLeaves.containment_on_realizable_class_of_p2`
(`WSC/Props/Shaped/RealizableLeaves.lean:441`) is `top_claim` at
`Shape := T1RShape hp`, with:

| field | discharged by | acceptance hypothesis used? |
|---|---|---|
| `p1` | **`WSC.P1R_T1`** — the compiled `programmableLogicGlobal` at K = 4400 — via `bridge_T1R` (`:99`) and `WSC.LR_BUDGET_global` (non-vacuity *proved*, not assumed) | **YES** |
| `p4` | the SHAPE: SHAPE T1R's `txInfoMint` is `[]`, so the fourth custody disjunct holds by computation. A pure-transfer transaction mints nothing | **NO** — bound as `_`, deliberately |
| `nopre` | the SHAPE: SHAPE T1R's two outputs carry `NoOutputDatum`, so none is a directory node. A pure-transfer transaction registers nothing | no such hypothesis exists in the field |
| `p2` | **NOT DISCHARGED** — carried as the single remaining hypothesis | — |

so the honest headline is **N = 1**: *one of four leaf obligations is now closed by
the production bytecode, over one non-empty shape class, assuming a second.*

### 1.1 What "non-empty" means here, precisely — and what it does not

This matters because the previous revision of this document could not say it.

* **Before stage 9, every shape class in this library was PROVED EMPTY.** For
  tractability each shape baked a **one-entry** redeemer map while carrying a
  **two-entry, both-script** withdrawal map, and Conway UTXOW's
  `hasExactSetOfRedeemers` requires one redeemer entry per script witness. So the six
  properties were true statements about sets with nothing in them.
  `WSC.ShapeRealizability.t1_class_is_empty` proves this **unconditionally** for
  SHAPE T1, and `t1_no_honest_step` proves the corresponding composed claim carries no
  information. Both are retained, on purpose.
* **Tasks C1/C2 re-cut 11 of the 12 shapes** to carry exactly the entries the rule
  demands — several *shrinking* the withdrawal map to the one script the validator
  actually dereferences — and re-proved every property over them (§2).
* **`WSC.RealizableLeaves.realizable_inhabitant` (`:512`) exhibits a member of the
  class** that satisfies CLAB's `validRewardingContext`, satisfies **both** halves of
  `hasExactSetOfRedeemers` (`redeemersExact`), and is accepted by the real compiled
  bytecode in 2,603 CEK steps. **0 project axioms, no `sorryAx`.**
* **What it does NOT mean.** `WSC.OnChain` is an opaque axiom, so **no term in this
  library can prove any concrete context is genuinely on-chain**, and `HonestTx`
  requires exactly that. Realizability is **NECESSARY, not SUFFICIENT**: fees against
  a real protocol-parameter set, agreement between a withdrawal credential and the
  script actually supplied in the witness set, and the UTxO set the inputs are drawn
  from are all still unmodelled (`WSC.Realizability.Realizable`'s docstring
  enumerates this). The precise claim is: **the one defect audit F2 named is gone, the
  classes are not provably empty, and each has a certified realizable inhabitant** —
  no more.

### 1.2 The gap, in one paragraph

There is still **no shape-coverage argument**: nothing establishes that a real
transaction must have one of the checked layouts. Every bytecode result is bounded
twice — a CEK step budget **and** a fixed `Data` skeleton. `p2` is assumed. Two of the
three discharged leaves are discharged by the narrowness of the class, not by the
code. And the composed result rests on **28** project axioms plus `sorryAx`. For the
general class of transactions that put a programmable token at an off-base output —
i.e. the transactions the claim is *about* — nothing here proves the claim.

---

## 2. THE SIX PROPERTIES

All budgets are CEK step budgets baked in by `#prep_uplc`; exceeding one yields
`Error`, which is why a *vacuity probe at the exact prep term and shape* is mandatory
for every accept-hypothesis theorem (§4.2). "Witness K" is the measured step count of
a concrete accepting `ScriptContext` run through the real CEK by `native_decide` —
solver-free evidence that the accepting class is non-empty. "Realizability" names the
theorem certifying the shape has a node-buildable inhabitant (§1.1).

**Every theorem below is stated over the RE-CUT shape.** The pre-re-cut theorems are
retained in the repository, unchanged and still `✅ Valid`, but they range over classes
now proved empty and **must not be quoted**.

| # | Plain English | Lean theorem(s) — file:line | Budget + shape | Non-vacuity (probe / witness K) | Realizability | Project axioms |
|---|---|---|---|---|---|---|
| **P1** | Transfers conserve programmable tokens inside the mini-ledger: for a non-exemptable `(cs,tn)`, the amount at base outputs is at least the amount at base inputs plus the **signed** net mint. | `P1R_T1` :125, `P1R_T2` :170, `P1R_T6` :218, `P1R_T7` :267 — `WSC/Props/Shaped/P1ShapedR.lean` | **K = 4400**, SHAPES T1R/T2R/T6R/T7R | probes :393/:415/:438/:291 all Falsified; witnesses **2603 / 3572 / 3150 / 3572**; plus `exec_rejects_escape` — a ledger-legal, redeemer-covered violation the bytecode rejects with 4400 steps available | `t1R/t2R/t6R/t7R_realizable` | **0** |
| **P2** | An accepted seizure relocates only the seized policy, and that policy stays in the mini-ledger. | `P2a_R_structure` :160, `P2b_R_containment` :209, `P2_R_gates_are_earned` :261 — `WSC/Props/Shaped/P2ShapedR.lean` | **K = 3800**, SHAPE S1R | probe :494 Falsified; witnesses **3004 / 3328**; `exec_rejects_escape_and_theft` at 20000 steps (genuine rejection, not budget exhaustion) | `s1r_realizable`, `s1r_realizableExact` | **0** |
| **P3** | You cannot spend a mini-ledger UTxO unless the global (transfer) or the seize validator runs in the same transaction. | `P3_base_requires_global_or_seize_run` — `WSC/Props/P3_BaseRun.lean:87` (the form the composition consumes) | **K = 600**, **no shape** — the only unshaped leaf, hence the only one with no realizability question | its **own** probe :123 Falsified *at the run term*; production golden halts accepting in **208** steps | n/a (unshaped) | **0** |
| **P4** | Every accepted mint routes tokens into the mini-ledger or is a pure burn — arm by arm: Local / DelegateTransfer / DelegateSeize / BurnOnly. | arm 1 `P4_local_noEscape_R` :93, `P4_local_arm_R` :177, `P4_disjunction_at_L1R` :214 (`P4LocalShapedR.lean`); arm 2 `P4_delegateTransfer_arm_R` :72, `P4_disjunction_at_DT1R` :126; arm 3 `P4_delegateSeize_arm_R` :250, `P4_disjunction_at_DS1R` :277 (`P4DelegateShapedR.lean`); arm 4 `P4_burn_only_R` :113, `P4_burnonly_arm_R` :131 (`P4ShapedR.lean`), `P4_burn_only_RIdx` :54 (`P4ShapedRIdx.lean`) | arm 4: **K = 900**, SHAPES M1R/M2R. arms 1–3: **K = 2500**, SHAPES L1R, DT1R, DS1R | probes at every one of those shapes Falsified (`P4ShapedR:208`, `P4ShapedRIdx:123`, `P4LocalShapedR:330`, `P4DelegateShapedR:236`/`:395`); witnesses **784 / 1681 / 1257 / 1466** — the first three exactly the step count of their production goldens; `exec_rejects_escaping_output` | `m1r/m2r/l1r/dt1r/ds1r_realizable` | **0** |
| **P4a** | Every accepted mint invokes the token's own minting-logic script (the corollary common to all four arms). | `P4a_R_mint_runs_minting_logic` `P4ShapedR.lean:93`; `P4a_RIdx_mint_runs_minting_logic` `P4ShapedRIdx.lean:36` (withdrawal index symbolic — strictly more general); `P4a_local_R` `P4LocalShapedR.lean:122` | as P4's arms | as P4's arms | as P4's arms | **0** |
| **P5** | A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ the transaction really references an authentic directory node whose interval covers `cs` (`key < cs < next`). | `P5R_shaped_indexed` :138, ∃-form `P5R_shaped_exists` :167, ground-truth `P5R_shaped_groundtruth` :201 — `WSC/Props/Shaped/P5ShapedR.lean` | **K = 1600**, SHAPE G1R | probe :318 Falsified; witness **1541** (halts at 1541, budget-errors at 1540), on a context with **zero** failing `validRewardingContext` conjuncts | `g1R_realizable` | **0** (ground-truth corollary: `Deployed`, `OnChain`, `TS3`) |
| **P6** | Claiming Member is self-penalizing: an accepted Member classification *adds* the positive minted amount to the value that must remain at base outputs. | `P6R_shaped_member_adds_to_requirement` :82, `P6R_shaped_member_mint_stays_at_base` :104, `P6R_shaped_noBaseInputs` :68 — `WSC/Props/Shaped/P6ShapedR.lean` | **K = 3300**, SHAPE G6R | probe :198 Falsified; witness **2837**; `exec_rejects_escape_under_member` | `g6R_realizable` | **0** (`P6R_shaped_noBaseInputs` is pure Lean) |

### 2.1 The measurement that makes the re-cut credible

**Every witness K is byte-identical to its pre-re-cut value** — 2603 / 3572 / 3150 /
3572 / 1541 / 2837 / 784 / 1681 / 1257 / 1466 / 3004+3328 — and every budget is
unchanged. That is not bookkeeping; it is *evidence about the validators*: the
transfer, minting and seize programs never dereference `txInfoRedeemers`, so enlarging
the redeemer map costs zero CEK steps. The one exception, `DelegateSeize`, does walk
the map, and its K was independently re-measured (1466, first halt found by search
over 1450–1489). No budget was raised to make a re-cut proof go through.

### 2.2 Scope caveats, one per property

* **P1.** Bounded by K = 4400 and by four shapes. Only **one of the three containment
  dispatch paths** is covered at UPLC (Path A); Paths B/C and input-side aggregation
  (≥ 2 mini-ledger inputs) are blocked by Blaster defect **D6** (§3.3). The exemption
  hypothesis is carried in raw-decode vocabulary; bridging it to ground truth costs
  `TS3`. **P1 is aggregate containment at the base *payment* credential — not
  per-holder ownership**; intra-mini-ledger transfers between holders are enforced by
  per-policy transfer-logic scripts, outside this formalization.
* **P2.** Conjunct (b) is the **sharpest shape-dependence in the library**: it is
  false-in-general on the source model (two machine-checked counterexamples —
  `ptokenPairsContain` is unsound with duplicate token names or unsorted maps) and
  closes at SHAPE S1R only because S1R gives every value exactly one policy and one
  token name. **The re-cut did NOT weaken this dependence** — S1R re-uses S1's value
  and mint terms *by name*. Do not generalize it by inspection. P2 does **not** claim
  the directory node the redeemer points at is authentic.
* **P3.** Covers base spends whose run halts within 600 steps. Its conclusion is "the
  credential is in `txInfoWdrl`"; upgrading that to "the validator actually ran" is
  the ledger axiom `LR_WDRL_RUNS_VALIDATOR`. This is the leaf every top-level theorem
  consumes, and the reason they all carry `sorryAx`.
* **P4.** The four arms are proved at four **pairwise disjoint** shapes, so the
  disjunction is per-shape and there is no single theorem over a symbolic redeemer
  tag. **SHAPE L2** — the free-registration-index rung of arm 1 — was **not** re-cut
  and its theorem (`P4_local_noEscape_shapedIdx`) still ranges over a class proved
  empty; it must not be quoted (audit F19).
* **P4a / M2R.** SHAPE M2R has a vacuity probe and a ledger-level realizability
  witness but **no CEK acceptance witness** — `appliedMintRShapedIdx900.exec` is
  executed nowhere (audit **F17**). Three of the four bars, not four.
* **P5.** The `NonMember` classification is positional in the shape; the theorem is
  about the shape's node index. The ground-truth corollary costs `TS3`.
* **P6.** SHAPE G6R has **no mini-ledger inputs** (`P6R_shaped_noBaseInputs` states
  this as a theorem, so the scope is machine-checked rather than promised).

---

## 3. PROVED vs ASSUMED vs OPEN

### 3.1 Proved

* The **reduction** (§1a) and the two composed discharges (§1c and
  `Composition.containment_on_contained_class`).
* The **six properties** (§2) over their re-cut shapes and budgets, each with a
  negative control, a tightness stanza (`solve-result: 1`), a vacuity probe at its own
  term and shape, and — except M2R — a concrete accepting CEK witness with a
  two-sided K.
* **Realizability of 11 of 12 shapes**, at two levels: class-level coverage in CLAB's
  own vocabulary for **every** leaf assignment (`*_class_coverage`), and point-level
  `Realizable` / `RealizableExact` at a concrete witness (`*_realizable`). All with
  **0 project axioms**.
* **The emptiness of the retired shapes** — so the "before" column of the re-cut is
  proved, not asserted. `t1/t2/t6/t7/g6_class_is_empty` need no `RedeemerCoverage`
  hypothesis; `l1/m1/g1/s1/dt1_class_is_empty_under_coverage` do.
* **The redeemer rule reproduces the real node**: 13/13 goldens satisfy
  `redeemerCoverage`, all 9 accepting satisfy `redeemersExact`, and the predicted
  purpose multiset matches in every case. The converse check — every pre-C2 witness
  *fails* coverage — is also proved (`all_old_witnesses_fail_c3_coverage`).
* **Provenance**: the four `.flat` files are byte-identical to the production
  `cborHex` at the recorded commit (§4.1).
* **The shape bridge** for 16 shapes at `exec` level by kernel-checked `rfl`, plus
  `exec_T1R`/`bridge_T1R` for the one shape actually consumed.
* Every `*NonVacuous` obligation, all five `native_decide` on the real CEK with 0
  project axioms and no `sorryAx`.

### 3.2 Assumed — the 28 project axioms under the strongest composed result

`RealizableLeaves.containment_on_realizable_class_of_p2` depends on 28. They are the
26 that `Composition.containment_on_contained_class` depends on, **plus exactly two**:

* **`WSC.LR_BUDGET_global`** — the ledger↔meter bridge at K = 4400. Its non-vacuity
  side condition is *discharged* (`NonVacuity.globalNonVacuous_at_4400`), not assumed.
* **`WSC.TS3`** — reached through the raw↔ground-truth reconciliation of the directory
  exemption predicate.

**That two-axiom delta is the price of making the bytecode load-bearing, and it is the
most informative number in the audit.** The cheaper result says nothing about the
validators; the dearer one does.

The 26, by home file — `WSC/Honest.lean` (16): `Deployed`, `OnChain`, `LR_CTX`,
`NONNEG`, `LR_BUDGET_base`, `LR_MINT_RUNS_POLICY`, `LR_SPEND_RUNS_VALIDATOR`,
`LR_WDRL_RUNS_VALIDATOR`, `NodeAccepts{Base,Global,Minting,Seize}`,
`nodeSteps{Base,Global,Minting}`, `mlhPolicyId`. `WSC/Composition.lean` (10):
`LedgerStep`, `Genesis`, `lr_utxo_semantics`, `lr_inputs_in_ledger`,
`lr_registration_source`, `LR_BALANCE_SLOT`, `NONNEG_L`, `DIRWF_L`, `ts_genesis`,
`ts_minting_identity_L`.

The library declares **51** axioms; 23 are reached by no top-level theorem. **Zero are
declared under `WSC/Prep/`, `WSC/Shaped/` or `WSC/Props/Shaped/`** — the shaped layer
adds no assumption, and that survived C1, C2 and C4.

### 3.3 Open

1. **SHAPE COVERAGE — the binding constraint.** No argument that the shapes exhaust
   the transactions the claim is about. §2.2's P2 caveat shows this is not pedantry.
2. **`p2` at the composed level.** Needs an unwritten "structure preserved ⟹
   contained" lemma, and a `Shape` that is the union of the re-cut shapes with a P2
   discharge at each — i.e. it is entangled with (1).
3. **`nopre` (`L-mint-needs-reg`) in general.** Discharged in `RealizableLeaves` only
   because SHAPE T1R registers nothing. Any shape admitting a registering transaction
   gets the full obligation back.
4. **`PropExecFaithful`** (audit F8). All 12 re-cut groups hypothesise `.prop`; every
   witness and every measured K runs `.exec`; equality is unproved and **not**
   axiomatized. `bridge_T1R` — the lemma carrying P1 into the composition — has
   `.prop` on its left-hand side, so the composed result inherits it.
5. **Blaster defect D6.** `#prep_uplc` emits kernel-ill-typed `dite'` when a CIP-153
   `Value` builtin result stays symbolic, blocking SHAPES T3/T4 and hence P1's
   dispatch Paths B/C and input-side aggregation. Needs an upstream fix.
6. **D5 — reproducibility, and the highest operational risk here.** The substrate is
   an **unpushed local branch** of PlutusCoreBlaster, and `lake-manifest.json` records
   **no revision at all** for it. Without its CIP-153 builtins
   `programmableLogicGlobal.flat` does not decode at all (verified negative control:
   against PCB `main` the import fails with *"Could not decode program!"*), so every
   P1/P5/P6 result — and the composed C4 result — inherits this. **Until the branch is
   pushed and the pin changed to a full git rev, no claim in this document is
   independently checkable**, and any external quotation must say so.
7. **SHAPE L2 not re-cut** (F19) and **SHAPE M2R has no CEK witness** (F17). The
   latter is the cheapest open item in the repository.
8. **`SeizeWdrlOfScoped`** — `LR5` does not entail `seizeCred ∈ txInfoWdrl`. Newly
   tractable: the same ledger rule, in the other direction, is now stated as audit row
   S / `LR_REDEEMER_COVERAGE`.
9. **`ValueAlgebra` + `LedgerCanon` uninstantiated**, so `LR_BALANCE_SLOT` remains an
   axiom. `valueOf` is not additive over `merge` without canonicity — a
   `native_decide` counterexample is on record. Budget ~330 lines.

---

## 4. WHY THE METHOD IS TRUSTWORTHY — what a skeptic should check

### 4.1 The proofs run against the actual production bytecode

`sha256sum WSC/flats/*.flat` matches `PROVENANCE.md`'s table **and** the `cborHex` of
the named **unapplied** production TextEnvelope JSONs at wsc-poc commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f`, 4/4 on both counts. "Unapplied" is
confirmed — every deployment parameter is still a lambda, supplied Lean-side — so no
theorem can quietly be about a partially applied term.

### 4.2 Vacuity probes are mandatory, and one caught a worthless theorem

A theorem of the form `accept → P` is worthless if nothing can be accepted. Task V3
stated P6 at SHAPE G6 budget 2500, got `✅ Valid`, and only the mandatory probe revealed
the class was accept-UNSAT. Preserved as `Probe/G6Vacuous2500.lean`. P6 was restated at
3300.

The audit re-ran the pairing **mechanically** over the whole built set: 20 prep/run
terms carry accept-hypothesis theorems and **every one has a probe at that same term**;
the five terms with theorems but no probe were each inspected and none is an
accept-hypothesis theorem. For the 12 re-cut groups the probe was checked to name the
**new** prep term *and* the **new** shape builder — a probe at the old term would have
certified nothing.

### 4.3 Ground-truth postconditions (no tautologies)

Every headline's postcondition is an independent structural recursion over the
context's own lists (`Model.outSum` / `inSum`, `P2.sumOutAtBase` / `sumInAtBase`,
`Spec.noEscape`), never the validator's own accumulator. The validator appears only in
the hypothesis. The escape routes are real and are exhibited: `ctxEscape_quantities`
gives `outSum = 3 < inSum = 5`, and the real CEK **rejects** that context with 4400
steps available.

### 4.4 Goldens: differential testing against real ledger-evaluated verdicts

13 vectors, 4 rejecting / 9 accepting, each verified at extraction by re-running the
compiled script at PV11 through the Haskell ledger evaluator, requiring `Right budget`
for accepting and `Left CekError` for rejecting — the rejecting controls double as an
**arity proof**, since an under-applied Plutus script evaluates to a lambda and can
never produce `Left`.

### 4.5 Controls, and the discipline about controls

Every headline carries a negative control **and** a tightness stanza that must come
back `Falsified`. 57 of the 158 verdicts are stanzas that are *expected to fail*; a
`Valid` there would be a red flag, and the build asserts the expectation.

### 4.6 The source reconciliation

158 verdicts = 99 `blaster` tactic invocations + 2 `solve-result: 0` stanzas + 57
`solve-result: 1` stanzas, counted over the 90 built modules with comments stripped.
**No stanza is unaccounted for and none is skipped.** (Note for the next auditor: 5 of
the 99 are written `:= by` with `blaster` on the following line; a naive one-line grep
lands on 96.)

### 4.7 The redeemer-coverage rule was transcribed from the ledger and checked both ways

C3 transcribed `hasExactSetOfRedeemers` from
`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`. The audit read
the Haskell independently and confirms the transcription — **including that CLAB's
version is deliberately *stronger* than the ledger rule** (it cannot express
`isNativeScript`, so it over-approximates). That asymmetry is documented, kept out of
`validScriptContext`, and its one consequence is recorded as audit **F18**: the
positive realizability uses are conservative and unaffected, while the *negative*
uses — the emptiness proofs of the retired shapes — inherit the all-Plutus reading.

### 4.8 The `unused variable` linter as an honesty instrument

Lean reports 5 `unused variable` warnings, all at `Composition.lean:2442-2446` — A2's
`containedLeaves` — and they are the compiler's own confirmation that **those** leaf
discharges do not use their acceptance hypotheses. `RealizableLeaves.lean` emits
**none**, because its `p1` really does use its hypothesis and its `p4`/`nopre` bind
theirs as `_` on purpose. Check this yourself; it is one grep.

### 4.9 What a skeptic should still refuse to take on trust

* That the shapes cover anything (§3.3.1).
* That `.prop` and `.exec` are the same term (§3.3.4).
* That any concrete witness is genuinely on-chain — `OnChain` is opaque.
* That this builds anywhere else (§3.3.6).
* That "`sorry`-free" holds: **99** theorem-position results are closed by `blaster`'s
  `admit`, and every top-level theorem inherits `sorryAx`. The build log's `sorry`
  warning count is **not** a census — 37 modules suppress it; use `#print axioms`.

---

## 5. FINDINGS THIS WORK PRODUCED

### 5.1 About the system

* **A specification correction.** ARCHITECTURE §3-P1's `mintPos` form of the
  containment inequality is **false for burns** — machine-refuted at both the original
  and the re-cut shapes (`mintPos_form_REFUTED`: with `inSum = 5`, `mintOf = −4` the
  unsigned requirement demands `1 ≥ 5`). The **signed** form is the true one and the
  one the composition consumes.
* **Two machine-checked counterexamples to `ptokenPairsContain`** (obligation B1): it
  is unsound with duplicate token names or unsorted token maps. This is why P2b's
  proof is shape-bound in an essential rather than incidental way.
* **An arity bug in the benchmark harness** (upstream wsc-poc): the base case applied
  2 of 3 arguments, so it was measuring a partially applied lambda.
* **`valueOf` is not additive over `merge` without canonicity** — a `native_decide`
  counterexample, which is why `LR_BALANCE_SLOT` is still an axiom.

### 5.2 About the method — the finding this campaign is most defined by

**Every shape in the library was unrealizable, and the campaign found it in its own
work.** A one-entry redeemer map cannot coexist with two script withdrawals under
Conway UTXOW. The consequence was that six proved properties were statements about
empty classes. It was found by the campaign's own audit, published before anyone else
could, sized in the same document (the fix is modelled by the
`transfer-nonmember-covering-node` golden), and then **repaired for 11 of 12 shapes**
with the repair verified in both directions.

That sequence — build, audit, find your own critical defect, publish it, size it, fix
it, re-audit — is the strongest evidence in this repository about the *method*, and it
is worth more than any individual verdict.

### 5.3 About documentation drift

Successive audits caught: prep-cost figures ~47× pessimistic because they were timed
with `lake env lean` (no `--load-dynlib`, so the solver ran interpreted) — a mistake
that had already caused one task to skip work as "unaffordable"; a `sorry`-count
claimed as a census when 37 modules suppress the warning; stale golden cost tables; a
`PROVENANCE.md` note that was simply false; and an earlier draft of this round's own
module header claiming the top claim was "proved over a realizable class" when it is
proved *assuming `p2`* over a class that is merely *not provably empty*.

### 5.4 Still open

See §3.3. The two that matter most: **shape coverage** (nothing has been started) and
**D5 reproducibility** (an unpushed dependency with no recorded revision).

---

## 6. HOW TO REPRODUCE

```bash
# 1. clean-room rebuild of the whole library
#    expect: 429 jobs, 90-105 s wall, 1.65 GB peak, 158 ✅ markers (101 Valid +
#            57 Expected Falsified), 0 errors, 0 ⚠️/❌, 20 expected `sorry`
#            warnings, 90 WSC modules, 5 `unused variable` (all Composition.lean)
cp -a <CLAB> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c
grep -cE '⚠️|❌' build.log ; grep -c 'error:' build.log        # 0 ; 0

# 3. the axiom delta that matters (§3.2)
grep -E 'depends on axioms' build.log                          # 142 lines, 27 sorryAx
#   Composition.containment_on_contained_class             -> 26 project axioms
#   RealizableLeaves.containment_on_realizable_class_of_p2 -> 28 (= 26 + LR_BUDGET_global + TS3)
#   RealizableLeaves.realizable_inhabitant                 -> 0, no sorryAx

# 4. the shaped layer adds no assumption
grep -rn '^axiom ' --include='*.lean' WSC/ | wc -l                                  # 51
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0

# 5. the re-cut, checked in BOTH directions
#   RealizableShapes.all_recut_witnesses_redeemersExact     (new shapes pass)
#   RealizableShapes.all_old_witnesses_fail_c3_coverage     (old shapes fail)
#   Goldens.Audit.every_golden_is_redeemer_covered          (13/13 real vectors)

# 6. PROVENANCE (§4.1) — 4/4 on both counts
sha256sum WSC/flats/*.flat
git -C <wsc-poc worktree> show 7ae0024b…:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | sha256sum
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs the solver interpreted, and is 15–50× slower. That artefact is
the entire content of audit finding F5.
