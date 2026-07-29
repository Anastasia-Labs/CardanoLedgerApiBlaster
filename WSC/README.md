# WSC programmable-token containment — what this formalization establishes

> # ⛔ TASK R1 (2026-07-28) — **THE TWO FAITHFULNESS AXIOMS ARE RETRACTED**
>
> `WSC.Model.globalModel_faithful` and `WSC.SeizeModel.seizeModel_faithful` are
> **FALSE and have been DELETED**, with every declaration that rested on them.
> Refutations are machine-checked and in the default build
> (`WSC/Model/GlobalModelRefuted.lean`, `WSC/Model/SeizeModelRefuted.lean`);
> full disposition in `WSC/AUDIT.md` entry **R1**.
>
> **Read this as a STRICT IMPROVEMENT.** Every property is proved at UPLC against
> the compiled production bytecode; the source models were the fallback route for
> a wall that shaped contexts removed. Measured, clean-room before/after: **445
> jobs** (+1 module), **175 verdicts (110 `✅ Valid` + 65 `✅ Expected Falsified`) —
> identical**, 0 `⚠️`/`❌`, 0 errors, and project axioms under every composed
> result **unchanged** (25 inert / 28 transfer / 28 seize). Neither axiom was ever
> reached by any composed result. Axiom DECLARATIONS under `WSC/`: **47 → 45**;
> the "51" quoted in §3.2 and §5 below was a grep artefact and is corrected there.
>
> **What is genuinely lost, and it is reported as a loss:** the library no longer
> has any UNBOUNDED statement about the seize path. P2 against production is
> `WSC/Props/Shaped/P2ShapedR.lean` — both conjuncts, budget 3800, SHAPE S1R.


> # ⚠️ POST-#112 (task N6, 2026-07-28) — READ `WSC/AUDIT.md`'s BANNER FIRST
>
> This file was written against the PRE-#112 wsc-poc bytecode. wsc-poc PR #112
> (`main` @ **2306678**) changed three of the four validators SEMANTICALLY; the
> minting policy is byte-identical. Tasks N1–N6 re-based everything.
>
> **The current measurements are (task H2, 2026-07-28): 444 jobs, 0 errors,
> `175` solver verdicts (`110 ✅ Valid` + `65 ✅ Expected Falsified`),
> 0 `⚠️`/`❌`, 20 `sorry`, 5 unused-variable, 106 WSC modules, two clean-room
> runs, wall 10:25 / 10:35, peak RSS ≈ 4.35 GB.**
> The delta over the N6 census (440 / 170 / 102) is tasks H1 (SHAPE T8R's
> certified inhabitant — no new solver verdicts) and H2 (SHAPES T3R/T4R:
> +3 modules, +2 `✅ Valid`, +3 `✅ Expected Falsified`). Both composed results survive with **28** project axioms
> each and **1 of 4** leaves discharged by the bytecode on each side — unchanged
> — but `top_claim` now carries one NEW hypothesis, `WdrlPairShaped Shape`.
>
> Everything that changed, with measurements: `WSC/AUDIT.md` (top banner) and
> `WSC/status-fragments/N6-compose-and-reaudit.md`. Numbers in the body below
> that disagree with the ones above are the pre-#112 record.

---


**Audience.** A senior engineer or auditor deciding what to believe. Everything below
is machine-checked in this repository or measured in a clean-room rebuild, with the
theorem name, file/line or measurement cited. Where something is assumed or open, it
says so in those words.

**Companion documents.** `WSC/AUDIT.md` is **authoritative** and this file defers to
it. `WSC/STATUS.md` is the per-property table. `WSC/EXEC-SUMMARY.md` is one page with
no Lean identifiers. `WSC/COVERAGE.md` is the coverage question and its answer.
`WSC/REPRODUCE.md` is the third-party build recipe.

**Verified build state (current, after the H2 dead-file cleanup):** **431 jobs**,
1 m 49 s – 2 m 00 s, **162 solver verdicts (103 `✅ Valid` + 59 `✅ Expected
Falsified`), 0 errors, 0 `⚠️ Undetermined`**, source reconciliation exact and done
**per verdict** rather than by totals, **93 WSC modules**, 20 expected `sorry`
warnings, 5 `unused variable`. Peak RSS 1.50–1.66 GB — **load-dependent, and not an
instrument**: unmodified `7039cdb` also measures 1.64 GB under the same concurrent
load. (At G3 `f4486ca`, two runs: 432 jobs, 1:46–2:10, the same 162 verdicts, 94
modules — H2 deleted six modules, one of which was in the build, and **no verdict
moved**; the decision table is `AUDIT.md` §12. At E5 `7039cdb`, quiet box, three
runs: 431 jobs, 1:39–1:57, 159 verdicts = 102 + 57, 93 modules.)

---

## 1. THE CLAIM, and exactly what is established

**The claim.** *In an honest deployment, programmable tokens cannot exist outside the
mini-ledger — the `programmableLogicBase` payment credential.*

**It is not proved.** What exists is three things, in increasing order of how much the
production code contributes and decreasing order of how general the class is:

1. **A machine-checked reduction.** `WSC.Composition.top_claim` reduces the claim to
   **four leaf obligations** (`p1`, `p2`, `p4`, `nopre`) plus **26 project axioms**,
   over an arbitrary transaction class.
2. **That reduction discharged over an inert accounting class.**
   `containment_on_contained_class`, over `ContainedTx`. **26 axioms, and no UPLC
   result is used at all** — Lean's own five `unused variable` warnings at
   `Composition.lean:2442-2446` are the proof that the acceptance hypotheses do no
   work. The class does everything.
3. **That reduction discharged with NO remaining leaf hypothesis over two
   node-realizable shape classes**, each depending on **28 project axioms**:

   | theorem | class | purpose |
   |---|---|---|
   | `RealizableLeaves.containment_on_realizable_class` | `T1RShapeNS` | transfer |
   | `RealizableLeaves.containment_on_seize_class` | `S1RShape` | seize |

### 1.1 The number that matters is the RATIO, not "N = 0"

Both classes in (3) have a complete `LeafSet` — no assumed leaf. That is a real
improvement over the previous revision, which carried `p2` as an open hypothesis. It
is **not** an improvement in what the code is shown to do, and quoting "N = 0" alone
is an overclaim:

| class | `p1` | `p2` | `p4` | `nopre` |
|---|---|---|---|---|
| `T1RShapeNS` (transfer) | **PRODUCTION BYTECODE** — `WSC.P1R_T1`, `programmableLogicGlobal` @ K = 4400, acceptance hypothesis **consumed** | shape + ledger rule | shape | shape |
| `S1RShape` (seize) | shape + ledger rule | **PRODUCTION BYTECODE** — `WSC.P2b_R_containment`, `programmableSeize` @ K = 3800, acceptance hypothesis **consumed** | shape | shape |

**One of four leaves is the code; three of four are the shape — on each side.**

Two measurements make this concrete rather than rhetorical:

* **Closing the last leaf hypothesis cost zero axioms.** The axiom set of the
  hypothesis-free result is *set-equal* to that of the earlier result that assumed
  `p2`. The obligation was removed by **restricting the class**, not by buying it with
  a new assumption, and not by proving anything new about `programmableSeize`.
* **The shape-discharged leaves provably do not touch the bytecode.**
  `p2_of_noSeizeWdrl` and `p1_of_noGlobalWdrl` carry **no `sorryAx` and no
  `native_decide`** in `#print axioms`. They are `exfalso` arguments from one ledger
  rule and nothing else.

The ledger rule is real: `NoSeizeWdrl hp ctx := credentialInWithdrawals
hp.seizeLogicCred …txInfoWdrl = false` makes `p2`'s hypotheses contradictory through
`validScriptInfo`'s `RewardingScript` clause
(`CardanoLedgerApi/V3/Contexts.lean:1014`, transcribing Conway rewarding
`scriptsNeeded`, `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/UTxO.hs:375-384`): a
rewarding script runs only for a credential the transaction actually withdraws at. A
transaction that does not withdraw at the seize credential cannot have run the seize
validator, so the leaf's hypotheses cannot all hold. That is honest, and it is also
exactly why it says nothing about the seize validator.

### 1.2 What "non-empty" means here, precisely — and what it does not

The classes are **not** empty, and this is certified:

* `realizable_inhabitant_NS` — `P1RShapedWitness.ctxOk` is in `T1RShapeNS`, is
  `validRewardingContext`, and satisfies **both halves** of Conway's
  `hasExactSetOfRedeemers`. **0 project axioms, no `sorryAx`.** The real compiled
  bytecode accepts it in **2,603** CEK steps.
* `realizable_inhabitant_S1R` + `inhabitant_accepted_by_bytecode` — the same for the
  seize side, accepted in **3,004** steps, pinned two-sided.

**What it does not mean.** `WSC.OnChain` is an **opaque axiom**, so no term in this
library can prove any concrete context is genuinely on-chain, and `HonestTx` requires
that. Fees, witness-set agreement and the UTxO set are unmodelled. And on the seize
side one of the three class conjuncts (`SeizeWithinBudget`) is about the opaque
`WSC.nodeStepsSeize` and therefore **cannot be checked at the witness at all** — that
class is certified inhabited for two of its three conjuncts, and the module says so.

"Not provably empty, with the one known obstruction machine-checked absent" is the
exact claim. It is weaker than "provably inhabited on-chain".

### 1.3 The gap, in one paragraph — and it is now measured

Every bytecode result is bounded **twice**: by a CEK step budget and by a fixed `Data`
skeleton (a "shape"). The step bound is stated in every theorem. The shape bound used
to be an *unquantified* worry; it no longer is. `WSC/Coverage.lean` states coverage in
Lean and **refutes it**: at `SizeBound 2 2 2 2 0` — SHAPE T1R's own size — there exist
transactions that are ledger-valid, Conway-redeemer-exact, **accepted by the real
compiled bytecode in exactly the certified inhabitant's 2,603 steps**, and outside all
twelve re-cut shapes. Two of the three differ from the inhabitant by a **list
length**, one by a **constructor tag**; none is repairable by adding a shape
parameter. **0 project axioms, no `sorryAx`.** So: the machine cannot tell the missed
transactions apart from covered ones; only the skeleton can. **That is the gap, and it
is now a theorem rather than an admission.**

---

## 2. THE SIX PROPERTIES

All six are proved at UPLC against the production bytecode, over **re-cut**,
node-realizable shapes. (Pre-re-cut theorems are retained but range over classes
proved empty and **must not be quoted**.)

| # | Property, in words | Budget / shape | Witness K |
|---|---|---|---|
| **P1** | A transfer cannot move more programmable value out of the base credential than it brings in plus what it mints (signed) | 4400 / T1R, T2R, T6R, T7R, **T8R**, **T3R**, **T4R** | 2343 / 2567 / 2777 / 2567 / **2288** / **1936 + 2228** / **2696** (T8R landed at H1, F23 closed; T3R/T4R at H2 (2026-07-28) — the first shapes off containment dispatch PATH A and the first with builtin input accumulation) |
| **P2** | Seizure preserves structure **modulo an ada top-up #112 legalised**, and cannot reduce the base-credential total below inputs plus mint | 3800 / S1R | 2301 (accept), 2412 |
| **P2b, generalized (R3)** | The same containment conjunct over values and a mint field carrying **two token names** — removes the "one token name" caveat | 3800 / **S1R2** | 2739 (accept), 2738 |
| **P3** | Spending at the base credential requires the global **or** the seize validator to run — the keystone | 600 / **B1RG, B1RS, B1W** (no longer unshaped) | 194 |
| **P4** | Any accepted mint runs the minting-logic script; the four redeemer arms are exhaustive and each is constrained | 900 / M1R, M2R; 2500 / L1R, **L2R**, DT1R, DS1R | 784 / **784** / 1681 / **1681** / 1257 / 1466 |
| **P5** | A non-member transfer cannot register a new policy in the directory | 1600 / G1R | 1402 |
| **P6** | A directory member's transfer adds its transfer-logic script to the withdrawal requirement, and its mint stays at base | 3300 / G6R | 2196 |

**⚠️ THIS PARAGRAPH WAS THE LIBRARY'S MOST-QUOTED SENTENCE AND PR #112 MADE IT FALSE.**
It used to read *"P3 is the only unshaped property, and therefore the only one that
needs no coverage argument at all"* (`Coverage.p3_lives_over_a_covering_class`).
The post-#112 base validator reads an index out of a real redeemer and `pdropList`s
into the withdrawal map; the unshaped goal now returns **no verdict** at a 600 s Z3
cap, at 2400 s, with the redeemer skeleton frozen, or at a smaller prep budget (task
N3). **No property in this library is proved unshaped any more**, and the theorem
that sentence named no longer exists.

What replaces it is weaker but still real, and is the reason the §5.4 recommendation
survives in modified form: P3 is now proved over `WSC.WdrlPair`
(`Coverage.p3_lives_over_the_wdrlPair_class`) — the class of contexts whose
withdrawal map has length 2 with both credentials script credentials — and **that
class has a complete, both-directions, non-circular characterisation in ledger
vocabulary** (`Coverage.wdrlPair_char`, axioms `[propext]` only). So P3 is the one
property whose coverage question is a fifteen-line theorem rather than a research
programme; it is no longer the property that needs no such theorem at all.

### 2.1 The measurement that makes the re-cut credible

**Every witness K was byte-identical before and after the RE-CUT** — that was the
C1/C2 measurement and it still holds of the re-cut itself. It is **not** true across
PR #112, which changed three of the four validators: at 2306678 the same witnesses
cost 2343 / 2567 / 2777 / 2567 / 1402 / 2196 / 784 / 784 / 1681 / 1257 / 1466 /
2301+2412. **The six minting K's are unchanged to the step**, which is exactly what
should happen — the minting bytecode is byte-identical across #112 — and is the
control that makes the other six movements credible. That is direct
evidence that none of the four validators dereferences `txInfoRedeemers` except
`DelegateSeize`, whose K was re-measured (1466). Enlarging the redeemer map to satisfy
the ledger cost the machine nothing, which is what you would expect if — and only if —
the map is not read.

### 2.2 Scope caveats, one per property, and they are binding

* **P1** — **Paths A and C are proved; Path B is reached and measured but cannot be
  isolated by any accept/reject theorem**, because on ledger-valid contexts B implies
  C (it is a pure performance fast path). Input-side builtin aggregation is proved
  too. This was closed in two steps on 2026-07-28: Blaster defect **D6**
  (kernel-ill-typed `dite'` on a symbolic CIP-153 `Value` result) was fixed upstream,
  which made the T3/T4 preps possible; then task **H2** supplied the re-cut those
  shapes needed to be node-realizable — SHAPES **T3R** (two token names, so the
  dispatch leaves Path A) and **T4R** (two mini-ledger inputs, so `pvalueFromCred`
  enters its builtin accumulation phase). `WSC/Props/Shaped/P1ShapedBC.lean` carries
  the theorems, the probes, the two-sided K and the executable path evidence; quote
  `AUDIT.md` entry **H2** for the exact status, not "all three paths verified".
* **P2** — the source-model route is **GONE** (task R1): `seizeModel_faithful` is
  false and was deleted, and with it the library's only unbounded seize statement.
  What remains is the shaped UPLC proof. **CORRECTION (task R3).** This entry used
  to say the containment conjunct is "false in general on the source model", that
  it closed only because SHAPE S1R gives every value one policy and one token name,
  and that this was "the sharpest doubt in the library". All three claims were
  wrong. The two `ptokenPairsContain` counterexamples use values `validTxOutValue`
  forbids — negative quantities, a duplicate token name, an unsorted map — and
  `validTxOutValue` is a conjunct of the `validRewardingContext` hypothesis every
  P2 theorem carries; under it `tokensContain` is SOUND, proved in the Lean kernel
  (`WSC.P2.tokensContain_sound`). And the one-token-name restriction was never
  needed: `WSC/Props/Shaped/P2ShapedR2.lean` proves the same conjunct over values
  carrying TWO token names, at the same budget, to the same four-point bar. What
  P2b is still bounded by, and what `containment_on_seize_class` still inherits, is
  SHAPE S1R's remaining skeleton (one non-ada policy per value, fixed list lengths,
  DEFECT D4, budget 3800) — a real bound, but an ordinary one.
* **P3** — proved over a fully symbolic context, but at budget 600.
* **P4** — SHAPE **L2** (the free-registration-index rung of P4-Local) had a class
  **proved empty**, so `P4_local_noEscape_shapedIdx` must not be quoted. It is now
  **superseded**: SHAPE **L2R** (`WSC/Shaped/MintingLocalShapedRIdx.lean`, new at
  `f4486ca`) is the same rung cut over the node-realizable redeemer map, it
  definitionally contains L1R, and **`P4_local_noEscape_RIdx` is the theorem to
  cite**. Two riders travel with it: the headline is *derived* from a `✅ Valid`
  negative control because the direct goal is `⚠️ Undetermined` at a 300 s cap (the
  negative control is strictly **stronger**, so nothing is lost), and **C1 at L2R is
  `⚠️ Undetermined` and is not asserted**. SHAPE **M2R** now meets **4 of 4** bars —
  its accepting CEK witness landed at `f4486ca` with `K = 784` pinned two-sided.
* **P5** — exactly as strong as the `DirWF` / `DIRWF_L` assumption. Proving
  `mkDirectoryNodeMP` at UPLC is what would turn that from assumed into proven.
* **P6** — one shape (G6R), and its predecessor at budget 2500 was the campaign's one
  silently-vacuous theorem (§4.2).

---

## 3. PROVED vs ASSUMED vs OPEN

### 3.1 Proved

* Six safety properties of the four production validators, at UPLC, over named
  node-realizable shapes, each with a mandatory vacuity probe at **its own** prep term
  and **its own** shape reporting `Falsified`, and each with a concrete CEK acceptance
  witness.
* The reduction of the top claim to four leaves plus 26 axioms.
* That reduction completed over two realizable classes, with one leaf from the
  bytecode on each side (§1.1).
* **Coverage is FALSE** for the sixteen re-cut shapes at SHAPE T1R's own size (§1.3).
* Provenance: the four `.flat` files are **byte-identical** to the `cborHex` of the
  named unapplied production scripts at wsc-poc `f918ec6` on `main` (the PR #110
  squash-merge; exported at `7ae0024`, identical tree) — **4/4, re-verified at
  every audit including this one**.
* The Conway redeemer-coverage rule reproduces the real node's output on **13/13**
  goldens, and the re-cut is checked in **both** directions (new witnesses pass, all
  5 pre-re-cut witnesses fail).

### 3.2 Assumed — the 28 project axioms under each strongest composed result

26 are shared with the inert-class result. `WSC/Honest.lean` (16): `Deployed`,
`OnChain`, `LR_CTX`, `NONNEG`, `LR_BUDGET_base`, `LR_MINT_RUNS_POLICY`,
`LR_SPEND_RUNS_VALIDATOR`, `LR_WDRL_RUNS_VALIDATOR`, `NodeAccepts{Base,Global,Minting,Seize}`,
`nodeSteps{Base,Global,Minting}`, `mlhPolicyId`. `WSC/Composition.lean` (10):
`LedgerStep`, `Genesis`, `lr_utxo_semantics`, `lr_inputs_in_ledger`,
`lr_registration_source`, `LR_BALANCE_SLOT`, `NONNEG_L`, `DIRWF_L`, `ts_genesis`,
`ts_minting_identity_L`.

The **+2** differ by side and are the price of making the bytecode load-bearing:

* transfer: `LR_BUDGET_global` (the ledger↔meter bridge at K = 4400, whose non-vacuity
  side condition is **discharged**, not assumed) and `TS3`;
* seize: `LR_BUDGET_seize` (at K = 3800) and `nodeStepsSeize`.

**Read 26/28 as a floor.** The library declares **45** axioms (task R1; it was 47
before the two `*_faithful` retractions — the **51** printed here until R1 was a
grep artefact, five prose lines beginning with the word "axiom" inside docstrings,
now reworded so the recipe below is exact; see `AUDIT.md` R1.4); the ones no top-level theorem reaches are what a fuller
bytecode discharge would add. **The two `*_faithful` axioms are no longer among
them: they are deleted, because they are false.** And **zero** axioms are declared
under `WSC/Prep/`, `WSC/Shaped/` or `WSC/Props/Shaped/` — the shaped layer adds no
assumption, machine-verified.

*Observed at R1 and NOT changed here, because it is not R1's finding to fix:* the
"26 shared" enumeration above lists `LR_CTX`, but `#print axioms
WSC.Composition.containment_on_contained_class` does not contain it — the measured
shared set is **25**, and `LR_CTX` is one of the three that each realizable side
adds (transfer: `LR_BUDGET_global`, `LR_CTX`, `TS3`; seize: `LR_BUDGET_seize`,
`LR_CTX`, `nodeStepsSeize`). The 28s are correct; the 26 should read 25.

### 3.3 Open

1. **Shape coverage — CRITICAL, and now known to be FALSE** (§1.3). The binding
   constraint on the whole deliverable. Enumeration cannot close it: the smallest
   bound admitting a real transfer already contains ≈9.27×10⁹ `Data` skeletons ≈
   **971 CPU-years** for one property at the measured cost.
2. ~~**The T3R/T4R re-cut — MEDIUM.**~~ **DONE at task H2 (2026-07-28)**, and D6
   before it. SHAPES T3R/T4R exist and P1 is proved over both to the four-point bar.
   What remains on this axis is not a re-cut but a fact about the bytecode: dispatch
   PATH B is subsumed by PATH C on ledger-valid contexts, so it can be measured
   (K 1936 vs 2228) but never separated by a theorem.
3. **`PropExecFaithful` (F8) — MEDIUM.** Theorems are on `.prop`; witnesses and every
   measured K are on `.exec`; the equality is unproved and deliberately **not**
   axiomatized. It binds all 12 re-cut groups and **both** composed results.
4. **"`sorry`-free" is false (F4).** 101 theorem-position results are closed by
   `blaster`'s `admit`; every top-level theorem inherits `sorryAx`. The build log's
   `sorry` warning count is **not** a census — 38 modules suppress it, and a
   line-oriented grep of `#print axioms` undercounts `sorryAx` as 17 when the true
   figure is **37**.
5. **Reproducibility (D5) — MEDIUM, partially repaired.** `WSC/substrate/` now carries
   a verified incremental `git bundle` that reconstructs the pinned PlutusCoreBlaster
   revision byte-identically, the revision is recorded in three places, and
   `WSC/REPRODUCE.md` is the recipe. Still open: the branch is **not published**, the
   `require` is an absolute path needing a two-file edit, and lake does not enforce the
   recorded revision for a path dependency.
6. **The redeemer-coverage predicate is not the ledger's rule (F18).** It is the
   **all-Plutus specialisation**: Conway's `hasExactSetOfRedeemers` skips needed
   scripts that are native timelocks, and `TxInfo` carries only script *hashes*, so
   the filter is **not expressible** in the PlutusV3 API at all. Used positively
   (witnesses, inhabitation) this is conservative and safe. Used **negatively** it
   asserts more than the ledger guarantees, and **six emptiness results were
   downgraded accordingly** — they now carry an explicit `RedeemerCoverageAt w` side
   condition in their TYPE, with two visible suppliers. The predicates are named
   `…AllPlutus` throughout so the reading cannot be forgotten.
7. **`ValueAlgebra` / `LedgerCanon`** uninstantiated, so `LR_BALANCE_SLOT` stays an
   axiom — `valueOf` is not additive over `merge` without canonicity
   (`native_decide` counterexample).

---

## 4. WHY THE METHOD IS TRUSTWORTHY — what a skeptic should check

### 4.1 The proofs run against the actual production bytecode

Not a model of it. The `.flat` files are byte-identical to the deployed scripts'
`cborHex` (sha256, 4/4). Decoding is by PlutusCoreBlaster's flat decoder; evaluation
by its CEK machine. The negative control is recorded: without the CIP-153 `Value`
builtins on the pinned substrate branch, `programmableLogicGlobal.flat` **does not
decode** ("Could not decode program!").

### 4.2 Vacuity probes are mandatory, and one caught a worthless theorem

Task V3 stated P6 at SHAPE G6 budget 2500, got `✅ Valid`, and only the probe revealed
the class was accept-**UNSAT** — the theorem was empty. It is preserved as
`WSC/Shaped/Probe/G6Vacuous2500.lean` rather than deleted. Since then every
accept-hypothesis theorem is paired with a probe at its **own** term and **own**
shape, verified by mechanical identifier extraction rather than by reading docstrings:
**20 prep/run terms carry accept-hypothesis theorems and all 20 have a probe.**

### 4.3 Ground-truth postconditions (no tautologies)

Each headline's postcondition is an independent structural recursion over the
transaction's own lists — `Model.outSum`/`inSum`, `P2.sumOutAtBase`, `noEscape` — with
**no validator function appearing in the postcondition**. The validator appears only
in the hypothesis. Excluded cases are exhibited as real, rejected transactions:
`P1RShapedWitness.ctxEscape_quantities` gives `outSum = 3 < inSum = 5` and the real CEK
**rejects** it with 4,400 steps available — a genuine rejection, not budget exhaustion.

### 4.4 Goldens: differential testing against real ledger-evaluated verdicts

13 golden transactions decoded into Lean `ScriptContext`s and checked against CLAB's
predicates. This is what caught the ordering defect in §5.1.

### 4.5 The `unused variable` linter as an honesty instrument

Five warnings, all at `Composition.lean:2442-2446` — the inert-class `LeafSet`, whose
acceptance hypotheses genuinely do nothing. **Zero** in `RealizableLeaves.lean`,
`RealizableLeavesS1R.lean` and `Coverage.lean`, because the bytecode leaves really use
their hypotheses and the shape leaves bind theirs as `_` deliberately. When this
library says "the acceptance hypothesis is used", Lean agrees.

### 4.6 The source reconciliation

Every solver verdict is matched to **the source line it points at**: **59**
`(solve-result: 1)` + **2** `(solve-result: 0)` + **101** `blaster` tactic
invocations = **162**, exact, **zero verdicts unclassified**. At G3 this replaced the
older method of counting stanzas in the source and comparing totals — a totals match
can be produced by two compensating errors, a per-verdict map cannot. **Six** of the
101 are written `:= by` with `blaster` on the next line, and one of those six carries
an argument, so no single grep finds them all; that is precisely why the check now
starts from the log rather than from the source. No stanza is unaccounted for and
none is skipped.

### 4.7 The redeemer-coverage rule was transcribed from the ledger and checked both ways

Conway `hasExactSetOfRedeemers` was read at cardano-ledger `cd8b7fab8` and transcribed
into CLAB. It reproduces the node on 13/13 goldens; the re-cut witnesses all satisfy
it; all 5 retired witnesses provably fail it. **Known limitation (F18), RESOLVED as
far as it can be:** CLAB's predicate omits the `not (isNativeScript …)` filter because
`TxInfo` cannot express it — the filter tests a script BODY and `TxInfo` carries only
hashes — so the predicate is *strictly stronger* than the ledger rule. (The companion
`scriptsProvided` filter is a no-op: `babbageMissingScripts` already forces every
needed hash to be provided.) The predicates are therefore named `…AllPlutus`, the
faithful rule is stated modulo a language oracle, and both directions are theorems:
positive uses are conservative (`redeemerCoverageModNative_of_allPlutus`), negative
uses are not (`coveredByNonNative_strictly_weaker`). Every negative use is audited
individually in `WSC/Props/Shaped/ShapeRealizability.lean` §2.3 — six survive, six
are downgraded to an explicit non-native side condition carried in their type, one is
a measurement whose interpretation only is downgraded. This weakens the library's
self-criticism, never its claims.

### 4.8 What a skeptic should still refuse to take on trust

* That the shapes cover anything — **they provably do not** (§1.3).
* That `.prop` and `.exec` are the same term (F8).
* That any concrete witness is genuinely on-chain — `OnChain` is opaque.
* That "N = 0" means the code does the work (§1.1).
* That "`sorry`-free" holds — 101 results are `admit`-closed; use `#print axioms`,
  parsed across newlines, not the warning count.
* That this builds elsewhere without the two manual steps in `WSC/REPRODUCE.md`.

---

## 5. FINDINGS THIS WORK PRODUCED

### 5.1 Defects found and fixed

* **A ledger-API ordering defect in CLAB, which had made a whole class of theorems
  vacuous.** CLAB compared `ScriptPurpose`s and `Credential`s in the **Plutus
  constructor order**. The ledger does not emit them that way and does not re-sort:
  `txInfoRedeemers` is keyed by `PlutusPurpose AsIx`, whose derived `Ord` is
  `ConwaySpending < ConwayMinting < ConwayCertifying < ConwayRewarding < …`
  (`Conway/Scripts.hs:202-213`, used at `Conway/TxInfo.hs:499,512`), and `txInfoWdrl`
  is keyed by `AccountAddress` with `ScriptHashObj < KeyHashObj`
  (`Credential.hs:96-99`). **Consequence:** every transaction carrying both a spending
  and a minting redeemer — i.e. **every programmable-token mint** — failed
  `validRedeemerMap`, so `validMintingContext` was *unsatisfiable* and every
  `validMintingContext ctx → … → POST` theorem was **vacuously true on exactly the
  class it was meant to constrain, at any budget**. Found by the golden differential
  (§4.4), initially **mis-attributed** to the benchmark harness, then corrected —
  and the two causes were told apart *mechanically* (`firstRedeemerOrderViolation`
  names the adjacent pair that breaks each check) rather than by assertion. Fixed by
  correcting the orders to the ledger's, not by weakening the predicate. Every
  `lt`/`irrefl`/decidability proof in CLAB survived unchanged.
* **An arity bug in the benchmark harness** (upstream wsc-poc): the base case applied
  2 of 3 arguments, so it was measuring a partially applied lambda. An under-applied
  Plutus script evaluates to a lambda and "succeeds", which is exactly the failure mode
  a benchmark cannot see.
* **Context-builder artifacts** in the golden harness — a zero fee, and withdrawal
  ordering inside a single purpose kind — separated from genuine CLAB defects by
  machine-checked attribution, so that neither was used to excuse the other.
* **The missing redeemer-coverage rule.** CLAB had no transcription of Conway
  UTXOW's `hasExactSetOfRedeemers`. Adding it is what revealed that **every shape in
  the library was unrealizable** (§5.2) — the campaign's single most important
  finding.

### 5.2 Two specification corrections the proofs forced

* **The containment inequality's unsigned form is wrong.** `ARCHITECTURE.md` §3-P1
  specified a `mintPos` form; it is **false for burns** and is machine-refuted at both
  the original and the re-cut shapes (`mintPos_form_REFUTED`: with `inSum = 5` and
  `mintOf = −4` the unsigned requirement demands `1 ≥ 5`). The **signed** form is the
  true one and the one the composition consumes.
* **`DirWF` was missing a conjunct.** The directory well-formedness predicate omitted
  its fourth (interval) clause. Task V4 added it and, in the same move, turned the two
  bridges that consume `DirWF` into **proved theorems**
  (`WSC.covering_node_excludes_registration`,
  `WSC.Composition.covering_excludes_ledger_registration`), so the assumption surface
  is the same size but discharging it is now an implication rather than a gap.

### 5.3 About the method — the finding this campaign is most defined by

**Every shape in the library was unrealizable, and the campaign found it in its own
work.** A one-entry redeemer map cannot coexist with two script withdrawals under
Conway UTXOW. The consequence was that six proved properties were statements about
**empty classes**. It was found by the campaign's own audit, published before anyone
else could, sized in the same document, and then **repaired for all 13 shapes** (11
of 12 at C4; the twelfth, SHAPE L2, was re-cut as L2R at `f4486ca`), with the repair
verified in both directions and every witness K measured unchanged.

That sequence — build, audit, find your own critical defect, publish it, size it, fix
it, re-audit — is the strongest evidence in this repository about the *method*, and it
is worth more than any individual verdict. The present revision continues it: the
coverage question, which every previous audit listed as an unquantified worry, is now
**stated in Lean and answered "no"**, against the campaign's own results.

### 5.4 About documentation and process drift

Successive audits caught: prep-cost figures ~47× pessimistic because they were timed
with `lake env lean` (no `--load-dynlib`, so the solver ran interpreted) — a mistake
that had already caused one task to skip work as "unaffordable"; a `sorry`-count
claimed as a census when 38 modules suppress the warning; a published `sorryAx` count
of 27 that was an artifact of grepping line-oriented output that wraps (the true
figure is **37**); a `#print axioms` total of 169 that missed the **five** results
printed in the *other* output form, "does not depend on any axioms", with no brackets
to parse (the true total was **174** at that revision, **172** after the H2 cleanup —
the trap is the parser, not the number); stale golden cost tables; a `PROVENANCE.md` note
that was simply false; and a module header claiming the top claim was "proved over a
realizable class" when it was proved *assuming `p2`*.

**And, new at this revision, a process finding (F20).** Of four units in the final
stage, one delivered **nothing at all** and a second produced correct, verified work
but **left it in a scratch directory, uncommitted**, with its own documentation
pointing at two files that did not exist. The repository's most damning practical
caveat therefore remained fully open even though it had been solved. **None of the
campaign's instruments could see this** — the verdict count, the axiom census and the
marker table all looked perfectly healthy, because they can only measure work that was
committed. The seal unit verified the work, landed it, and wrote the missing files.

**The fix is a procedure, not a better instrument**, because every instrument the
campaign owns measures what EXISTS. It was adopted and executed at the following
stage: resolve each assigned finding to a commit, a path, a declaration name and a
*reading* of that declaration **before** rebuilding anything; reconcile every verdict
delta to a **source line** rather than to a total; and unfold the definitions a claim
depends on instead of accepting the claim's own summary. Applied to the three
findings that F20 left open, all three were found genuinely landed — which is the
outcome the procedure is meant to be able to *distinguish*, not the outcome it
assumes.

---

## 6. HOW TO REPRODUCE

Full recipe including substrate reconstruction: **`WSC/REPRODUCE.md`**.

```bash
# 1. clean-room rebuild of the whole library
#    expect (CURRENT, post-H2): 431 jobs, 1:49-2:00 wall, 162 ✅ markers (103 Valid +
#            59 Expected Falsified), 0 errors, 0 ⚠️/❌, 20 expected `sorry`
#            warnings, 93 WSC modules, 5 `unused variable` (all Composition.lean),
#            RSS 1.50-1.66 GB (load-dependent — NOT an instrument)
#    at HEAD f4486ca it was 432 jobs / 94 modules, same 162 markers (AUDIT.md §12)
cp -a <CLAB> <SCRATCH>/clab && cd <SCRATCH>/clab
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c
grep -cE '⚠️|❌' build.log ; grep -c 'error:' build.log        # 0 ; 0

# 3. the axiom deltas that matter (§3.2) -- PARSE ACROSS NEWLINES, a line
#    grep undercounts sorryAx as 17 when the true figure is 37
#   Composition.containment_on_contained_class        -> 26 project axioms
#   RealizableLeaves.containment_on_realizable_class  -> 28 (= 26 + LR_BUDGET_global + TS3)
#   RealizableLeaves.containment_on_seize_class       -> 28 (= 26 + LR_BUDGET_seize + nodeStepsSeize)
#   RealizableLeaves.realizable_inhabitant{,_NS,_S1R} -> 0, no sorryAx
#   Coverage.not_covers_at_T1R_size                   -> 0, no sorryAx

# 4. the shaped layer adds no assumption
# NOTE (task R1): '^axiom ' USED to match 5 prose lines inside docstrings and so
# reported 51 where the truth was 47. R1 reworded those five lines, so the two
# forms now agree exactly; prefer the anchored one, which cannot drift back.
grep -rnE '^axiom [A-Za-z_][A-Za-z_0-9]* *[:({]' --include='*.lean' WSC/ | wc -l    # 45
grep -rn  '^axiom ' --include='*.lean' WSC/ | wc -l                                 # 45
grep -rn  '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l # 0

# 5. the re-cut, checked in BOTH directions
#   RealizableShapes.all_recut_witnesses_redeemersExact     (new shapes pass)
#   RealizableShapes.all_old_witnesses_fail_c3_coverage     (old shapes fail)
#   Goldens.Audit.every_golden_is_redeemer_covered          (13/13 real vectors)

# 6. PROVENANCE (§3.1) — 4/4 on both counts (full recipe: WSC/REPRODUCE.md §6)
sha256sum WSC/flats/*.flat
git -C <wsc-poc clone> show f918ec6d…:generated/scripts/unapplied/prod/<name>.json \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['cborHex'])" | tr -d '\n' | sha256sum

# 7. SUBSTRATE — see WSC/substrate/README.md §3
git bundle verify WSC/substrate/pcb-cip153-value-builtins.bundle
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs the solver interpreted, and is 15–50× slower. That artefact is
the entire content of audit finding F5.
