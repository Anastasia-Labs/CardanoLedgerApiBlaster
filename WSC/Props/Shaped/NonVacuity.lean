-- ⚠️ PRE-#112 (PARTIAL): part of this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Read WSC/IMPACT-PR112.md for the split before quoting anything here.
/-
WSC/Props/Shaped/NonVacuity.lean — **EVERY OPEN NON-VACUITY OBLIGATION,
DISCHARGED** (task A1; audit finding **F7** and the `SeizeNonVacuous` /
`MintingNonVacuous`-at-2500 gaps).

WHAT THIS MODULE IS FOR.  `WSC/Honest.lean`'s four `LR_BUDGET_*` axioms are each
gated on a non-vacuity hypothesis: *some ledger-normalized context is accepted by
`Runs.XRun K`*.  Before task A1 two of the four were recorded OPEN in that file
(`GlobalNonVacuous` at every global budget; `SeizeNonVacuous` at every affordable
one, where it was MEASURED FALSE) and one budget had no statement at all (minting
at 2500, for P4's three custody arms).  All of them are theorems below.

WHY THEY CAN BE CLOSED NOW, in one sentence: a non-vacuity claim is an `∃`, and
after A1 the predicates speak about `Runs.XRun K` — the imported production
bytecode under a `K`-step meter — which is a COMPUTABLE Lean function, so a
concrete accepting `ScriptContext` closes the goal through the real CEK machine by
`native_decide`.  The obstacle that kept them open was never the mathematics: it
was that the predicates named `appliedX.prop`, an `Optimize.main` output that
`native_decide` cannot touch, while every witness in the library runs `.exec`
(audit **F8**, `prop`-vs-`exec`).  A1's restatement puts the witnesses and the
statements on the same term.

**WHY THIS IS A DOWNSTREAM MODULE and not `Honest.lean`.**  `Honest.lean` cannot
import the witnesses: they live in `WSC/Props/Shaped/*`, which import
`Honest.lean`.  Audit F7 names the precedent — `WSC/Props/Shaped/P6Bridge.lean` —
and this module follows it.

## THE TABLE A REVIEWER SHOULD CHECK

| obligation | budget | witness | measured witness K | instrument | previous status |
|---|---|---|---|---|---|
| `MintingNonVacuous K_mint_custody` | 2500 | `P4LocalShapedWitness.ctx` (SHAPE L1) | 1681 | `native_decide` | NO STATEMENT EXISTED (no affordable 2500 prep) |
| `GlobalNonVacuous K_global_nonmember` | 1600 | `P5ShapedWitness.ctx` (SHAPE G1) | 1541 | `native_decide` | **OPEN** (audit F7) |
| `GlobalNonVacuous K_global_member` | 3300 | `P6ShapedWitness.ctx` (SHAPE G6) | 2837 | `native_decide` | no statement existed |
| `GlobalNonVacuous K_global` | 4400 | `P1ShapedWitness.ctxOk` (SHAPE T1) | 2603 | `native_decide` | no statement existed |
| `SeizeNonVacuous K_seize` | 3800 | `P2ShapedWitness.ctxAccept` (SHAPE S1) | 3004 | `native_decide` | **MEASURED FALSE** at every affordable prep budget |

`BaseNonVacuous K_base` and `MintingNonVacuous K_mint` are discharged in
`WSC/Composition.lean` §7 (`baseNonVacuous`, `mintingNonVacuous`) and are not
repeated here.  With those two, the set is COMPLETE: **no `*NonVacuous`
obligation of `WSC/Honest.lean` is open.**

## THE THREE THINGS THIS DOES NOT DO — read before quoting

1. **A non-vacuity theorem is not a coverage theorem.**  Each says "the accept
   class of `Runs.XRun K` is non-empty", which is exactly what stops the
   corresponding `LR_BUDGET_*` from being an equivalence with a `False` side.  It
   says NOTHING about which transactions the budget covers, and nothing about
   shape coverage (audit **F2**, still open).
2. **Every witness here is a SHAPED context** (except the base/minting ones in
   `Composition.lean`), i.e. a concrete `ScriptContext` built by a shape's `σ`.  So
   these theorems inherit the shape bound of the modules they come from, in the
   weak sense that matters for an `∃`: they exhibit one point of the accept class,
   they do not characterise it.
3. **`sorryAx` status IMPROVES, and that is the only trust-base change.**  All
   five proofs are `native_decide` on the real CEK plus a term-level
   `⟨_, _, _, _⟩`, so they depend on `Lean.ofReduceBool` / `Lean.trustCompiler`
   (the compiler-trust axioms) and **not** on `sorryAx`.  Compare the discharge
   audit F7 pointed at — `ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`, a
   `blaster` verdict on `appliedGlobal1600.prop`, which carries `sorryAx`.  That
   one is RETAINED, deliberately, as independent corroboration on the `prop` term:
   the two instruments are different (SMT on the optimized term vs. the compiled
   CEK on the raw one) and neither subsumes the other.

## PROVENANCE OF EACH WITNESS K, so no number here is unsourced

Every K below is pinned to the STEP by a theorem in the witness's own module
(`Halt` at K, `Error` at K-1), measured by bisection in the named probe:

* 1681 — `P4LocalShapedWitness.K_is_1681` (`WSC/Shaped/Probe/L1K.lean`); equals the
  measured step count of the REAL off-chain `Local` golden
  `mint-local-registered-by-ref` (K-MEASUREMENTS §3).  Companions inside the same
  2500 bound: DT1 at 1257 (`ctxDT_K_is_1257`), DS1 at 1466 (`ctxDS_K_is_1466`).
* 1541 — `P5ShapedWitness.K_is_1541` (`WSC/Shaped/Probe/G1K.lean`); the cheapest
  accepting global GOLDEN is 1554, so SHAPE G1 sits in the real transaction's
  regime.
* 2837 — `P6ShapedWitness.K_is_2837` (`WSC/Shaped/Probe/G6Diag.lean`).  The
  1,296-step gap over G1's 1541 is the containment scan a `Member` claim switches
  on, and 2500 < 2837 is exactly why P6-at-2500 was VACUOUS
  (`WSC/Shaped/Probe/G6Vacuous2500.lean`).
* 2603 — `P1ShapedWitness.K_T1_is_2603`; T2/T7 cost 3572 and T6 3150, all < 4400.
* 3004 / 3328 — `P2ShapedWitness.K_is_3004_and_3328` (`WSC/Shaped/Probe/S1K.lean`).
  The accepting seize GOLDENS cost 2570 and 4647; 3800 covers the first regime and
  NOT the second, which is a stated limit of `K_seize`.
-/
import WSC.Honest
import WSC.Props.Shaped.P1Shaped
import WSC.Props.Shaped.P2Shaped
import WSC.Props.Shaped.P4LocalShaped
import WSC.Props.Shaped.P5Shaped
import WSC.Props.Shaped.P6Shaped

namespace WSC
namespace NonVacuity

-- The witness contexts are large concrete `Data` skeletons; the modules that
-- build them set the same option (`P6Shaped` uses 4000000).  Needed only for the
-- defeq checks that identify a shaped `.exec` term with its `Runs.XRun K` form.
set_option maxRecDepth 4000000

/-! ## MINTING at `K_mint_custody = 2500` — P4's three custody-forwarding arms

The bridge this unblocks did not previously exist at any budget above 900: the
shaped `Local`/`DelegateTransfer`/`DelegateSeize` modules prep at 2500 and an
unshaped `#prep_uplc` there is unaffordable (K-MEASUREMENTS §5.1 — minting at 1700
did not finish in 48.6 min), so under the old `appliedX_K.prop` form there was no
term to state a 2500 non-vacuity claim over.  `Runs.mintingRun 2500` needs no
prep. -/

/-- **`MintingNonVacuous K_mint_custody` — PROVED.**  Witness: SHAPE L1 at
`P4LocalShapedWitness.ctx`, which is `validMintingContext` IN FULL (`ctx_valid`)
and mints a STRICTLY POSITIVE quantity of its own policy (`ctx_mints_positive`) —
so the accept class of the 2500 bound contains a genuine token-CREATION
transaction, not merely a burn.  Measured K = 1681, i.e. 1.49x inside the bound.

The acceptance term is `P4LocalShapedWitness.exec_accepts_at_2500`, which is
`appliedMintLocalShaped2500.exec` at L1's leaf values; that IS
`Runs.mintingRun 2500 ppCS mlh ctx` definitionally, and the equality is the
kernel-checked `ShapeBridge.exec_L1`. -/
theorem mintingNonVacuous_at_2500 : WSC.MintingNonVacuous WSC.K_mint_custody :=
  ⟨WSC.P4LocalShapedWitness.ppCS, WSC.P4LocalShapedWitness.mlh,
   WSC.P4LocalShapedWitness.ctx, WSC.P4LocalShapedWitness.ctx_valid,
   WSC.P4LocalShapedWitness.exec_accepts_at_2500⟩

/-! ## GLOBAL at all three published budgets

This closes audit **F7**, which recorded `GlobalNonVacuous` as open in
`WSC/Honest.lean` although a `blaster` discharge existed at 1600.  A1 closes it at
1600 AND at the two budgets that had no statement at all. -/

/-- **`GlobalNonVacuous K_global_nonmember` (1600) — PROVED.  This is audit F7's
obligation.**  Witness: SHAPE G1 at `P5ShapedWitness.ctx` — P5's own subject
context, `validRewardingContext`-true with ZERO failing conjuncts
(`WSC/Shaped/Probe/G1Witness.lean` evaluates CLAB's per-conjunct report on it and
gets the empty failure list).  Measured K = 1541.

STRICTLY CLEANER THAN THE DISCHARGE F7 POINTED AT, and the difference is the whole
value of A1's restatement.  F7 pointed at
`ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`, which is `blaster` on
`appliedGlobal1600.prop` and therefore carries `sorryAx`, and which could not be
applied inside `Honest.lean` because of an import cycle.  This proof is
`native_decide` on the real CEK — no solver, no `sorryAx` — because the predicate
now names `Runs.globalRun 1600`, the term the witness was always about.

The acceptance term is `P5ShapedWitness.exec_accepts_at_1600_unshaped`, i.e.
`appliedGlobal1600.exec ppCS ctx`, which is `Runs.globalRun 1600 ppCS ctx` by
δ-reduction alone. -/
theorem globalNonVacuous_at_1600 : WSC.GlobalNonVacuous WSC.K_global_nonmember :=
  ⟨WSC.P5ShapedWitness.ppCS, WSC.P5ShapedWitness.ctx, WSC.P5ShapedWitness.ctx_valid,
   WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped⟩

/-- **`GlobalNonVacuous K_global_member` (3300) — PROVED.**  Witness: SHAPE G6 at
`P6ShapedWitness.ctx`, `validRewardingContext` in full, measured K = 2837.

Read the margin: 3300 − 2837 = 463 steps.  It is DELIBERATELY tight-ish and it is
the reason the constant is 3300 and not 2500 — task V3 first stated P6 at 2500,
got `✅ Valid`, and the mandatory vacuity probe then revealed the accept class was
UNSAT, i.e. the theorem was EMPTY (`WSC/Shaped/Probe/G6Vacuous2500.lean`).  A
non-vacuity theorem at the published budget is exactly the artifact that makes
that failure mode impossible to repeat silently. -/
theorem globalNonVacuous_at_3300 : WSC.GlobalNonVacuous WSC.K_global_member :=
  ⟨WSC.P6ShapedWitness.ppCS, WSC.P6ShapedWitness.ctx, WSC.P6ShapedWitness.ctx_valid,
   WSC.P6ShapedWitness.exec_accepts_at_3300⟩

/-- **`GlobalNonVacuous K_global` (4400) — PROVED.**  Witness: SHAPE T1 at
`P1ShapedWitness.ctxOk`, `validRewardingContext`-true (`ctxOk_valid`), measured
K = 2603 (`K_T1_is_2603`: `Halt` at 2603, `Error` at 2602).

Note that this witness is stated on the UNSHAPED bytecode already
(`exec_accepts_unshaped` is literally `cekExecuteProgram
programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 4400`), so the
term identity with `Runs.globalRun 4400` is δ-reduction and nothing else.  4400
also exceeds the two containment-carrying off-chain goldens (3262, 3726) and the
other three P1 shapes (T6 3150, T2/T7 3572). -/
theorem globalNonVacuous_at_4400 : WSC.GlobalNonVacuous WSC.K_global :=
  ⟨WSC.P1ShapedWitness.ppCS, WSC.P1ShapedWitness.ctxOk, WSC.P1ShapedWitness.ctxOk_valid,
   WSC.P1ShapedWitness.exec_accepts_unshaped⟩

/-! ## SEIZE at `K_seize = 3800` — reversing a MEASURED-FALSE entry

`WSC/Honest.lean` previously recorded `SeizeNonVacuous` as false at 600 and 1000
(the E2 spike's probes returned `Valid` for the negation) and unreachable at any
affordable budget, since the cheapest accepting seize run costs 2570 steps and a
symbolic `#prep_uplc` at 2000 never completed in 77 minutes.  Every one of those
measurements stands.  All of them are about `#prep_uplc` COST, and none of them
applies to `Runs.seizeRun 3800`, which is not a prep. -/

/-- **`SeizeNonVacuous K_seize` (3800) — PROVED.**  Witness: SHAPE S1 at
`P2ShapedWitness.ctxAccept` — the "nothing moves" seizure, in which the
continuing pair keeps all 10 seized tokens and the second output sits OUTSIDE the
mini-ledger holding an unrelated policy.  It satisfies `validRewardingContext` IN
FULL including `isBalanced` (`all_four_valid`, first conjunct).  Measured
K = 3004; the residual-output instance (the shape of the real accepting seize
goldens) costs 3328, also inside the bound.

LIMIT, stated: the 2-input accepting seize golden costs 4,647 steps and is
OUTSIDE 3800.  This theorem certifies the bound is non-empty, not that it covers
the golden suite. -/
theorem seizeNonVacuous_at_3800 : WSC.SeizeNonVacuous WSC.K_seize :=
  ⟨WSC.P2ShapedWitness.ppCS, WSC.P2ShapedWitness.ctxAccept,
   WSC.P2ShapedWitness.all_four_valid.1, WSC.P2ShapedWitness.exec_accepts_at_3800⟩

/-! ## AXIOM AUDIT

Expected for all five: `[propext, Classical.choice, Lean.ofReduceBool,
Lean.trustCompiler, Quot.sound]` — the Lean-standard three plus the two
`native_decide` compiler-trust axioms, and **no `sorryAx`, no project axiom**. -/

#print axioms WSC.NonVacuity.mintingNonVacuous_at_2500
#print axioms WSC.NonVacuity.globalNonVacuous_at_1600
#print axioms WSC.NonVacuity.globalNonVacuous_at_3300
#print axioms WSC.NonVacuity.globalNonVacuous_at_4400
#print axioms WSC.NonVacuity.seizeNonVacuous_at_3800

end NonVacuity
end WSC
