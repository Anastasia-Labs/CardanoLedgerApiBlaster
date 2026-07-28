# N6 — restore the composition, re-audit, bring the documents to the post-#112 state

**Substrate.** wsc-poc `main` @ **2306678** (PR #112) · PlutusCoreBlaster
`cip153-value-builtins` @ **3fdd3fb** · Blaster `wsc-d6-dite-branch-retype` @
**4d320dd** · CLAB `wsc-containment-proofs`, this commit, on top of N4's
`d630f59`.

---

## 1. EXISTENCE CHECK — done FIRST, before anything was believed (the F20 lesson)

Every property N3/N4/N5 claim to have restored, checked against the tree and
against clean-room rebuild markers, on the four-point bar.

| property | shape | (a) theorem `✅ Valid` | (b) vacuity probe at OWN term + shape | (c) two-sided CEK witness | (d) realizability |
|---|---|---|---|---|---|
| **P1** | T1R | `P1R_T1` ✅ | `P1R_T1_vacuity_probe` ✅EF | `K_T1R_is_2343` (2343/2342) | `t1R_realizable` + class `redeemerCoverageAllPlutus` |
| **P1** | T2R | `P1R_T2` ✅ | `P1R_T2_vacuity_probe` ✅EF | `K_T2R_is_2567` | `t2R_realizable` |
| **P1** | T6R | `P1R_T6` ✅ | `P1R_T6_vacuity_probe` ✅EF | `K_T6R_is_2777` | `t6R_realizable` |
| **P1** | T7R | `P1R_T7` ✅ | `P1R_T7_vacuity_probe` ✅EF | `K_T7R_is_2567` | `t7R_realizable` |
| **P1** | **T8R** | `P1R_T8` ✅, `P1R_T8_owner_witness_enforced_thm` ✅ | `P1R_T8_vacuity_probe` ✅EF, `D9_T8R_vacuity` ✅EF | ❌ **ABSENT** | ❌ **ABSENT** |
| **P5** | G1R | `P5R_shaped_indexed` ✅ | `P5R_shaped_vacuity_probe` ✅EF | `P5RShapedWitness.K_is_1402` (1402/1401) | `g1R_realizable` |
| **P6** | G6R | `P6R_shaped_member_adds_to_requirement` ✅ | `P6R_shaped_vacuity_probe` ✅EF | `P6RShapedWitness.K_is_2196` (2196/2195) | `g6R_realizable` |
| **P2a/P2b** | S1R | `P2a_R_structure`, `P2b_R_containment`, `P2a_R_ada_only_tops_up` ✅ | `P2_R_vacuity_probe` ✅EF | `P2RWitness.K_is_2301_and_2412` (both two-sided) | `s1r_realizable`, `s1r_residual_realizable`, `all_four_covered` |
| **P3** | B1RG / B1RS | `P3_B1RG_forces_globalCred`, `P3_B1RS_forces_seizeCred` ✅ + mutation controls | `P3_B1R{G,S}_vacuity_probe` (prep) **and** `P3_run_vacuity_probe_B1R{G,S}` (run) ✅EF | `K_B1RG_two_sided`, `K_B1RS_two_sided` (194/193, stable @1940) | `b1RG_realizable`, `b1RS_realizable` + class `baseR_class_covered` |
| **P3** | **B1W** *(new, N6)* | `P3_B1W_prop`, `P3_B1W_run`, `P3_B1W_negative_control` ✅ | `P3_B1W_vacuity_probe` (prep) **and** `P3_B1W_run_vacuity_probe` (run) ✅EF | `K_B1W_two_sided` (194/193, stable @1940) | `b1W_realizable` (via `ctxG_is_B1W`, `rfl`) |
| **P4 / P4a** | M1R M2R L1R L2R DT1R DS1R | untouched — minting bytecode byte-identical | ✅EF each | ✅ each | ✅ each |

**FINDING F23 (new, N6). SHAPE T8R meets 2 of the 4 bar items, not 4.**
Task N4 introduced T8R specifically to exercise the line PR #112 was written to
add (`pvalueFromCred`'s script-owner arm, `ownerWdrlIdxs`), and its headline
theorem `P1R_T8_owner_witness_enforced_thm` is real and `✅ Valid`. But:

* there is **no `K_T8R` theorem anywhere in the tree** — `grep -rn "theorem K_"`
  returns 22 K theorems and none is T8R's — so T8R has no two-sided CEK witness;
* there is **no `t8R_realizable`** in `WSC/Props/Shaped/GlobalRealizability.lean`,
  which carries `g1R`, `g6R`, `t1R`, `t2R`, `t6R`, `t7R` and stops;
* there is **no `exec_accepts_T8R`** — the other five shapes each have one.

N4's report says point (d) is "partial" for T8R and cites "its point-level
inhabitant is established (probe green)". That is not the same thing: the green
probe is `D9_T8R_vacuity`, a **solver** falsification — it says Z3 found a model
in which the shaped prep accepts. It is not a concrete `ScriptContext` that
`native_decide` shows the real CEK accepting, and it is not checked against
`validRewardingContext` or Conway's redeemer rule. N4 did not claim otherwise
about (c) — it simply did not mention (c) for T8R at all, and the K table it
published lists six shapes without T8R among them.

**Consequence, stated plainly:** the ONE theorem in the library that is about
#112's new `ownerWdrlIdxs` check lives over a class that has **not** been shown
to contain a single buildable transaction. It is not known to be vacuous — its
own vacuity probe is `✅ Expected Falsified`, so accepting contexts of the shape
exist inside the solver's model — but "the solver can satisfy it" is a strictly
weaker fact than "here is a node-realizable transaction the bytecode accepts in
K steps", and every other shape in this library has the latter. **T8R is the
only shape in the campaign below the bar.** This is not repaired here; it is
reported, because repairing it means building and certifying a fifth global
witness, which is a unit of work in its own right.

Everything else on the table exists, is `✅`, and reconciles to a source line.

---

## 2. THE COMPOSITION — restored, and the restoration is a NEW RESULT

### 2.1 What was actually broken

`WSC/Composition.lean` failed to compile with `Unknown identifier
WSC.P3_base_requires_global_or_seize_run`. N3 flagged this and said "this is a
real change to the composition's reach, not a rename; do not paper it over with
an alias". N3 was right, and the reach change is worse than a rename in a way
N3's report did not spell out:

**SHAPES B1RG/B1RS are DISJOINT from both classes the library composes over.**
They freeze the whole `TxInfo` — 1 input, 0 outputs, 0 reference inputs, empty
mint. SHAPE T1R has 2 inputs, 2 outputs, 2 reference inputs; SHAPE S1R has 2
inputs, 2 outputs and a mint. `Composition.p3_lifted` runs the base validator at
`WSC.withPurpose ctx r (.SpendingScript …)`, whose `TxInfo` **is the ledger
transaction's**. So a P3 available only at B1R cannot close branch C of
`nonEscape_of_registered` (*exit: a mini-ledger UTxO is spent*) for either
composed class — and branch C fires on both, because both classes contain an
input at `progLogicCred` and neither mints positively into branch B.

Without a fix, **both composed results are dead**, not merely un-reproved.

### 2.2 SHAPE B1W — the measurement N3 did not take

N3 localised the blocker correctly ("the symbolic withdrawal LIST under
`pdropList <symbolic index>`") and measured two points: freezing the redeemer
alone changes nothing; freezing the redeemer *and* the withdrawal map closes
everything in under 2 s. **The intermediate point was never measured.** It is
measured here:

| cut | redeemer | rest of `TxInfo` | script params | verdict | wall |
|---|---|---|---|---|---|
| unshaped (N3) | symbolic | symbolic | symbolic `Credential` | `⚠️ Undetermined` | 602 s, and again at 2404 s |
| redeemer-only (N3) | `Constr 0 [I red]` | symbolic | symbolic | `⚠️ Undetermined` | 903 s |
| **B1W (N6)** | **symbolic `Data`** | **symbolic** | **symbolic `Credential`** | **✅ Valid** | **≈ 5 s for the whole module** |
| B1RG/B1RS (N3) | `Constr t [I red]` | frozen | `ScriptCredential` | ✅ Valid | ≈ 2 s |

SHAPE **B1W** (`WSC/Props/P3_BaseWdrl.lean`) freezes exactly one thing:
`txInfoWdrl` is a two-entry list at two script credentials. The two hashes, both
amounts, the redeemer (a free symbolic `Data` — a wrong index, a wrong
constructor tag, a non-`Constr` redeemer are all inside the class), the
`ScriptInfo`, every other `TxInfo` field and both script parameters stay
symbolic.

**Why that cut:** `WSC.p1ShapedWdrl` (T1R) and `WSC.seizeShapedWdrl` (S1R) are
both literally `[(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]`, so
both classes satisfy the condition by `rfl`
(`RealizableLeaves.t1RShape_wdrlPair`, `RealizableLeavesS1R.s1RShape_wdrlPair`).

**The four-point bar is met at B1W** (table §1), and the inputs function is
literally `WSC.baseInputs`, so `exec_B1W : appliedBaseB1W.exec … = Runs.baseRun
600 …` is `rfl` — task A1's arrangement that keeps `PropExecFaithful` (audit F8)
off the keystone path survives.

### 2.3 The measured boundary of the cut

`WSC/Shaped/Probe/P3WdrlLadder.lean`, run at a 900 s cap with EVERYTHING else
symbolic including both withdrawal credentials' constructor tags:

| withdrawal map length | verdict | vacuity probe |
|---|---|---|
| 1 | ✅ Valid | ✅ Expected Falsified |
| 2 | ✅ Valid | ✅ Expected Falsified |
| **3** | **no verdict at 900 s** (`unsolved goals`) | ✅ Expected Falsified |

The n = 3 rung is kept as prose, not as a `⚠️` in the build: it cost 14 m 30 s
of a 14 m 48 s three-rung module and would put a non-`✅` into an otherwise
all-`✅` census. Its vacuity probe closing in seconds is the evidence that the
failure is Z3 search and not an empty accept class.

Note that the ladder proves the fully-symbolic-`Credential` form at n = 2 as
well, so freezing the two withdrawal credentials' KIND is a convenience, not a
necessity — B1W keeps it only because the seven solver calls of `P3_BaseWdrl`
then cost ≈ 5 s instead of > 10 minutes.

### 2.4 How the narrowing is carried — visible in the type, not hidden

`Composition.WdrlPairShaped Shape := ∀ ctx, Shape ctx → WSC.WdrlPair ctx` is a
NEW EXPLICIT ARGUMENT of `p3_lifted`, `nonEscape_of_registered`, `preservation`,
`top_claim` and `no_programmable_tokens_outside_mini_ledger`. It is deliberately
**not** a `LeafSet` field: it is a property of the shape, not a leaf discharged
by the bytecode, and folding it in would have inflated the leaf count while
deflating the ratio.

`Composition.LeafSet.narrow` (new, `LeafSet` is antitone in `Shape` because every
field takes `Shape ctx` as a hypothesis) lets the two §11 BONUS top claims —
`containment_on_contained_class` over `ContainedTx` and the `InertOffBase` one —
survive by intersecting their classes with `WSC.WdrlPair`. Those two statements
are therefore **strictly narrower than before #112**, and the narrowing is
visible in their `Reachable hp (fun ctx => ContainedTx hp ctx ∧ WSC.WdrlPair ctx)`.

### 2.5 The accounting, re-measured

| | pre-#112 (G3/H2 baseline) | **post-#112 (N6)** |
|---|---|---|
| `containment_on_realizable_class` — leaves by BYTECODE | 1 of 4 (`p1` = `P1R_T1`) | **1 of 4** — unchanged, same theorem |
| `containment_on_seize_class` — leaves by BYTECODE | 1 of 4 (`p2` = `P2b_R_containment`) | **1 of 4** — unchanged, same theorem |
| project axioms, transfer side | 28 | **28** |
| project axioms, seize side | 28 | **28** |
| axiom sets | — | transfer and seize differ in exactly two entries: `LR_BUDGET_global`+`TS3` vs `LR_BUDGET_seize`+`nodeStepsSeize` |
| `sorryAx` under both | yes (blaster `admit`) | yes |
| NEW shape-side obligation | — | **`WdrlPairShaped`**, discharged by `rfl` at both classes |

**The ratio did not move and the axiom count did not move.** What moved is that
the top claim now carries one more hypothesis, and it is a hypothesis about the
transaction's withdrawal map that the two composed classes happen to satisfy for
free.

---

## 3. COVERAGE — the refutation REPRODUCES, and §7 is now a stronger statement

### 3.1 §5's refutation, re-measured

All three missed transactions (`ctxTwoSigners`, `ctxThreeRefIns`,
`ctxAlwaysRange`) are still `validRewardingContext ∧ redeemersExactAllPlutus`,
still ACCEPTED by the post-#112 `programmableLogicGlobal` at budget 4400, still
outside all thirteen `range*` shapes, still inside `SizeBound 2 2 2 2 0`. **The
refutation of `Covers` is unchanged.**

The one number that moved: each costs **2,343** CEK steps (was 2,603), two-sided
(`missed_transactions_cost_exactly_2343_steps`) — and so does the shape's own
certified inhabitant (`K_T1R_is_2343`). The coincidence that makes the point —
*the machine cannot tell a missed transaction from a covered one* — survives PR
#112 exactly. #112 made the global validator cheaper, not more discriminating.

### 3.2 §7 was FALSE and is now a better theorem, not a retirement

`p3_lives_over_a_covering_class` and the sentence it anchored — *"the only
property in the campaign proved over a covering class"* — are false of
production at 2306678, exactly as N3 predicted. They are **replaced**, not
deleted:

* `p3_lives_over_the_wdrlPair_class` — P3 over `WSC.WdrlPair`, in the run form,
  with the redeemer and both parameters symbolic;
* `wdrlPair_char` — and this is the part worth reading — **that class has a
  complete, both-directions, non-circular characterisation in ledger
  vocabulary**:

      WdrlPair ctx  ↔  wdrl.length = 2 ∧ every entry's credential is a script hash

  which is §8's pre-existing `wdrl_range_char` applied to the context's own
  withdrawal map. §8 was written as *"what a coverage proof would cost, one
  component, done"*; it turns out to be exactly the coverage argument for P3's
  new class. **For P3 alone in this campaign, the coverage question is not a
  research programme — it is a fifteen-line theorem that was already in the
  tree.**

That is a genuine improvement in what is known, and it is the direct consequence
of B1W being cut in a single ledger-level dimension rather than as a `Data`
skeleton.

---

## 4. CLEAN-ROOM REBUILD ×2 — and TWO REGRESSIONS THAT ARE NOT PROOF FAILURES

Recipe exactly as `AUDIT.md` §1.1 (delete every `WSC.*` olean/ilean/trace, keep
dependency packages, `/usr/bin/time -v lake build WSC WSC.ShapeBridge`), in
`<SCRATCH>/clab-n6`; the canonical repo was never built in.

| measurement | pre-#112 baseline (H2/G3) | **N6 run 1** | **N6 run 2** |
|---|---|---|---|
| exit status | 0 — 431 jobs | **0 — 440 jobs** | **0 — 440 jobs** |
| wall clock | 1:46 – 2:10 | **10:36.40** ⚠ | **10:0x** (same band) |
| user + sys CPU | 466–515 + 64–70 s | **1205.8 + 127.8 s** | — |
| max RSS | 1.65 GB | **4.34 GB** ⚠ | — |
| WSC modules re-elaborated | 93 | **102** | **102** |
| `error:` lines | 0 | **0** | **0** |
| solver verdicts | 162 = 103 V + 59 F | **170 = 108 V + 62 F** | **170 = 108 V + 62 F** |
| `⚠️ Undetermined` / `❌` | 0 | **0** | **0** |
| `declaration uses 'sorry'` | 20 | **20** | **20** |
| `unused variable` | 5 | **5** | **5** |

### 4.1 The wall/RSS regression is ONE MODULE and it is a #112 consequence

`WSC.Prep.Global1600` alone costs **~9 of the ~10.5 min** wall — measured live at 4.2 GB RSS and 94 % CPU on a single `lean` process. The
next slowest module is `WSC.ShapeBridge` at 80 s. Pre-#112 the same prep was part
of a 1:46 build.

This is the `#prep_uplc` of the post-#112 `programmableLogicGlobal` at CEK budget
1600. The flat got *smaller* (6880 → 5624 hex chars) but the term got harder:
#112 moved the mint merge and the per-pair value delta onto CIP-153 `Value`
builtins whose symbolic results the optimizer has to carry. It is also the module
that used to FAIL outright (N1's defect **D8**, an 8 m 9 s kernel error) until
N5's Blaster `optimizeDITE` fix; so 516 s is the cost of it working at all.

**Peak RSS is not a proof instrument** (audit §1.2 already demoted it), but 1.65 →
4.35 GB is large enough to matter for anyone reproducing this: **the build now
needs ~5 GB of RAM**, and `WSC/REPRODUCE.md` says so.

### 4.2 The verdict delta reconciles exactly: 162 → 170, per module, +8

`AUDIT.md` §1.4's instrument, re-run: take each of the 170 `file:line:col`
verdicts the log emits, read THAT source line out of the built tree, classify it.

| source construct at the verdict's own line | count | verdict |
|---|---|---|
| `#blaster … (solve-result: 1)` | **62** | 62 × `✅ Expected Falsified` |
| `#blaster … (solve-result: 0)` | **3** | 3 × `✅ Valid` |
| `blaster` **tactic** in theorem position | **105** | 105 × `✅ Valid` |
| anything else | **0** | — |

62 + 3 + 105 = **170**, **zero unclassified**, identical in both runs.

**The `solve-result: 0` count is 3, not 2.** The third deliberate vacuity
assertion is new: `WSC/Shaped/Calib/P3Shaped.lean`'s
`B1_accept_class_is_empty` (task N3) — the machine-checked statement that the
PRE-re-cut SHAPE B1's accept class is EMPTY against the post-#112 bytecode. The
other two are unchanged (`Prep/Global.lean` `global_vacuity_probe_600`,
`P4_Minting.lean` `minting600_is_vacuous`).

**And the whole 162 → 170 delta reconciles per module across N1–N6.** Method:
count verdict-bearing stanzas in the import closure of `WSC.lean` at the pre-N1
CLAB commit `e5b08dd` and at this one. (The counter over-reads by a constant 3 on
both sides — the `:= by`-newline trap of §1.4 — so its *totals* are 165 and 173,
but its *delta* is exact and every row below is a source change someone made.)

| module | (V, V0, F) before → after | Δ | who, and why |
|---|---|---|---|
| `Props/P3_Base.lean` | (3,0,2) → (0,0,0) | −3 V, −2 F | **N3** — the UNSHAPED P3 goals no longer close; retired to prose + `P3Unshaped.lean.disabled` |
| `Shaped/Calib/P3Unshaped.lean` | (1,0,1) → (0,0,0) | −1 V, −1 F | **N3** — same; it shipped an UNCAPPED `blaster` on a goal that never returns |
| `Shaped/Calib/P3Shaped.lean` | (2,0,2) → (0,1,0) | −2 V, −2 F, **+1 V0** | **N3** — old B1 calibration replaced by `B1_accept_class_is_empty` |
| `Props/P3_BaseRun.lean` | (3,0,1) → (6,0,2) | +3 V, +1 F | **N3** — one keystone per arm (B1RG/B1RS) + probes at the run terms |
| `Props/Shaped/P3ShapedR.lean` | — → (4,0,6) | **+4 V, +6 F** | **N3** — new module: P3 at B1RG/B1RS, mutation controls, probes |
| `Props/Shaped/P1ShapedR.lean` | (5,0,5) → (7,0,6) | +2 V, +1 F | **N4** — SHAPE T8R: `P1R_T8`, `P1R_T8_owner_witness_enforced_thm`, `P1R_T8_vacuity_probe` |
| `Props/Shaped/P2ShapedR.lean` | (5,0,3) → (6,0,3) | +1 V | **N5** — `P2a_R_ada_only_tops_up`, the proof that #112's ada relaxation is one-directional |
| `Props/Shaped/P2Shaped.lean` | (5,0,3) → **deleted** | −5 V, −3 F | **N6** — REFUTED at 2306678 (§5) |
| `ShapeBridge.lean` | (19,0,6) → (19,0,3) | −3 F | **N6** — the three SHAPE-B1 controls, two of which returned `❌ Unexpected Valid` (§5) |
| `Props/P3_BaseWdrl.lean` | — → (3,0,4) | **+3 V, +4 F** | **N6** — new module: P3 at SHAPE B1W |
| `Shaped/Probe/P3WdrlLadder.lean` | — → (2,0,2) | **+2 V, +2 F** | **N6** — the n = 1 / n = 2 rungs of the boundary measurement |

Column sums: **V +4, V0 +1, F +3 → +8**, i.e. `101 + 4 = 105` tactic-Valids,
`2 + 1 = 3` `solve-result: 0` Valids, `59 + 3 = 62` Expected-Falsifieds:
**103 + 59 = 162 → 108 + 62 = 170.** No row is unexplained.

Module count `93 → 102`: the import closure of `WSC.lean` grows 92 → 101.
+3 new files (`Props/P3_BaseWdrl`, `Shaped/Probe/P3WdrlLadder`,
`Shaped/S1Witnesses`), −1 deleted (`Props/Shaped/P2Shaped`), and **+7 modules that
existed but had never been reached by a build that completed** —
`Prep.Seize` and `Prep.Global1600` (blocked by defects D7 and D6/D8 until N5's PCB
and Blaster fixes), plus `Prep.GlobalImport`, `Shaped.GlobalShapedP1SOwnPrep`,
`Props.Shaped.P6Vocab`, `Shaped.Probe.D9Probe`, `Shaped.Probe.D9Budget` (all N4).

---

## 5. THE FATE OF THE PRE-#112 MODULES — KEEP/DELETE

The brief's framing is right: unlike the empty-shape case, where the old shapes
were kept **because the emptiness proofs are stated over them**, nothing here
depends on the pre-#112 *results*. But "nothing depends on them" turned out to be
false for two files, and both are in the table.

| module | fate | reason |
|---|---|---|
| `Props/Shaped/P2Shaped.lean` | **DELETE** | **REFUTED at 2306678.** `P2a_shaped_structure` `❌ Falsified` (the ada top-up #112 legalised); `P2a_shaped_negative_control` `❌ Falsified` (its contrapositive); `P2ShapedWitness.K_is_3004_and_3328` `native_decide`-FALSE (seize K moved). Superseded by `P2ShapedR` over the node-realizable S1R. Repairing it means redoing N5 at a shape audit **F2** already showed is not node-realizable. |
| its four witness contexts | **KEEP**, moved to `Shaped/S1Witnesses.lean` | `RealizableShapes`'s measurement *"none of the four old S1 witnesses is redeemer-covered"* is the historical justification for the S1 → S1R re-cut and is still true. `validRewardingContext` still holds of all four (`all_four_valid`, re-checked). Its K and `exec_accepts` theorems are NOT carried over — they are false. |
| `ShapeBridge.lean` SHAPE-B1 controls (`control_B1_pubkey_param`, `_collapsed_wdrl`, `_polarity`) | **DELETE** | Two of the three returned **`❌ Unexpected Valid`**. SHAPE B1's accept class is EMPTY at 2306678 (`Z2Calib.B1_accept_class_is_empty` `✅ Valid`, N3): B1's redeemer is a bare `Data.I` and the post-#112 validator `pasConstr`s it. An `iff` between two identically-false propositions is Valid whatever you perturb — the controls cannot discriminate. |
| `ShapeBridge.lean`'s `b1_accepts_when_global_present` | **DELETE** | `native_decide`-FALSE at 2306678, for the same reason. |
| `ShapeBridge.lean`'s `bridge_B1`, `inputs_B1`, `exec_B1` | **KEEP, with a ⛔ VACUITY WARNING in the docstring** | True; `bridge_B1` true *vacuously*. Kept so the emptiness result has something to point at, and marked "do not quote". |
| `ShapeBridge.lean`'s `b1_rejects_when_neither_cred_present` | **KEEP, re-annotated** | Still a rejection — but for a DIFFERENT reason now (malformed redeemer, not absent credential), which is precisely why B1 had to be re-cut. |
| `Shaped/BaseShaped.lean` (the SHAPE B1 builder) | **KEEP** | This IS the empty-shape case: `Z2Calib.B1_accept_class_is_empty` is stated over it. |
| `Props/Shaped/P1Shaped.lean`, `P4Shaped`, `P4LocalShaped`, `P4DelegateShaped`, `P5Shaped`, `P6Shaped` (pre-re-cut shapes) | **KEEP** | Not marked PRE-#112 and not refuted: they are true statements about the post-#112 bytecode over the pre-re-cut (non-node-realizable) shapes. They are superseded in usefulness, not in truth, and `ShapeRealizability` states the emptiness/uncoveredness results over them. |
| the ~30 orphan `Shaped/Probe/*` modules marked PRE-#112 | **KEEP** | They are not imported by `WSC.lean` and are therefore not built, so they cannot make the build red; they are dated measurements of the pre-#112 bytecode, each already carrying its `⚠️ PRE-#112` banner from N1. Deleting them would destroy the record of how the old numbers were obtained without buying a single verdict. **They must never be quoted as statements about production** — the banner says so. |
| `Model/SeizeModel.lean`, `Model/SeizeDiff.lean`, `Props/P2_Seize.lean` | **KEEP, marked ⛔ REFUTED** (N5) | `seizeModel_faithful` is false at 2306678 and `Model/SeizeModelRefuted.lean` proves it by computation. Kept because the refutation is stated over them. |
| `Model/GlobalModel.lean`, `Model/GlobalGoldens.lean`, `Model/Ground.lean` | **KEEP, marked** | `Ground` supplies the ground-truth vocabulary the LIVE P1 statement uses. `GlobalModel` is stale (arity-fixed only) and says so. |

**Recommendation for a future cleanup, not done here:** the orphan probe modules
are the only candidates for a bulk deletion, and the right time is when the
library is published, not now — a reviewer reading `AUDIT.md`'s history will want
to be able to open them.

---

## 6. WHAT I DID NOT DO

* **T8R's missing (c) and (d)** — reported as F23, not repaired.
* **No re-measurement of the goldens or of K on the golden suite** — that is N2's
  and N5's work and it was not re-run; the numbers quoted here are theirs.
* **`WSC/Props/P3Unshaped.lean.disabled` was not re-run** at the B1W cut. It is
  worth someone's time to check whether the withdrawal-length insight also
  unblocks the goals N3 left Undetermined there.
* **Peak RSS** — measured once (run 1) with `/usr/bin/time -v`; the box was
  otherwise quiet, but audit §1.2's warning that RSS measures the machine still
  applies.


---

## 7. SECOND PASS (same task, after the first pass was left uncommitted)

The first pass of N6 completed §§1-6 but was **never committed**, and it had not
reached brief item **6b**. This section is the second pass: it verifies the first
pass's claims, then does 6b. Everything in §§1-6 above was re-checked against a
fresh clean-room build and stands, with the wall/RSS figures updated in place.

### 7.1 D6 — RE-TESTED, NOT TAKEN ON TRUST, and the standing limitation is HALF withdrawn

The brief said to re-test before rewriting. Done, and the result is not the
obvious one.

| module | before | at Blaster `4d320dd` |
|---|---|---|
| `Shaped/Probe/T3PrepFAILS.lean` (rewrite `¬(true=b)`) | kernel error | **exit 0, 0 errors, 2.4 s** |
| `Shaped/Probe/T4PrepFAILS.lean` (De Morgan) | kernel error | **exit 0, 0 errors, 9.4 s** |

Both **relabelled as REGRESSION TESTS** in place (filenames kept — ~20 files cite
them by path — with headers that say the name is historical).

**A prep that stops crashing is not a result**, so the campaign's own bar was
applied: `T3_vacuity_probe`, stated at SHAPE T3's OWN prep term and OWN shape,
is **`✅ Expected Falsified` in ≈ 4.6 s**. The accept class is non-empty; Paths
B/C are genuinely reachable at UPLC.

**And then the honest half.** SHAPE T3 is PRE-RE-CUT and provably unbuildable on
a node — 1 script input + 0 mint policies + 2 script withdrawals means Conway
demands **3** redeemer entries and T3 supplies **1**. A P1 theorem there would
live over an empty class of node-realizable transactions. So:

* *"Paths B/C are unreachable at UPLC at any shape"* — **FALSE, withdrawn** from
  `AUDIT.md`, `STATUS.md`, `README.md`, `COVERAGE.md`, `SHAPE-BRIDGE.md` and both
  probe headers.
* *"Paths B/C are verified"* — **also false.** They need a SHAPE **T3R/T4R**
  re-cut, mechanical and already done thirteen times, and NOT done here.

`WSC/pr/02-…` is converted from an ISSUE to a **PR** (renamed
`02-blaster-PR-d6-dite-motive.md`, references repointed) carrying the 37-line
diff, the soundness argument and the verdict-neutrality control. Its Part 2 now
records that a **Blaster-only minimal reproduction still does not exist** — that
was a work item nobody did, and a PR without a regression test in the upstream
suite is worth less; said plainly rather than dropped.

### 7.2 SHAPE T8R joined `recutFamily` — thirteen → fourteen

`rangeT8R` (42 free leaves, counted mechanically) + `inv_T8R` + the extra
`family_invariants` case. The refutation schema consumes only `family_invariants`
and `¬ ShapeInvariants ctx`, so **all three `not_covers_*` results now hold over a
strictly larger family and are correspondingly stronger** with no new witness
work. Free-leaf total **458 → 500**, re-derived mechanically across all fourteen
range predicates (the arithmetic checks: 458 + 42 = 500).

⚠️ The roster is deliberately **no longer described as "N node-realizable
shapes"**: thirteen carry a certified inhabitant, T8R does not (finding **F23**).
That costs nothing for refutations — a bigger family makes them stronger either
way — and `COVERAGE.md` flags it at the one place a positive claim could be built.

### 7.3 The substrate bundle DID NOT reconstruct the substrate — now it does

Both pins moved at #112 and **Blaster had no offline artifact at all**, so
`WSC/substrate/` was incapable of rebuilding what produced these numbers.

| artifact | status |
|---|---|
| `pcb-cip153-value-builtins.bundle` | pre-existing, → `9f9ca8c` |
| `pcb-scalevalue-3fdd3fb.bundle` | pre-existing (first pass), incremental → `3fdd3fb`, tree `1c9d802…` |
| **`blaster-d6-dite-4d320dd.bundle`** | **NEW** — incremental on public `59db213` → `4d320dd`, tree `9550c96…`, sha256 `19e67631…` |
| **`patches/0003-Optimize-DITE-re-type-branch-binders-D6.patch`** | **NEW** — same commit, `git am`-able |

Re-pinned: `lakefile.lean` (both comment blocks + the "restore a real git pin"
line), `lake-manifest.json` (PCB `9f9ca8c`→`3fdd3fb`; Blaster gained `rev`/
`inputRev`), `REPRODUCE.md` (pin table + new §1b), `substrate/README.md`,
`ARCHITECTURE.md` E11 and §0.1.

**Caveat carried, not buried:** `lake` does **not** verify the `rev` key on a
`"type": "path"` entry, and BOTH dependencies are now paths — so neither pin is
machine-enforced, and the table is documentation. Both bundles were verified with
`git bundle verify` against the **local** repositories only; neither has been
fetched into a fresh clone of its public remote, because that needs network this
machine did not use.

### 7.4 The stale-K sweep nobody had done

The first pass updated §-level prose but the per-property tables still carried
PRE-#112 step counts. Corrected: `README.md`'s property table (all six rows),
`STATUS.md`'s per-property table (P1/P2/P5/P6 rows and the P3 row, which still
said *"PROVED, unshaped … golden 208"*), `AUDIT.md` (five sites),
`COVERAGE.md`, and the two composed-result modules' docstrings, which claimed
their witnesses cost K = 2603 / 3004 when they now cost **2343 / 2301**.
`missed_transactions_cost_exactly_2603_steps` was renamed to `…_2343_steps` in
the source at the first pass but three documents still cited the old name.

### 7.5 Censuses — second pass, all green

Re-run against the run-1 log with a tightened instrument. The first pass's
reconciliation script attached verdicts to a neighbouring stanza's `#blaster`
via a ±3-line window and reported **63/62**; the scan is now BACKWARD-ONLY and
stops at any `theorem`/`def` header:

| census | result |
|---|---|
| markers | **170** = 108 `✅ Valid` + 62 `✅ Expected Falsified`; **0** appearing as errors |
| per-verdict source reconciliation | 3 `solve-result:0` + 62 `solve-result:1` + 105 `blaster` tactic = **170**, **0 unclassified** |
| `#print axioms` results | 203 (196 bracketed + **7** "does not depend on any axioms" — both forms parsed) |
| carrying `sorryAx` | 49 · native_decide trust: 82 · distinct project axioms: **33** |
| composed results | `containment_on_realizable_class` / `_seize_class` / both `no_tokens_outside_…`: **34 total, 28 project**, `sorryAx` yes — **28 unchanged** |
| `axiom` decls under `Prep/`, `Shaped/`, `Props/Shaped/` | **0** |
| vacuity probes declared | 45 (incl. the new `T3_vacuity_probe`) |
| `sorry` warnings / unused-variable / `error:` | 20 / 5 / **0** |

**The refuted axiom is quarantined — checked, not assumed.**
`WSC.SeizeModel.seizeModel_faithful` is FALSE at 2306678 (N5). It appears in the
axiom list of exactly **one** declaration, `WSC.P2.P2a_bytecode`, in
`WSC/Props/P2_Seize.lean`, which carries a `⛔ REFUTED` banner on line 1. It is
**absent** from `containment_on_realizable_class`, `containment_on_seize_class`
and both `no_tokens_outside_mini_ledger_*`.

**Anti-tautology spot-check.** `P1R_T1`'s postcondition is over `Model.outSum` /
`inSum` / `mintSigned`, which unfold to `valueOf` and `payCred`; `P2b_R_containment`'s
is over `WSC.P2.sumOutAtBase`, which unfolds to `valueOf` and `outAtBase`. Neither
mentions any validator-computed accumulator.
