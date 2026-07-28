# WSC shape coverage — the question stated, and answered NO

> # ⚠️ POST-#112 (task N6, 2026-07-28) — READ `WSC/AUDIT.md`'s BANNER FIRST
>
> This file was written against the PRE-#112 wsc-poc bytecode. wsc-poc PR #112
> (`main` @ **2306678**) changed three of the four validators SEMANTICALLY; the
> minting policy is byte-identical. Tasks N1–N6 re-based everything.
>
> **The current measurements are: 440 jobs, 0 errors, `170` solver verdicts
> (`108 ✅ Valid` + `62 ✅ Expected Falsified`), 0 `⚠️`/`❌`, 20 `sorry`,
> 5 unused-variable, 102 WSC modules, two clean-room runs, wall 10:34 / 10:36,
> peak RSS ≈ 4.3 GB.** Both composed results survive with **28** project axioms
> each and **1 of 4** leaves discharged by the bytecode on each side — unchanged
> — but `top_claim` now carries one NEW hypothesis, `WdrlPairShaped Shape`.
>
> Everything that changed, with measurements: `WSC/AUDIT.md` (top banner) and
> `WSC/status-fragments/N6-compose-and-reaudit.md`. Numbers in the body below
> that disagree with the ones above are the pre-#112 record.

---


## 0-N6. WHAT PR #112 CHANGED IN THIS DOCUMENT

**The refutation reproduces.** Re-measured at wsc-poc `main` @ 2306678: the three
missed transactions are still `validRewardingContext ∧ redeemersExactAllPlutus`,
still accepted by the production `programmableLogicGlobal` at budget 4400, still
outside all sixteen `range*` shapes, still inside `SizeBound 2 2 2 2 0`. `Covers`
is still PROVED FALSE at SHAPE T1R's own size. The single number that moved is the
step count: **2,603 → 2,343**, two-sided, for the three missed transactions AND for
the shape's own certified inhabitant. The coincidence that carries the argument —
*the machine cannot tell a missed transaction from a covered one* — survives #112
exactly. **#112 made the global validator cheaper, not more discriminating.**

**One sentence in this document is now FALSE and must not be quoted:** §7's
*"P3 lives over a covering class … the only property in the campaign of which this
is true"*. The post-#112 base validator reads an index out of its redeemer and
`pdropList`s into the withdrawal map, and the unshaped goal returns no verdict at a
600 s cap, a 2400 s cap, a redeemer-only shape or a smaller prep budget (task N3).

**What replaced it is better than a retirement.** P3 now holds over `WSC.WdrlPair`
— *the withdrawal map is two entries at two script credentials* — with the
redeemer, both script parameters and every other `TxInfo` field still fully
symbolic (SHAPE **B1W**, `WSC/Props/P3_BaseWdrl.lean`). And that class is the ONLY
one in the campaign that has a complete, both-directions, non-circular
characterisation in ledger vocabulary:

    WdrlPair ctx  ↔  wdrl.length = 2 ∧ every entry's credential is a script hash

which is this document's own §4 cost-anchor lemma (`Coverage.wdrl_range_char`,
~15 lines, no solver) applied to the context's own map — see
`Coverage.wdrlPair_char`. §4-§5's argument that a full coverage proof is
impractical is unchanged for the other twelve shapes; **for P3 it is already
done.**

**Measured boundary of the new class** (`WSC/Shaped/Probe/P3WdrlLadder.lean`, 900 s
cap, everything else including both credentials' constructor tags symbolic):
length 1 `✅ Valid`, length 2 `✅ Valid`, length 3 **no verdict**, with the length-3
vacuity probe `✅ Expected Falsified` in seconds — so the failure is Z3 search, not
an empty accept class.

---


**Task E4.** The single largest remaining assurance gap in this campaign is that
every UPLC result is "over this layout": `WSC/AUDIT.md` §8 **F2** calls the
missing coverage argument the binding constraint, §9.3 says *"do not believe any
UPLC result is universally quantified over transactions"*, and
`WSC/SHAPE-BRIDGE.md` §10 records three possible routes and offers none.

This document and `WSC/Coverage.lean` change the status of that gap from
**unknown** to **measured**. Nothing here makes any earlier claim stronger. One
earlier hope is closed off, with a proof.

---

## 0. THE ONE-PARAGRAPH ANSWER

Coverage is now **stated in Lean** (`Coverage.Covers`), and it is **false** for
the sixteen re-cut shapes of tasks C1/C2, the G stage, the N6 stage and task H2 — not at some larger
transaction size, but at **SHAPE T1R's own size**. Three witnesses prove it, each
of which is (i) `validRewardingContext` **and** `redeemersExactAllPlutus`, i.e. realizable
at exactly the bar `WSC.t1R_realizable` meets, (ii) **accepted by the real
compiled `programmableLogicGlobal` bytecode**, and (iii) halting in **exactly
2,603 CEK steps — byte-identical to the shape's own certified inhabitant**. They
are: a transfer with two required signers, a transfer reading three reference
inputs, and a transfer with an unbounded validity interval (the default every
wallet emits). None is exotic. (That last characterisation — "what every wallet
emits" — is a statement about the world, not a measurement in this repository;
what IS machine-checked is that an unbounded validity interval is
`validRewardingContext` and outside all sixteen shapes.) The arithmetic explains why no repair by enumeration is available: at
that bound there are at least **3.05 × 10¹⁴** distinct `Data` skeletons against a
family of **14**, and even the smallest bound that admits a single real transfer
has **9.27 × 10⁹** — ≈ 971 single-core CPU-years at the campaign's own measured
prep+solve rate, for one property. The recommendation is therefore **not** a
coverage programme: it is to prove over fully symbolic contexts. **Caveat added
at N6, and it is a real weakening:** this recommendation used to add "the route
P3 already demonstrates works and which needs no coverage argument at all". That
is **false at 2306678** — PR #112 gave the base validator a real redeemer, and P3
no longer closes unshaped at any cap task N3 tried (600 s, 2400 s, and with the
redeemer skeleton frozen). No property in the library is now proved unshaped, so
the unshaped route is currently a HOPE, not a demonstrated technique. Blaster
defect D6, which this sentence also used to blame, **is fixed** (N5, `4d320dd`).
The one positive datum is SHAPE **B1W**: cutting a single LEDGER-level dimension
(the withdrawal map's length) closes P3 in ≈5 s with everything else symbolic —
see §7.

**What this is NOT.** It is not "the shapes are wrong", not "a property fails",
and not "coverage is impossible in principle". The validator *accepts* all three
missed transactions; the library simply says nothing about them. A coverage gap
is an absence of assurance, not the presence of a bug — and `¬ Covers` is a
statement about *this family at this bound*, nothing more (§4.4).

---

## 1. THE QUESTION, STATED

`WSC/Coverage.lean` §1, verbatim:

```lean
/-- A class of contexts. Intended reading: the RANGE of one shape builder. -/
abbrev ShapeClass := ScriptContext → Prop

def SizeBound (mIn mRef mOut mWdrl mMint : Nat) (ctx : ScriptContext) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs.length          ≤ mIn   ∧
  ctx.scriptContextTxInfo.txInfoReferenceInputs.length ≤ mRef  ∧
  ctx.scriptContextTxInfo.txInfoOutputs.length         ≤ mOut  ∧
  ctx.scriptContextTxInfo.txInfoWdrl.length            ≤ mWdrl ∧
  ctx.scriptContextTxInfo.txInfoMint.length            ≤ mMint

def Covers (fam : List ShapeClass) (Valid Bound : ScriptContext → Prop) : Prop :=
  ∀ ctx, Valid ctx → Bound ctx → ∃ S ∈ fam, S ctx
```

and each family member is literally the range of a shape builder, e.g.

```lean
def rangeT1R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (plc owner : ByteString) (inAda qIn : Integer) … (fee : Integer),
    p1RShapedCtx cs tn plc owner inAda qIn … fee = ctx
```

**Three choices in that statement a reviewer should check, because they are where
an overclaim would hide.**

1. **`SizeBound` constrains only the five list dimensions a transaction is
   normally measured in.** It says nothing about signatory count, certificates,
   datum witnesses, validity-interval form, staking references, datum tags or
   reference scripts. That is deliberate and it is the crux: a reviewer told
   *"≤2 inputs, ≤2 outputs, ≤1 mint policy"* has not been told anything about
   those other dimensions, so a coverage claim at that bound must handle them.
   §4 is the proof that this is exactly where the family fails.
2. **The family is the RANGE of each builder, with all its free leaves
   existentially bound.** This is the largest class each shape could possibly
   justify — larger than `RealizableLeaves.T1RShape`, which additionally pins
   three leaves to the deployment's own credentials. Using the larger class is
   the conservative choice for a *negative* result.
3. **`Covers` says nothing about the CEK step budget.** That is the campaign's
   *other* bound and it is orthogonal; nothing in this module addresses it and
   nothing here should be read as addressing it.

**Control against a transcription error.** A range predicate that accidentally
denoted the empty set would make `Covers` false for a reason having nothing to do
with coverage. `Coverage.ctxOk_in_family` exhibits the campaign's own certified
inhabitant `P1RShapedWitness.ctxOk` **inside** `rangeT1R`, hence inside the
family — `#print axioms` = `[propext]`.

---

## 2. WHAT A SHAPE ACTUALLY FIXES

A shape freezes two kinds of thing, and the distinction decides everything:

| kind | examples | can a shape parameterise over it? |
|---|---|---|
| **leaf scalars** | every `ByteString`, every `Integer` (hashes, quantities, ada amounts, fee, redeemer indices) | **yes** — they are the shape's free leaves, and they are symbolic |
| **list lengths and constructor tags** — the `Data` skeleton | how many inputs / reference inputs / outputs / withdrawals / redeemer entries / signatories / certificates / datum witnesses / mint policies / token names per policy; `Credential` tag; staking-reference tag; datum tag; `Option` presence; validity-interval bound tags | **no.** Freezing them is precisely what makes `#prep_uplc` tractable. Escaping one needs a NEW SHAPE — a new prep, new theorems, a new vacuity probe |

The sixteen re-cut shapes and their free-leaf counts (the builders' own arities,
counted mechanically from their `def` signatures):

**T8R joined the family at task N6 (2026-07-28).** It is the shape that exercises
PR #112's new script-owner arm of `pvalueFromCred` — three script withdrawals, no
signatories, `ownerWdrlIdxs = [2]`. ~~⚠️ **It is the one member with no certified
inhabitant** (finding **F23**): no two-sided K, no `t8R_realizable`. Its class is
known non-empty only from a solver model. That is harmless for the refutations in
§4 — a bigger family makes them stronger either way — but it means the roster
below must NOT be described as "fourteen node-realizable shapes"; thirteen are,
and one is pending.~~ **CORRECTED at task H1 (2026-07-28) — F23 is CLOSED.** T8R
now carries a certified inhabitant like every other member: `WSC.t8R_realizable`
(`WSC/Props/Shaped/GlobalRealizability.lean:939`), a two-sided `K_T8R_is_2288`
(`WSC/Props/Shaped/P1ShapedR.lean:1039`), and class-level coverage
(`t8R_class_covered` / `t8R_class_coverage`). **All sixteen shapes below are
node-realizable**, so the roster may be described that way again.

**T3R AND T4R JOINED THE FAMILY AT TASK H2 (2026-07-28).** They are the re-cuts
of the pre-re-cut SHAPES T3 and T4, which audit **F2** showed unbuildable on a
node (T3: 1 script input + 2 script withdrawals ⟹ 3 redeemer entries demanded,
1 supplied; T4: 2 script inputs + 2 script withdrawals ⟹ 4 demanded, 1
supplied). They are the only members that leave the containment dispatch's PATH
A (T3R — two token names per policy, so `checkWholesaleThenBuiltin` runs) and
that drive `pvalueFromCred` into its PHASE 3 builtin accumulation (T4R — two
mini-ledger inputs). Both carry a CERTIFIED inhabitant from the day they landed
— `WSC.t3R_realizable` / `WSC.t3R_realizable_pathC` / `WSC.t4R_realizable`
(`WSC/Props/Shaped/P1ShapedBC.lean`), two-sided `K_T3R_B_is_1936` /
`K_T3R_C_is_2228` / `K_T4R_is_2696`, and class-level `t3R_class_covered` /
`t4R_class_covered`. T4R is also the first member with **three inputs**, so it
is the first for which the `SizeBound` `mIn` dimension bites.

| shape | builder | free leaves | in | ref | out | wdrl | mint |
|---|---|---|---|---|---|---|---|
| G1R | `globalRShapedCtx` | 31 | 1 | 2 | 1 | 1 | 1 |
| G6R | `memberRShapedCtx` | 24 | 1 | 1 | 2 | 1 | 1 |
| T1R | `p1RShapedCtx` | 39 | 2 | 2 | 2 | 2 | 0 |
| T2R | `p1RShapedMintCtx` | 41 | 2 | 2 | 2 | 2 | 1 |
| T6R | `p1ROutCtx` | 41 | 2 | 2 | 3 | 2 | 0 |
| T7R | `p1ROutMintCtx` | 43 | 2 | 2 | 3 | 2 | 1 |
| M1R | `mintRCtx` | 18 | 1 | 0 | 1 | 1 | 1 |
| M2R | `mintRCtxIdx` | 19 | 1 | 0 | 1 | 1 | 1 |
| L1R | `localRCtx` | 36 | 1 | 2 | 2 | 1 | 1 |
| L2R | `localRCtxIdx` | 37 | 1 | 2 | 2 | 1 | 1 |
| DT1R | `dtRCtx` | 39 | 1 | 2 | 2 | 2 | 1 |
| DS1R | `dsRCtx` | 39 | 1 | 2 | 2 | 2 | 1 |
| **T8R** | `p1SOwnCtx` | **42** | 2 | 2 | 2 | **3** | 0 |
| **T3R** | `p1BCShapedCtx` | **44** | 2 | 2 | 2 | 2 | 0 |
| **T4R** | `p1AggRCtx` | **42** | **3** | 2 | 2 | 2 | 0 |
| S1R | `seizeRCtx` | 51 | 2 | 2 | 2 | 2 | 1 |
| **total** | | **586** | | | | | |

**586 free leaves is the whole symbolic surface of the campaign.** Everything
else about every context the library reasons about is a constant.

> **TWELVE → THIRTEEN, at the G stage (2026-07-25).** SHAPE **L2R**
> (`localRCtxIdx`, 37 leaves = L1R's 36 plus the registration index) joined the
> family when audit **F19** closed. `Covers` is an existential over the family, so
> a LARGER family is easier to satisfy and harder to refute — every negative result
> in §4 is therefore now stated over a strictly larger family and says strictly
> more than it did at E4. The total moved 421 → 458, 458 → 500 at N6 when T8R
> joined, and 500 → 586 at H2 when T3R (44) and T4R (42) joined.

### 2.1 Five things ALL SIXTEEN freeze — proved, at every leaf assignment

`Coverage.ShapeInvariants` + `Coverage.family_invariants`
(`#print axioms` = `[propext, Quot.sound]` — no solver, no `native_decide`, no
project axiom):

| field | what the sixteen shapes allow | what the ledger allows |
|---|---|---|
| `txInfoSignatories` | 0 or 1 (`[]` or `[owner]`) | any sorted list of required signers |
| `txInfoReferenceInputs` | 0, 1 or 2 | any list |
| `txInfoValidRange` | a **finite** lower bound (`Shape.range lo hi` only) | `NegInf` / `Finite` / `PosInf`, either closure |
| `txInfoTxCerts` | `[]` | any certificate list |
| `txInfoData` | `[]` | any sorted datum witness map |

Two of the five (`txInfoTxCerts`, `txInfoData`) are dimensions **no shape in the
library has ever populated**: all **32** shaped `ScriptContext` builders under
`WSC/Shaped/` (20 files) assign `txInfoTxCerts := []` and `txInfoData := []`,
32/32, verified by grep at this revision. (31/31 over 19 files at E4; the +1 is
G1's `WSC/Shaped/MintingLocalShapedRIdx.lean`, SHAPE L2R.)

---

## 3. THE ENUMERATION ARITHMETIC

If coverage were to be had by enumeration — route 1 of `SHAPE-BRIDGE.md` §10 —
the family would need one shape per skeleton. How many are there?

`Coverage.skeletonLowerBound` computes a deliberate **LOWER** bound: every factor
counts a strict subset of the real choices, and four dimensions (certificates,
votes, proposals, datum witnesses) are counted as **one** option each, i.e. as if
they could only be empty. Per resolved UTxO (input, reference input or output):

| factor | count | why |
|---|---|---|
| payment credential | 2 | `PubKeyCredential` / `ScriptCredential` |
| staking reference | 4 | `none`, `StakingHash PubKey`, `StakingHash Script`, `StakingPtr` |
| datum | 3 | `NoOutputDatum` / `OutputDatumHash` / `OutputDatum` |
| reference script | 2 | present or absent |
| value profile | 2 | ada-only, or ada + one policy with one token name — i.e. exactly `Shape.adaOnly` and `Shape.adaPlusOne`, and **nothing else** |
| **per UTxO** | **96** | |

times `∑ 96^k` over the admissible list lengths, times 2 mint profiles, 9
validity-interval forms (3 lower × 3 upper bound tags), and the signatory-list
profiles. Machine-checked by `native_decide` in `Coverage.lean` §9:

| bound | in | ref | out | wdrl | **skeletons (lower bound)** | theorem |
|---|---|---|---|---|---|---|
| SHAPE M1R's (the smallest in the library) | 1 | 0 | 1 | ≤1 | **995,328** | `skeletons_at_M1R_size` |
| smallest that admits ONE real transfer | 1 | 2 | 1 | ≤1 | **9,269,489,664** | `skeletons_at_minimal_transfer_size` |
| SHAPE T1R's own | ≤2 | ≤2 | ≤2 | ≤2 | **305,258,198,870,016** | `skeletons_at_T1R_size` |

Against a family of **14**.

**Why the middle row is the decision-relevant one.** The global/transfer
validator cannot run at all without its protocol-params reference input, and the
transfer redeemer names a directory node at a second reference index
(`p1ShapedParamsIn` at `⟨"",2⟩`, `p1ShapedNode` at `⟨"",3⟩`). So no real
WSC transfer has fewer than 2 reference inputs, and the 995,328-skeleton row —
the only one within a plausible compute budget — describes transactions the
validator under study cannot participate in.

### 3.1 The cost, at the campaign's own measured rates

Measured, not estimated: a shaped `#prep_uplc` costs **1.1–1.5 s** and is
budget-independent (`AUDIT.md` §1.5, twelve new preps in stage 9); a shaped
solve costs **≈1–3 s** (`P1ShapedR` 3.1 s for 10 verdicts; `P2Shaped` 25 s for
8). Take **3.3 s per shape per property** — prep plus one solve, generously
ignoring the vacuity probe, the controls, and the fact that a bigger skeleton
solves more slowly.

| bound | shapes | single-core CPU time, ONE property |
|---|---|---|
| M1R's | 9.95 × 10⁵ | **38 CPU-days** |
| smallest real transfer | 9.27 × 10⁹ | **971 CPU-years** |
| T1R's | 3.05 × 10¹⁴ | **3.2 × 10⁷ CPU-years** |

Multiply by 12 property groups, and again by the fact that each shape needs its
own vacuity probe or its theorem may be empty (`AUDIT.md` §4: SHAPE G6 at 2500
was silently accept-UNSAT and only the probe caught it).

**Conclusion: enumeration is not the route.** Not "expensive" — arithmetically
out of reach at every bound at which the question is meaningful.

---

## 4. THE RESULT

### 4.1 The theorems

| theorem | statement | axioms |
|---|---|---|
| `not_covers_at_T1R_size` | `¬ Covers recutFamily ValidRewarding (SizeBound 2 2 2 2 0)` | `propext, ofReduceBool, trustCompiler, Quot.sound` — **no `sorryAx`, no project axiom** |
| `not_covers_at_T1R_size'` | the same, from an independent witness | same |
| `not_covers_with_three_reference_inputs` | `¬ Covers recutFamily ValidRewarding (SizeBound 2 3 2 2 0)` | same |
| `family_invariants` | all sixteen shapes satisfy all five invariants at every leaf assignment | `propext, Quot.sound` |
| `ctxOk_in_family` | the transcription control | `propext` |

The bound in the first two is **SHAPE T1R's own size**: ≤2 inputs, ≤2 reference
inputs, ≤2 outputs, ≤2 withdrawals, no mint. Not a bigger transaction, not a
different validator, not a harder budget.

### 4.2 The three missed transactions

Each is `P1RShapedWitness.ctxOk` — the campaign's own certified SHAPE-T1R
inhabitant — with **exactly one** `Data`-skeleton feature changed and every leaf
scalar untouched.

| witness | change | axis | plain English |
|---|---|---|---|
| `ctxTwoSigners` | `txInfoSignatories := [OWNER, SIGNER2]` | list length | a transfer with two required signers |
| `ctxThreeRefIns` | a third reference input at `⟨"",4⟩` | list length | a transfer reading three reference inputs |
| `ctxAlwaysRange` | `txInfoValidRange := always` | constructor tag | a transfer with no time constraint |

All three are of the *unrepairable* kind: none can be reached by adding a
parameter to an existing shape, because none is a leaf scalar.

### 4.3 Why the counterexamples bite — three measurements

1. **Realizable at exactly the campaign's own bar.** `RealizableRewarding`
   = `validRewardingContext ∧ redeemersExactAllPlutus` — the two conjuncts
   `WSC.t1R_realizable` quotes for `ctxOk`. `native_decide`, no solver.
2. **Accepted by the production bytecode.** `isSuccessful (Runs.globalRun 4400
   ppCS ·)` for all three — the same term `WSC.LR_BUDGET_global` names and the
   same budget `WSC.P1R_T1` is proved at. These are not contexts the validator
   rejects; they are contexts it accepts and about which the library says
   nothing.
3. **Indistinguishable from the covered transaction by the machine.**
   `missed_transactions_cost_exactly_2343_steps`: each halts at 2,343 CEK steps
   and budget-errors at 2,602 — the same two-sided bracket
   `P1RShapedWitness.K_T1R_is_2603` pins for the shape's own inhabitant. Same
   validator, same budget, same step count, same verdict. **The only thing that
   puts them outside every theorem in this library is the `Data` skeleton.**

That third measurement is the honest quantification of what a shape bound costs.

### 4.4 CALIBRATION — the difference between "not proved" and "false"

This section exists because getting this distinction wrong would be the worst
outcome of the task.

* **PROVED FALSE:** *"the sixteen re-cut shapes cover the ledger-valid rewarding
  contexts at `SizeBound 2 2 2 2 0`"*. There is a Lean term for its negation, it
  carries no `sorryAx` and no project axiom, and three independent witnesses
  discharge it.
* **NOT PROVED, either way:** *"coverage is unachievable"*. A larger family could
  cover a smaller bound; §3 argues from arithmetic that it is unaffordable, and
  arithmetic is not a proof of impossibility. **No Lean artifact asserts it and
  this document does not claim it.**
* **NOT CLAIMED:** that any *property* fails on the missed transactions. The
  validator accepts all three. Whether P1's containment postcondition holds on
  them is simply **not evaluated anywhere** — that is what the gap *is*.
* **INHERITED CAVEAT:** "realizable" here means what it means everywhere else in
  this campaign — `validScriptContext` plus Conway's exact-redeemer rule.
  `WSC/Realizability.lean` is explicit that this is **NECESSARY, NOT SUFFICIENT**:
  fees against real protocol parameters, witness-set agreement and the UTxO set
  are unmodelled. The three witnesses are exactly as realizable as
  `P1RShapedWitness.ctxOk` — no more, and the comparison is the only one claimed.

---

## 5. THE ONE PROPERTY THAT NEEDS NO COVERAGE ARGUMENT — P3

**P3, the keystone, is proved over a fully symbolic `ScriptContext`.** Its only
hypothesis is `validSpendingContext ctx`: no shape, no `Data` skeleton, no list
length. The class it ranges over is `⊤`, and `Coverage.unshaped_covers` proves
the one-element family `[unshapedClass]` covers **every** validity class at
**every** bound. `Coverage.p3_lives_over_a_covering_class` exhibits the pairing.

This deserves prominence in any external quotation:

> *"You cannot spend a mini-ledger UTxO unless the global or seize validator runs
> in the same transaction"* is proved against the production
> `programmableLogicBase` bytecode **for every ledger-normalized context**, with
> no shape bound of any kind. It is the only headline in the campaign of which
> that is true, and it is the one on which the composition's `p3_lifted` rests.

P3's remaining bound is the CEK budget (600 steps), bridged by
`WSC.LR_BUDGET_base`. That bound is orthogonal to coverage and is untouched here.

**And it is the existence proof for the recommendation in §6:** an unshaped prep
is not merely desirable, it is *demonstrated to work* on the smallest of the four
validators.

---

## 6. RECOMMENDATION — where the next unit of effort should go

Two routes could close audit F2's second half. They are not close.

### Route A — a coverage programme over shapes

What it needs, per property, per bound:

1. one shape per skeleton (§3: 10⁶ at a bound no real transfer fits in, 10⁹ at
   the smallest that does, 10¹⁴ at T1R's own);
2. a prep, a theorem, a vacuity probe and a control for each;
3. a **range characterization** per shape — the lemma that turns "in the range of
   the builder" into ledger vocabulary. `Coverage.wdrl_range_char` is one of
   these, done in full for the smallest non-trivial component in the library
   (SHAPE T1R's two-script withdrawal map): ~15 lines, both directions, no
   solver. SHAPE T1R has 39 free leaves over 16 `TxInfo` fields, two structured
   reference-input datums, a redeemer map and a `Data`-encoded redeemer; the
   sixteen shapes have 586 leaves between them.

**Cost: 971 CPU-years at the smallest meaningful bound, for one property.** Route
A is closed.

### Route B — ~~fix Blaster defect D6~~ (DONE) and prove over fully symbolic contexts

This is the route P3 **used to** demonstrate. As of wsc-poc `main` @ 2306678 it
demonstrates nothing: P3 regressed to shaped (task N3), and no property in the
library is proved unshaped. Route B's appeal is unchanged in principle — a result
over fully symbolic contexts needs no coverage argument at all — but it now has
**no worked example**, which is a material weakening of the case for it.

What blocks it today, measured:

| obstacle | measurement | source |
|---|---|---|
| unshaped global prep is affordable at 1600 | **45.5 s** cold, `lake build` | `AUDIT.md` §8 F5 |
| …and does not complete at 3300 | probe retained, never completes | `WSC/Shaped/Probe/UnshapedCost.lean` |
| symbolic-context solve above the vacuity boundary | **killed at 5,241 s ≈ 87 min, NO verdict** (P5, unshaped) — against **≈2 s** for the same property shaped | `WSC/SHAPING-RESULTS.md:11` |
| unshaped seize prep at 2000 | never completed in 77 min | `SHAPE-BRIDGE.md` §247 |
| ~~**Blaster D6**~~ — **FIXED (N5, Blaster `4d320dd`); re-tested N6** | no longer blocks anything: both preps build (2.4 s / 9.4 s, exit 0) and SHAPE T3's accept class is measured non-empty. What remains is the **T3R/T4R re-cut**, without which Paths B/C have no node-realizable shape to be proved over | `AUDIT.md` D6, `Probe/{T3PrepFAILS,T4PrepFAILS}.lean` (now regression tests) |

So Route B is not free either — but its obstacles are **engineering defects in
the substrate with named reproductions**, whereas Route A's obstacle is
arithmetic. Prep/solve performance work buys, per validator, a result that
quantifies over every context; a coverage programme buys, per property per bound,
a result that quantifies over 10⁶–10¹⁴ enumerated skeletons and still needs the
same budget bridge. **D6 itself is now fixed**, so that part of Route B's cost is
already paid — but Route B also lost its demonstration (P3 regressed to shaped at
#112), so its remaining cost is less certain than this section claimed.

**Recommendation: do not start a coverage programme. Invest in unshaped
prep/solve cost, and in minimal LEDGER-level cuts of the B1W kind.** If Route B stalls, the correct fallback is not Route A but
Route C of `SHAPE-BRIDGE.md` §10 — the source-model route (`WSC/Model/*`, which
already quantify over arbitrary contexts) with an explicit per-model faithfulness
axiom. That trade is *stated* rather than hidden, which is more than a coverage
programme could offer at any affordable bound.

### 6.1 The cheap partial repairs, for completeness

Two of the five frozen dimensions could be un-frozen without new shapes, because
they are ledger fields the validators never dereference:

* `txInfoTxCerts` and `txInfoData` are `[]` in all sixteen shapes. A shape variant
  carrying one entry each would cost one prep (~1.3 s) per shape.

This would not change any coverage verdict — the *list-length* axes (§4.2) remain
— and is recorded only so that nobody mistakes the counterexamples for a defect
that a small edit removes. Two of the three witnesses are length changes and the
third is a constructor tag; **no parameterisation reaches any of them.**

---

## 7. WHAT THIS ADDS TO THE AUDIT'S FINDING LIST

`AUDIT.md` §8 **F2** should now read, in its coverage half:

> *Coverage — REFUTED for the current family, and priced.* `WSC/Coverage.lean`
> states `Covers` and proves `¬ Covers recutFamily ValidRewarding
> (SizeBound 2 2 2 2 0)` — at SHAPE T1R's own size, over all THIRTEEN re-cut
> shapes — with three node-realizable
> witnesses the production bytecode accepts in exactly 2,603 steps, the shape's
> own step count. The enumeration route is priced at 9.27 × 10⁹ skeletons
> (≈971 CPU-years, one property) at the smallest bound admitting a real transfer.
> P3 is unaffected: it is proved over a fully symbolic context and needs no
> coverage argument (`Coverage.unshaped_covers`,
> `Coverage.p3_lives_over_a_covering_class`).

And `AUDIT.md` §9 gains one entry:

> **Do not believe that a coverage argument is a matter of writing more shapes.**
> It is refuted for the family that exists, and priced out of reach for any
> family that would replace it.

---

## 8. REPRODUCTION

```bash
# the module (≈1.7 s cold once its imports are built)
lake build WSC.Coverage

# the whole library with it: expect 431 jobs, 162 ✅ markers
# (103 Valid + 59 Expected Falsified — this module still runs no solver),
# 0 errors, 20 `sorry` warnings, 5 unused-variable warnings
#
# NUMBERS RECONCILED AT THE G STAGE (2026-07-25) AND AGAIN AT H2. This block used
# to say "430 jobs, 158 ✅ markers (101 Valid + 57 Expected Falsified)", which was
# the E4-era state; the G stage took it to 432 jobs / 162 markers / 94 modules, and
# H2's dead-file cleanup took the jobs to 431 and the modules to 93 with the 162
# markers UNCHANGED. WSC/AUDIT.md §1.2 is the authority for the current figures:
# 431 jobs, 1:49-2:00 wall, 1.50-1.66 GB (load-dependent), 93 WSC modules.
# The decision table for the deletions is WSC/AUDIT.md §12.
lake build WSC WSC.ShapeBridge 2>&1 | tee build.log
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c
grep -c 'error:' build.log

# the axiom census that matters — no sorryAx, no project axiom on the negatives
grep "Coverage\." build.log | grep "depends on axioms"
#   not_covers_at_T1R_size                     -> propext, ofReduceBool, trustCompiler, Quot.sound
#   not_covers_at_T1R_size'                    -> same
#   not_covers_with_three_reference_inputs     -> same
#   family_invariants                          -> propext, Quot.sound
#   ctxOk_in_family                            -> propext
#   wdrl_range_char                            -> propext
#   unshaped_covers                            -> propext
#   p3_lives_over_a_covering_class             -> + sorryAx  (inherited from P3's blaster verdict; EXPECTED)

# the three skeleton counts, native_decide-checked
#   skeletons_at_M1R_size              = 995_328
#   skeletons_at_minimal_transfer_size = 9_269_489_664
#   skeletons_at_T1R_size              = 305_258_198_870_016
```

## 9. FILES

| path | role |
|---|---|
| `WSC/Coverage.lean` | the deliverable: `Covers`, `SizeBound`, the **14** shape ranges, `ShapeInvariants` + **14** per-shape proofs, the refutation schema, 3 counterexamples with realizability / acceptance / step-count measurements, the **`WdrlPair`** P3 statement + `wdrlPair_char` (which REPLACED the retired no-coverage-needed claim), `wdrl_range_char`, the skeleton arithmetic, the axiom audit |
| `WSC/COVERAGE.md` | this document |
| `WSC/SHAPE-BRIDGE.md` §10 | the three routes, recorded by task U1 and unsolved — Route 1 is the one priced out here |
| `WSC/AUDIT.md` §8 F2 | the finding this answers, in its coverage half only |
