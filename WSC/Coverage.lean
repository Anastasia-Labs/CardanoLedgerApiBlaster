/-
WSC/Coverage.lean — **THE SHAPE-COVERAGE QUESTION, STATED IN LEAN, AND ANSWERED
IN THE NEGATIVE FOR THIS LIBRARY'S TWELVE SHAPES** (task E4, audit finding **F2**
second half).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
Every UPLC result in this campaign is bounded twice: by a CEK step budget `K`
and by a fixed `Data` skeleton — a SHAPE. `WSC/SHAPE-BRIDGE.md` §10 records the
consequence in one line:

> the bridge says "shaped theorem about σ's leaves ⟹ statement about every
> `ScriptContext` in `range σ`", and says **nothing** about contexts outside
> `range σ`.

`WSC/AUDIT.md` §8 F2 calls the missing argument the binding constraint, and
audit §9.3 says "do not believe any UPLC result is universally quantified over
transactions". Until now the gap was an UNKNOWN: nobody had written down what
coverage would even mean, so nobody could say whether it was within reach.

This module writes the statement down (§1), and then decides it — negatively —
for the twelve re-cut shapes of tasks C1/C2 (§6). **The result is a theorem, not
an absence of one**: the family does not cover, at a size bound that admits
nothing bigger than the shapes themselves already contain, and the three
witnesses are node-realizable transactions that the production
`programmableLogicGlobal` bytecode ACCEPTS.

════════════════════════════════════════════════════════════════════════════
WHAT IS PROVED HERE, AND WHAT IS NOT — read this before quoting anything
════════════════════════════════════════════════════════════════════════════
**PROVED (this module).**

1. `not_covers_at_T1R_size` — the twelve-shape family does **not** cover the
   rewarding-context class at bound `SizeBound 2 2 2 2 0` (≤2 inputs, ≤2
   reference inputs, ≤2 outputs, ≤2 withdrawals, 0 mint entries), which is
   *exactly SHAPE T1R's own size*. Two independent witnesses.
2. `not_covers_with_three_reference_inputs` — likewise at `SizeBound 2 3 2 2 0`.
3. Each witness is `validRewardingContext` **and** `redeemersExact` — the two
   conjuncts `WSC.t1R_realizable` quotes for the campaign's own certified
   inhabitant — and each is ACCEPTED by the real compiled global validator in
   `Runs.globalRun 4400`, by `native_decide` on the CEK machine (§5).
4. `p3_lives_over_a_covering_class` — P3, the keystone, is proved over the
   UNSHAPED class, and the one-element family `[unshapedClass]` covers every
   bound (`unshaped_covers`). **P3 needs no coverage argument at all.** It is the
   only property in the campaign of which that is true, and it is the single
   most important sentence in this module.
5. `wdrl_range_char` — a genuine, non-circular coverage lemma for ONE component
   (the two-script withdrawal map): a `Withdrawals` list is in the range of
   `p1ShapedWdrl` **iff** it has length 2 and both credentials are script
   credentials. This is the unit of work a coverage programme would have to do,
   and it is here so that `WSC/COVERAGE.md`'s cost estimate is an extrapolation
   from a measured unit rather than a guess.

**NOT PROVED, and NOT claimed.**

* This is **not** "coverage is impossible". It is "*these twelve shapes* do not
  cover *this bound*", plus an arithmetic argument in `WSC/COVERAGE.md` that the
  enumeration route is not affordable. A different, larger family could cover a
  smaller bound; nothing here rules that out.
* The three counterexample contexts meet the campaign's own realizability bar
  (`validRewardingContext ∧ redeemersExact`), which `WSC/Realizability.lean`
  states is **NECESSARY, NOT SUFFICIENT** for node acceptance — fees, witness-set
  agreement and the UTxO set are unmodelled. They are exactly as realizable as
  `P1RShapedWitness.ctxOk`, no more. The comparison is apples to apples, and it
  is the only comparison claimed.
* Nothing here says any *property* fails on the missed transactions. The global
  validator accepts all three; P1's containment postcondition is not evaluated
  on them, because no theorem in the library ranges over them. **A coverage gap
  is an absence of assurance, not the presence of a bug.**

════════════════════════════════════════════════════════════════════════════
THE SHAPE OF THE ARGUMENT — why these counterexamples are the right ones
════════════════════════════════════════════════════════════════════════════
A shape fixes two kinds of thing:

* **LIST LENGTHS and CONSTRUCTOR TAGS** — the `Data` skeleton. `#prep_uplc`
  cannot parameterise over these; freezing them is precisely what makes the prep
  tractable. Escaping them needs a NEW SHAPE (a new prep, a new set of theorems,
  a new vacuity probe), not a new parameter.
* **LEAF SCALARS** — `ByteString`s and `Integer`s, all symbolic.

The three counterexamples are of the first kind, so that "just add another
parameter" is not an available repair:

| witness | axis | what it is, in plain English |
|---|---|---|
| `ctxTwoSigners` | list length | a transfer that names **two** required signers |
| `ctxThreeRefIns` | list length | a transfer that reads **three** reference inputs |
| `ctxAlwaysRange` | constructor tag | a transfer with an **unbounded validity interval** — the default every wallet emits |

All twelve shapes carry ≤1 signatory, ≤2 reference inputs and a FINITE CLOSED
validity interval (`ShapeInvariants`, §3, proved shape by shape). None of the
three is exotic. ("What every wallet emits" is a statement about the world, not
a measurement in this repository; what is machine-checked is that an unbounded
validity interval is `validRewardingContext` and outside all twelve shapes.)

PROVENANCE / SCOPE. The twelve range predicates in §2 are transcribed
mechanically from the `def` signatures of the twelve shape builders at this
revision (`WSC/Shaped/{GlobalShapedR, MintingShapedR, MintingShapedRIdx,
MintingLocalShapedR, MintingDelegateShapedR, SeizeShapedR}.lean`); the free-leaf
count in each docstring is the builder's own arity, and the totals are reported
in `WSC/COVERAGE.md` §3. SHAPE L2 and the ten pre-C2 shapes are deliberately
**not** in the family: L2's class is proved empty (audit F19) and the pre-C2
classes are proved empty by `ShapeRealizability`, so adding them could only make
a coverage claim weaker, never stronger.
-/
import WSC.Props.Shaped.GlobalRealizability
import WSC.Props.Shaped.RealizableShapes
import WSC.Props.P3_Base
import WSC.Runs
import WSC.Realizability

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC
namespace Coverage

open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOutRef Withdrawals
                          validScriptContext validRewardingContext validSpendingContext
                          credentialInWithdrawals)
open CardanoLedgerApi.V3.Contexts (redeemersExact)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ════════════════════════════════════════════════════════════════════════
## §1 THE QUESTION, STATED

A **shape class** is a set of `ScriptContext`s. The only shape classes this
module ever builds are RANGES of the library's shape builders: `rangeT1R ctx`
says "`ctx` is `p1RShapedCtx` at *some* assignment of its 39 free leaves".

A **size bound** is what a reviewer means by "all transactions of that size":
upper bounds on the five list-valued dimensions a transaction is normally
measured in. It deliberately says NOTHING about signatory count, certificates,
datum witnesses, validity-interval form, or any other `Data`-skeleton feature —
because a reviewer told "≤2 inputs, ≤2 outputs, ≤1 mint policy" is not thereby
told anything about those, and §6 is the proof that this distinction is the
whole ballgame.

**COVERAGE** is then: every ledger-valid context inside the size bound is an
instance of some shape in the family. That is the property that would license
turning "proved over these shapes" into "proved for all transactions of this
size", and it is the property §6 refutes for this family.
-/

/-- A class of contexts. Intended reading: the RANGE of one shape builder. -/
abbrev ShapeClass := ScriptContext → Prop

/-- **The size bound**, in the five dimensions a transaction is normally
measured in. Nothing else is constrained — that is the point. -/
def SizeBound (mIn mRef mOut mWdrl mMint : Nat) (ctx : ScriptContext) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs.length ≤ mIn ∧
  ctx.scriptContextTxInfo.txInfoReferenceInputs.length ≤ mRef ∧
  ctx.scriptContextTxInfo.txInfoOutputs.length ≤ mOut ∧
  ctx.scriptContextTxInfo.txInfoWdrl.length ≤ mWdrl ∧
  ctx.scriptContextTxInfo.txInfoMint.length ≤ mMint

/-- **COVERAGE.** The finite family `fam` covers the class `Valid` at the bound
`Bound` when every valid context within the bound is an instance of some shape
in the family.

This is the statement a reviewer should check first. Read it as: *if this held,
then a theorem proved at every leaf assignment of every shape in `fam` would be
a theorem about every `Valid` transaction of that size.* Note what it does NOT
say: nothing about the CEK step budget (that bound is orthogonal and remains),
and nothing about whether the shapes' own theorems agree with each other. -/
def Covers (fam : List ShapeClass) (Valid Bound : ScriptContext → Prop) : Prop :=
  ∀ ctx, Valid ctx → Bound ctx → ∃ S ∈ fam, S ctx

/-- The ledger-validity side for the rewarding validators (the global/transfer
validator's purpose): CLAB's `validScriptContext` plus "the running purpose is
`Rewarding`". -/
def ValidRewarding (ctx : ScriptContext) : Prop :=
  validRewardingContext ctx = true

/-- The campaign's own realizability bar at a context: CLAB's ledger predicate
AND both halves of Conway's exact-redeemer rule. These are the two conjuncts
`WSC.t1R_realizable` quotes; §5's witnesses satisfy the same two, and nothing
more is claimed for them. -/
def RealizableRewarding (ctx : ScriptContext) : Prop :=
  validRewardingContext ctx = true ∧ redeemersExact ctx.scriptContextTxInfo = true

/-! ════════════════════════════════════════════════════════════════════════
## §2 THE TWELVE SHAPE RANGES

One `def` per re-cut shape, transcribed from the builder's `def` signature. The
existential binds exactly the builder's own arguments, so `rangeXYZ ctx` holds
iff `ctx` is an instance of SHAPE XYZ. This is the same "is an instance of the
shape" notion `RealizableLeaves.T1RShape` uses, minus the three deployment
identifications it additionally pins — those only SHRINK the class, so using the
larger class here is the conservative choice for a NEGATIVE coverage result. -/

/-- The range of shape builder `globalRShapedCtx` (31 free leaves). -/
def rangeG1R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer) (pHash pCS pTn : ByteString)
    (pAda pQty : Integer) (dirCS plc glc slc : ByteString) (nHash nCS nTn : ByteString)
    (nAda nQty : Integer) (key next tlsH ilsH gsCS : ByteString) (w0 : ByteString)
    (a0 rMint : Integer) (fee : Integer),
    globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc
      glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee
      = ctx

/-- The range of shape builder `memberRShapedCtx` (24 free leaves). -/
def rangeG6R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer) (ob1 : ByteString)
    (outAda1 : Integer) (qq1 : Integer) (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString) (w0 : ByteString) (a0 rMint : Integer) (fee : Integer),
    memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1 pHash pCS pTn pAda
      pQty dirCS plc glc slc w0 a0 rMint fee
      = ctx

/-- The range of shape builder `p1RShapedCtx` (39 free leaves). -/
def rangeT1R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (plc owner : ByteString) (inAda qIn : Integer) (ext : ByteString)
    (in2Ada qIn2 : Integer) (outAda qOut : Integer) (dest : ByteString)
    (escAda qEsc : Integer) (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString) (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rTls : Integer) (fee : Integer),
    p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
      pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 w1 a0 a1 rBase rTls fee
      = ctx

/-- The range of shape builder `p1RShapedMintCtx` (41 free leaves). -/
def rangeT2R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer) (dest : ByteString)
    (escAda qEsc : Integer) (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString) (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rMint rTls : Integer) (fee : Integer),
    p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda
      qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH
      gsCS w0 w1 a0 a1 rBase rMint rTls fee
      = ctx

/-- The range of shape builder `p1ROutCtx` (41 free leaves). -/
def rangeT6R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (plc owner : ByteString) (inAda qIn : Integer) (ext : ByteString)
    (in2Ada qIn2 : Integer) (outAda0 qOut0 outAda1 qOut1 : Integer) (dest : ByteString)
    (escAda qEsc : Integer) (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString) (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rTls : Integer) (fee : Integer),
    p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest
      escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next
      tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee
      = ctx

/-- The range of shape builder `p1ROutMintCtx` (43 free leaves). -/
def rangeT7R : ShapeClass := fun ctx =>
  ∃ (cs tn : ByteString) (q : Integer) (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer) (pHash pCS pTn : ByteString)
    (pAda pQty : Integer) (dirCS glc slc : ByteString) (nHash nCS nTn : ByteString)
    (nAda nQty : Integer) (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString)
    (a0 a1 : Integer) (rBase rMint rTls : Integer) (fee : Integer),
    p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
      dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key
      next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee
      = ctx

/-- The range of shape builder `mintRCtx` (18 free leaves). -/
def rangeM1R : ShapeClass := fun ctx =>
  ∃ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer) (owner : ByteString)
    (inAda qIn : Integer) (dest : ByteString) (outAda qOut : Integer) (w0 : ScriptHash)
    (a0 : Integer) (mlRed : ByteString) (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid
      = ctx

/-- The range of shape builder `mintRCtxIdx` (19 free leaves). -/
def rangeM2R : ShapeClass := fun ctx =>
  ∃ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer) (owner : ByteString)
    (inAda qIn : Integer) (dest : ByteString) (outAda qOut : Integer) (w0 : ScriptHash)
    (a0 : Integer) (mlRed : ByteString) (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer),
    mintRCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi
      tid wIdx
      = ctx

/-- The range of shape builder `localRCtx` (36 free leaves). -/
def rangeL1R : ShapeClass := fun ctx =>
  ∃ (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer) (pHash pCS pTn : ByteString)
    (pAda pQty : Integer) (dirCS plc glc slc : ByteString) (nHash nCS nTn : ByteString)
    (nAda nQty : Integer) (key next tlsH ilsH gsCS : ByteString) (w0 : ByteString)
    (a0 : Integer) (mlRed : ByteString) (fee : Integer),
    localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn
      pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0
      mlRed fee
      = ctx

/-- The range of shape builder `dtRCtx` (39 free leaves). -/
def rangeDT1R : ShapeClass := fun ctx =>
  ∃ (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer) (pHash pCS pTn : ByteString)
    (pAda pQty : Integer) (dirCS plc glc slc : ByteString) (nHash nCS nTn : ByteString)
    (nAda nQty : Integer) (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString)
    (a0 a1 : Integer) (mlRed glRed : ByteString) (fee : Integer),
    dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda
      pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
      mlRed glRed fee
      = ctx

/-- The range of shape builder `dsRCtx` (39 free leaves). -/
def rangeDS1R : ShapeClass := fun ctx =>
  ∃ (ownCS tn : ByteString) (q : Integer) (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer) (pHash pCS pTn : ByteString)
    (pAda pQty : Integer) (dirCS plc glc slc : ByteString) (nHash nCS nTn : ByteString)
    (nAda nQty : Integer) (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString)
    (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer) (fee : Integer),
    dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda
      pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
      mlRed sIdx fee
      = ctx

/-- The range of shape builder `seizeRCtx` (51 free leaves). -/
def rangeS1R : ShapeClass := fun ctx =>
  ∃ (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString) (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString)
    (i1Qty : Integer) (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer) (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString) (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString) (fee : Integer),
    seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada
      o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc
      slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee
      = ctx

/-! ════════════════════════════════════════════════════════════════════════
## §3 WHAT ALL TWELVE SHAPES FREEZE

Five features of the `Data` skeleton that **every** re-cut shape fixes, and that
`validRewardingContext` / `SizeBound` leave entirely free. Each is proved shape
by shape below, at every leaf assignment, by computation — no solver.

Each of the five is a genuine restriction on real transactions:

| field | what the shapes allow | what the ledger allows |
|---|---|---|
| `txInfoSignatories` | 0 or 1 (`[]` or `[owner]`) | any sorted list of required signers |
| `txInfoReferenceInputs` | 0, 1 or 2 | any list |
| `txInfoValidRange` | a FINITE lower bound (`range lo hi` only) | `NegInf` / `Finite` / `PosInf`, either closure |
| `txInfoTxCerts` | `[]` | any certificate list |
| `txInfoData` | `[]` | any sorted datum witness map |
-/

/-- The `Extended` constructor tag of a validity interval's LOWER bound, read
straight off the `Data`. `WSC.Shape.range lo hi` always yields `some 1`
(`Finite`); `NegInf` yields `some 0` and `PosInf` `some 2`
(`CardanoLedgerApi/V1/Time.lean:202-217, 336-348`). -/
def loBoundTag : Data → Option Integer
  | .Constr _ [.Constr _ [.Constr t _, _], _] => some t
  | _ => none

/-- The five skeleton features every one of the twelve re-cut shapes freezes. -/
structure ShapeInvariants (ctx : ScriptContext) : Prop where
  sigLe : ctx.scriptContextTxInfo.txInfoSignatories.length ≤ 1
  refLe : ctx.scriptContextTxInfo.txInfoReferenceInputs.length ≤ 2
  finiteLowerBound : loBoundTag ctx.scriptContextTxInfo.txInfoValidRange = some 1
  noCerts : ctx.scriptContextTxInfo.txInfoTxCerts = []
  noDatums : ctx.scriptContextTxInfo.txInfoData = []

section Invariants

theorem inv_G1R : ∀ ctx, rangeG1R ctx → ShapeInvariants ctx := by
  simp only [rangeG1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_G6R : ∀ ctx, rangeG6R ctx → ShapeInvariants ctx := by
  simp only [rangeG6R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_T1R : ∀ ctx, rangeT1R ctx → ShapeInvariants ctx := by
  simp only [rangeT1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_T2R : ∀ ctx, rangeT2R ctx → ShapeInvariants ctx := by
  simp only [rangeT2R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_T6R : ∀ ctx, rangeT6R ctx → ShapeInvariants ctx := by
  simp only [rangeT6R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_T7R : ∀ ctx, rangeT7R ctx → ShapeInvariants ctx := by
  simp only [rangeT7R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_M1R : ∀ ctx, rangeM1R ctx → ShapeInvariants ctx := by
  simp only [rangeM1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_M2R : ∀ ctx, rangeM2R ctx → ShapeInvariants ctx := by
  simp only [rangeM2R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_L1R : ∀ ctx, rangeL1R ctx → ShapeInvariants ctx := by
  simp only [rangeL1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_DT1R : ∀ ctx, rangeDT1R ctx → ShapeInvariants ctx := by
  simp only [rangeDT1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_DS1R : ∀ ctx, rangeDS1R ctx → ShapeInvariants ctx := by
  simp only [rangeDS1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

theorem inv_S1R : ∀ ctx, rangeS1R ctx → ShapeInvariants ctx := by
  simp only [rangeS1R, forall_exists_index]; intros; subst_vars
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl, rfl⟩

end Invariants

/-- **The family**: the twelve node-realizable shapes of tasks C1/C2 — every
shape in this library whose class is not proved empty. -/
def recutFamily : List ShapeClass :=
  [rangeG1R, rangeG6R, rangeT1R, rangeT2R, rangeT6R, rangeT7R,
   rangeM1R, rangeM2R, rangeL1R, rangeDT1R, rangeDS1R, rangeS1R]

/-- Every member of the family satisfies all five invariants at every leaf
assignment. This is the only fact about the shapes §6 uses. -/
theorem family_invariants :
    ∀ S ∈ recutFamily, ∀ ctx, S ctx → ShapeInvariants ctx := by
  intro S hS ctx h
  simp only [recutFamily, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact inv_G1R ctx h
  · exact inv_G6R ctx h
  · exact inv_T1R ctx h
  · exact inv_T2R ctx h
  · exact inv_T6R ctx h
  · exact inv_T7R ctx h
  · exact inv_M1R ctx h
  · exact inv_M2R ctx h
  · exact inv_L1R ctx h
  · exact inv_DT1R ctx h
  · exact inv_DS1R ctx h
  · exact inv_S1R ctx h

/-! ### §3.1 CONTROL — the range predicates are transcribed correctly

Without this the negative results of §6 could be an artefact of a mis-copied
binder list: a range predicate that accidentally denoted the empty set would
make `Covers` false for a reason that has nothing to do with coverage. The
campaign's own certified SHAPE-T1R inhabitant is exhibited INSIDE the family. -/

/-- CONTROL: `P1RShapedWitness.ctxOk` — the context `WSC.t1R_realizable`
certifies and `WSC.P1R_T1` reasons about — is in `rangeT1R`, hence in the
family. -/
theorem ctxOk_in_rangeT1R : rangeT1R P1RShapedWitness.ctxOk :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- CONTROL, in the form §4 consumes: the family is not empty at `ctxOk`. -/
theorem ctxOk_in_family : ∃ S ∈ recutFamily, S P1RShapedWitness.ctxOk :=
  ⟨rangeT1R, by simp [recutFamily], ctxOk_in_rangeT1R⟩

/-! ════════════════════════════════════════════════════════════════════════
## §4 THE REFUTATION SCHEMA

Four lines. If every shape in a family satisfies an invariant, and one valid
in-bound context violates it, the family does not cover. -/

theorem not_covers_of_invariant {fam : List ShapeClass}
    {Valid Bound : ScriptContext → Prop}
    (hfam : ∀ S ∈ fam, ∀ ctx, S ctx → ShapeInvariants ctx)
    (ctx₀ : ScriptContext) (hV : Valid ctx₀) (hB : Bound ctx₀)
    (hI : ¬ ShapeInvariants ctx₀) : ¬ Covers fam Valid Bound := by
  intro hcov
  obtain ⟨S, hS, hSctx⟩ := hcov ctx₀ hV hB
  exact hI (hfam S hS ctx₀ hSctx)

/-! ════════════════════════════════════════════════════════════════════════
## §5 THREE MISSED TRANSACTIONS

Each is `P1RShapedWitness.ctxOk` — the campaign's own certified SHAPE-T1R
inhabitant, accepted by the production bytecode in 2,603 CEK steps
(`WSC.t1R_realizable`, `P1RShapedWitness.K_T1R_is_2603`) — with **exactly one**
`Data`-skeleton feature changed. Every leaf scalar is untouched.

The point of building them this way is that the comparison is forced: they
differ from a context the library DOES reason about only in a dimension no
`SizeBound` mentions and no shape can parameterise over. -/

/-- `ctxOk` plus a second required signer. Sorted (`"OWNER" < "SIGNER2"`), so
`validSigners` still holds; adds no needed script, so `redeemersExact` still
holds; changes no value, so the balance is untouched. -/
def ctxTwoSigners : ScriptContext :=
  { P1RShapedWitness.ctxOk with
    scriptContextTxInfo :=
      { P1RShapedWitness.ctxOk.scriptContextTxInfo with
        txInfoSignatories := [ByteString.mk "OWNER", ByteString.mk "SIGNER2"] } }

/-- An ordinary third reference input: a pubkey-owned, ada-only UTxO at
`⟨"", 4⟩`, after the two the shape already carries (`⟨"",2⟩`, `⟨"",3⟩`), so the
reference list stays sorted and the redeemer's reference indices 0 and 1 still
point where they did. Reference inputs are not spent, so the balance is
untouched. -/
def extraRefIn : TxInInfo :=
  ⟨⟨ByteString.mk "", 4⟩,
   { txOutAddress := ⟨.PubKeyCredential (ByteString.mk "REFOWNER"), none⟩
   , txOutValue := Shape.adaOnly 100
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- `ctxOk` reading three reference inputs instead of two. -/
def ctxThreeRefIns : ScriptContext :=
  { P1RShapedWitness.ctxOk with
    scriptContextTxInfo :=
      { P1RShapedWitness.ctxOk.scriptContextTxInfo with
        txInfoReferenceInputs :=
          P1RShapedWitness.ctxOk.scriptContextTxInfo.txInfoReferenceInputs ++ [extraRefIn] } }

/-- The unbounded validity interval `(-∞, +∞)`, both bounds closed — Plutus's
`always`, and what a wallet emits when the transaction has no time constraint.
`Data` form per `CardanoLedgerApi/V1/Time.lean:202-205, 336-348`: `NegInf` is
`Constr 0 []`, `PosInf` is `Constr 2 []`, closure `True` is `Constr 1 []`. -/
def alwaysRange : Data :=
  Data.Constr 0 [ Data.Constr 0 [Data.Constr 0 [], Data.Constr 1 []]
                , Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []] ]

/-- `ctxOk` with no time constraint. -/
def ctxAlwaysRange : ScriptContext :=
  { P1RShapedWitness.ctxOk with
    scriptContextTxInfo :=
      { P1RShapedWitness.ctxOk.scriptContextTxInfo with
        txInfoValidRange := alwaysRange } }

/-! ### §5.1 All three are realizable, at exactly the campaign's own bar

`validRewardingContext ∧ redeemersExact` — the two conjuncts `WSC.t1R_realizable`
quotes. `native_decide`; no solver, no project axiom. -/

theorem ctxTwoSigners_realizable : RealizableRewarding ctxTwoSigners := by
  constructor <;> native_decide

theorem ctxThreeRefIns_realizable : RealizableRewarding ctxThreeRefIns := by
  constructor <;> native_decide

theorem ctxAlwaysRange_realizable : RealizableRewarding ctxAlwaysRange := by
  constructor <;> native_decide

/-! ### §5.2 All three are ACCEPTED by the production bytecode

`Runs.globalRun 4400` is the imported `programmableLogicGlobal.flat` on the
denoted context under a 4,400-step CEK meter — the same term
`WSC.LR_BUDGET_global` names and the same budget `WSC.P1R_T1` is proved at.
This is what makes the coverage gap bite: these are not contexts the validator
rejects, they are contexts it accepts and about which the library says
**nothing**. -/

/-- The protocol-params policy id of the T1R witness. -/
abbrev ppCS : CurrencySymbol := P1ShapedWitness.ppCS

theorem ctxTwoSigners_accepted :
    isSuccessful (Runs.globalRun 4400 ppCS ctxTwoSigners) :=
  P1ShapedWitness.isHaltB_sound _ (by native_decide)

theorem ctxThreeRefIns_accepted :
    isSuccessful (Runs.globalRun 4400 ppCS ctxThreeRefIns) :=
  P1ShapedWitness.isHaltB_sound _ (by native_decide)

theorem ctxAlwaysRange_accepted :
    isSuccessful (Runs.globalRun 4400 ppCS ctxAlwaysRange) :=
  P1ShapedWitness.isHaltB_sound _ (by native_decide)

/-- **THE MEASUREMENT THAT MAKES THE GAP CONCRETE.** Each of the three missed
transactions halts in EXACTLY 2,603 CEK steps and budget-errors at 2,602 — the
same two-sided bracket `P1RShapedWitness.K_T1R_is_2603` pins for the shape's own
certified inhabitant.

So the three are indistinguishable from a covered transaction *by the machine*:
same validator, same budget, same step count, same verdict. The ONLY thing that
puts them outside every theorem in this library is the `Data` skeleton. That is
what a shape bound costs, measured. -/
theorem missed_transactions_cost_exactly_2603_steps :
    (P1ShapedWitness.isHaltB (Runs.globalRun 2603 ppCS ctxTwoSigners) = true
     ∧ P1ShapedWitness.isHaltB (Runs.globalRun 2602 ppCS ctxTwoSigners) = false)
  ∧ (P1ShapedWitness.isHaltB (Runs.globalRun 2603 ppCS ctxThreeRefIns) = true
     ∧ P1ShapedWitness.isHaltB (Runs.globalRun 2602 ppCS ctxThreeRefIns) = false)
  ∧ (P1ShapedWitness.isHaltB (Runs.globalRun 2603 ppCS ctxAlwaysRange) = true
     ∧ P1ShapedWitness.isHaltB (Runs.globalRun 2602 ppCS ctxAlwaysRange) = false) := by
  native_decide

/-! ### §5.3 …and none of the three is in ANY of the twelve shapes -/

theorem ctxTwoSigners_outside : ¬ ShapeInvariants ctxTwoSigners := by
  intro h; exact absurd h.sigLe (by decide)

theorem ctxThreeRefIns_outside : ¬ ShapeInvariants ctxThreeRefIns := by
  intro h; exact absurd h.refLe (by decide)

theorem ctxAlwaysRange_outside : ¬ ShapeInvariants ctxAlwaysRange := by
  intro h; exact absurd h.finiteLowerBound (by decide)

/-! ### §5.4 …and all three are inside the size bound -/

theorem ctxTwoSigners_size : SizeBound 2 2 2 2 0 ctxTwoSigners := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem ctxAlwaysRange_size : SizeBound 2 2 2 2 0 ctxAlwaysRange := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem ctxThreeRefIns_size : SizeBound 2 3 2 2 0 ctxThreeRefIns := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ════════════════════════════════════════════════════════════════════════
## §6 THE RESULT — the twelve shapes DO NOT COVER

Stated at SHAPE T1R's own size: ≤2 inputs, ≤2 reference inputs, ≤2 outputs,
≤2 withdrawals, no mint. Not a bigger transaction, not a different validator, not
a harder budget — the *same size*, and the family still misses.

Read the two theorems as the sharp form of audit F2's second half: it is no
longer "no coverage argument exists", it is **"coverage is false for this family
at this bound, and here are three node-realizable transactions the production
validator accepts to prove it"**. -/

/-- **MAIN NEGATIVE RESULT.** The twelve re-cut shapes do not cover the
rewarding-context class at their own size. Witness: a transfer with two required
signers. -/
theorem not_covers_at_T1R_size :
    ¬ Covers recutFamily ValidRewarding (SizeBound 2 2 2 2 0) :=
  not_covers_of_invariant family_invariants ctxTwoSigners
    ctxTwoSigners_realizable.1 ctxTwoSigners_size ctxTwoSigners_outside

/-- The same conclusion from an independent axis: a transfer with an unbounded
validity interval — the default a wallet emits when the transaction has no time
constraint. Two independent witnesses at the same bound is the difference
between "an artefact of one modelling choice" and "a property of the
mechanism". -/
theorem not_covers_at_T1R_size' :
    ¬ Covers recutFamily ValidRewarding (SizeBound 2 2 2 2 0) :=
  not_covers_of_invariant family_invariants ctxAlwaysRange
    ctxAlwaysRange_realizable.1 ctxAlwaysRange_size ctxAlwaysRange_outside

/-- A third axis, at the next bound up: three reference inputs. -/
theorem not_covers_with_three_reference_inputs :
    ¬ Covers recutFamily ValidRewarding (SizeBound 2 3 2 2 0) :=
  not_covers_of_invariant family_invariants ctxThreeRefIns
    ctxThreeRefIns_realizable.1 ctxThreeRefIns_size ctxThreeRefIns_outside

/-- **The headline, in one term.** All three missed transactions are realizable
at the campaign's own bar AND accepted by the production `programmableLogicGlobal`
bytecode at the budget P1 is proved at. -/
theorem missed_transactions_are_realizable_and_accepted :
    (RealizableRewarding ctxTwoSigners ∧ isSuccessful (Runs.globalRun 4400 ppCS ctxTwoSigners))
  ∧ (RealizableRewarding ctxThreeRefIns ∧ isSuccessful (Runs.globalRun 4400 ppCS ctxThreeRefIns))
  ∧ (RealizableRewarding ctxAlwaysRange ∧ isSuccessful (Runs.globalRun 4400 ppCS ctxAlwaysRange)) :=
  ⟨⟨ctxTwoSigners_realizable, ctxTwoSigners_accepted⟩,
   ⟨ctxThreeRefIns_realizable, ctxThreeRefIns_accepted⟩,
   ⟨ctxAlwaysRange_realizable, ctxAlwaysRange_accepted⟩⟩

/-! ════════════════════════════════════════════════════════════════════════
## §7 THE ONE PROPERTY THAT NEEDS NO COVERAGE ARGUMENT — P3

**P3, the keystone, is proved over a fully symbolic `ScriptContext`.** Its
hypothesis is `validSpendingContext ctx` and nothing else: no shape, no `Data`
skeleton, no list length. So the class it ranges over is `⊤`, and the
one-element family `[unshapedClass]` covers **every** bound trivially.

This is worth stating loudly because it is the only property in the campaign of
which it is true, and because it is the existence proof for the alternative
route `WSC/COVERAGE.md` §6 recommends: an unshaped prep needs no coverage
argument *at all*. P3's remaining bound is the CEK budget (600 steps), which is
orthogonal and is bridged by `WSC.LR_BUDGET_base` — a bound this module does
not address and does not claim to. -/

/-- The unshaped class: every context. -/
def unshapedClass : ShapeClass := fun _ => True

/-- The one-element unshaped family covers every validity class at every
bound — the trivial positive instance, included so that `Covers` is visibly
provable as well as refutable. -/
theorem unshaped_covers (Valid Bound : ScriptContext → Prop) :
    Covers [unshapedClass] Valid Bound := by
  intro ctx _ _
  exact ⟨unshapedClass, by simp, trivial⟩

/-- **P3 lives over that class.** Verbatim `WSC.P3_base_requires_global_or_seize`
with the (vacuous) class hypothesis inserted, so that the pairing
"property + class it is proved over" is exhibited for the one case where the
class is everything. -/
theorem p3_lives_over_a_covering_class (globalCred seizeCred : Credential) :
    ∀ ctx, unshapedClass ctx →
      validSpendingContext ctx →
      isSuccessful (appliedBase.prop globalCred seizeCred ctx) →
        credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
        ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl :=
  fun ctx _ => P3_base_requires_global_or_seize globalCred seizeCred ctx

/-! ════════════════════════════════════════════════════════════════════════
## §8 WHAT A COVERAGE PROOF WOULD COST — one component, done

A coverage proof is a chain of RANGE CHARACTERIZATIONS: for each component of
the context, "the component is in the builder's range **iff** it satisfies these
ledger-vocabulary conditions". Below is one, in full, for the smallest
non-trivial component in the library — SHAPE T1R's two-script withdrawal map.

It is a real theorem (both directions, no solver) and it is NOT circular: the
right-hand side mentions only `length` and the `Credential` constructor, never
`p1ShapedWdrl`.

**It is also the cost anchor.** This one component took ~15 lines. SHAPE T1R has
39 free leaves spread over 16 `TxInfo` fields, two inputs, two reference inputs
with structured datums, two outputs, a withdrawal map, a redeemer map and a
`Data`-encoded redeemer; the twelve shapes together have 421 free leaves. The
extrapolation, and why the other side of the ledger (the number of skeletons)
makes the exercise pointless anyway, is `WSC/COVERAGE.md` §4-§5. -/

theorem wdrl_range_char (w : Withdrawals) :
    (∃ w0 w1 a0 a1, p1ShapedWdrl w0 w1 a0 a1 = w)
      ↔ (w.length = 2 ∧ ∀ e ∈ w, ∃ h, e.1 = Credential.ScriptCredential h) := by
  constructor
  · rintro ⟨w0, w1, a0, a1, rfl⟩
    refine ⟨rfl, ?_⟩
    intro e he
    simp only [p1ShapedWdrl, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨w0, rfl⟩
    · exact ⟨w1, rfl⟩
  · rintro ⟨hlen, hcred⟩
    rcases w with _ | ⟨⟨c0, a0⟩, t0⟩
    · simp at hlen
    · rcases t0 with _ | ⟨⟨c1, a1⟩, t1⟩
      · simp at hlen
      · rcases t1 with _ | ⟨e2, t2⟩
        · obtain ⟨h0, hh0⟩ := hcred (c0, a0) (by simp)
          obtain ⟨h1, hh1⟩ := hcred (c1, a1) (by simp)
          simp only at hh0 hh1
          subst hh0; subst hh1
          exact ⟨h0, h1, a0, a1, rfl⟩
        · simp at hlen

/-! ════════════════════════════════════════════════════════════════════════
## §9 HOW MANY SKELETONS ARE THERE? — the enumeration arithmetic, machine-checked

If coverage by enumeration were the route, the question is how many shapes a
family would need. The function below is a deliberate **LOWER** bound: every
factor counts a strict subset of the real choices, and four dimensions
(certificates, votes, proposals, datum witnesses) are counted as *one* option
each, i.e. as if they could only be empty.

Per resolved UTxO (input, reference input or output) the factors are
* payment credential: pubkey or script — **2**
* staking reference: `none`, `StakingHash PubKeyCredential`,
  `StakingHash ScriptCredential`, `StakingPtr` — **4**
* datum: `NoOutputDatum`, `OutputDatumHash`, `OutputDatum` — **3**
* reference script: present or not — **2**
* value shape: `valueShapes`, the number of (policy count, token-name count)
  profiles allowed. `valueShapes = 2` means "ada only, or ada + one policy with
  one token name" — i.e. exactly what `Shape.adaOnly` and `Shape.adaPlusOne`
  offer, and nothing else.

`WSC/COVERAGE.md` §4 gives the derivation and the two numbers this section
proves. -/

/-- Skeletons per resolved UTxO, at `valueShapes` value profiles. -/
def perUTxO (valueShapes : Nat) : Nat := 2 * 4 * 3 * 2 * valueShapes

/-- `∑_{i=lo}^{hi} b^i` — the number of lists of length between `lo` and `hi`
over an alphabet of `b` element skeletons. -/
def powSum (b lo hi : Nat) : Nat :=
  (List.range (hi + 1)).foldl (fun acc i => if lo ≤ i then acc + b ^ i else acc) 0

/-- LOWER bound on the number of distinct `Data` skeletons a `ScriptContext`
inside `SizeBound mIn mRef mOut mWdrl _` can have. `mintForms`, `rangeForms` and
`sigForms` are the mint-field, validity-interval and signatory-list profiles
counted separately. -/
def skeletonLowerBound (mIn mRef mOut mWdrl : Nat)
    (valueShapes mintForms rangeForms sigForms : Nat) : Nat :=
  powSum (perUTxO valueShapes) 1 mIn *
  powSum (perUTxO valueShapes) 0 mRef *
  powSum (perUTxO valueShapes) 1 mOut *
  powSum 2 0 mWdrl *
  mintForms * rangeForms * sigForms

/-- **At SHAPE T1R's own size** (≤2 in, ≤2 ref, ≤2 out, ≤2 wdrl; 2 value
profiles; mint empty-or-one-policy; 9 interval forms; 0–2 signatories):
**305,258,198,870,016** skeletons — 3.05 × 10¹⁴, against a family of **12**. -/
theorem skeletons_at_T1R_size :
    skeletonLowerBound 2 2 2 2 2 2 9 3 = 305258198870016 := by native_decide

/-- **At the SMALLEST interesting size** — SHAPE M1R's (1 input, 0 reference
inputs, 1 output, ≤1 withdrawal, 0–1 signatories): **995,328**. Even the floor
is five orders of magnitude above the twelve shapes that exist. -/
theorem skeletons_at_M1R_size :
    skeletonLowerBound 1 0 1 1 2 2 9 2 = 995328 := by native_decide

/-- **The number that decides the recommendation.** The SMALLEST bound that
admits even one real transfer transaction — 1 input, **2** reference inputs (the
global validator cannot run without its protocol-params reference input and the
directory node the redeemer points at), 1 output, ≤1 withdrawal, 0–1 signatories:
**9,269,489,664**. At the measured ~1.3 s prep + ~2 s solve per shape that is
≈ 971 single-core CPU-years, for ONE property, at the smallest bound where the
question is even meaningful. `WSC/COVERAGE.md` §5. -/
theorem skeletons_at_minimal_transfer_size :
    skeletonLowerBound 1 2 1 1 2 2 9 2 = 9269489664 := by native_decide

/-! ════════════════════════════════════════════════════════════════════════
## §10 AXIOM AUDIT

The two negative results and the three realizability facts must not depend on
anything but Lean's own axioms and `native_decide`'s compiler trust
(`Lean.ofReduceBool`, `Lean.trustCompiler`). In particular **no project axiom
and no `sorryAx`** — a refutation that leaned on an assumption would be worth
nothing. `p3_lives_over_a_covering_class` DOES carry `sorryAx`, inherited from
P3's `blaster` verdict, and that is expected and stated. -/

#print axioms not_covers_at_T1R_size
#print axioms not_covers_at_T1R_size'
#print axioms not_covers_with_three_reference_inputs
#print axioms missed_transactions_are_realizable_and_accepted
#print axioms missed_transactions_cost_exactly_2603_steps
#print axioms family_invariants
#print axioms ctxOk_in_family
#print axioms wdrl_range_char
#print axioms unshaped_covers
#print axioms skeletons_at_T1R_size
#print axioms skeletons_at_minimal_transfer_size
#print axioms p3_lives_over_a_covering_class

end Coverage
end WSC
