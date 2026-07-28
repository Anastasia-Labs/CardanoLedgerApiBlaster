-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/RealizableLeavesS1R.lean — **the SEIZE-purpose counterpart of
`WSC/Props/Shaped/RealizableLeaves.lean`** (task E1 step 3).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
`RealizableLeaves` composes over a TRANSFER class (SHAPE T1R): there `p1` is the
production `programmableLogicGlobal` bytecode and the other three leaves are the
shape. That leaves an obvious question a reader is entitled to ask — *is the
composition only ever carried by P1?* — and the answer is measured here rather
than argued: over a SEIZE class (SHAPE S1R) the load-bearing leaf is `p2`,
discharged from the production `programmableSeize` bytecode at budget 3800, and
`p1` is the one discharged by the shape.

One composed result per purpose family, and in each the ratio is 1 bytecode leaf
to 3 shape leaves. **That ratio is the honest measure of what the composition
buys**, and it is the same on both sides.

════════════════════════════════════════════════════════════════════════════
THE CLASS, AND EVERY CONJUNCT'S REASON — read this before quoting anything
════════════════════════════════════════════════════════════════════════════
`S1RShape hp ctx` is "`ctx`'s `TxInfo` is an instance of SHAPE S1R" plus SIX
identifications. Three are forced by the leaf statements (they are the S1R
analogues of `T1RShape`'s three), and three are genuine RESTRICTIONS of the
class, each stated here because each is doing work:

1. `hp.progLogicCred = .ScriptCredential plc` — FORCED. `WSC.P2b_R_containment`
   is about the base credential the params-UTxO datum publishes; the composition
   is about `hp.progLogicCred`.
2. `hp.seizeLogicCred = .ScriptCredential w0` — FORCED. SHAPE S1R runs at
   `RewardingScript (.ScriptCredential w0)` and the leaf triggers at
   `RewardingScript hp.seizeLogicCred`; without this the leaf's `ctx'` is not the
   shape's context. (It is also what makes `p4`'s third disjunct true.)
3. `NoGlobalWdrl hp ctx` — RESTRICTION, and the mirror image of
   `RealizableLeaves.NoSeizeWdrl`: the deployment's GLOBAL credential is not in
   this transaction's withdrawal map, so the transfer validator does not run and
   `p1` has no instances. SHAPE S1R withdraws at `w0` (the seize script) and `w1`
   (`= ilsH`, the issuer-logic script the accept path forces); nothing in the
   shape says the global credential is neither, exactly as nothing in SHAPE T1R
   said the seize credential is neither.
4. `SeizeWithinBudget hp ctx` — RESTRICTION, and it is `WithinBudget`'s MISSING
   CLAUSE. `Composition.WithinBudget` publishes base/minting/global step bounds
   and deliberately has NO seize clause (its docstring says so: "nothing here
   consumes `K_seize` and `LeafSet.p2` is open, so adding a clause would only
   narrow the class for no gain"). Discharging `p2` from the bytecode is exactly
   what needs it, so the clause is carried by the class instead — same shape,
   same constant `WSC.K_seize = 3800`, quantified over every `SameTx` view.
   **This is an assumption about the transaction, and it is the price of using
   `WSC.LR_BUDGET_seize` at all.**
5. `mlCS = key` — RESTRICTION: the mini-ledger UTxO's non-ada policy IS the
   seized policy. `WSC.P2b_R_containment` is a theorem about the SEIZED policy
   only (`key`, position 0 of the datum of the reference input the redeemer
   selects); the composition's `p2` demands containment for EVERY policy. This
   conjunct is what makes the two coincide, and §3 states the alternative
   plainly: without it the non-seized policies need "structure preserved ⟹
   contained", the UNWRITTEN lemma `LeafSet.p2`'s own docstring names.
6. `mCS = key` — RESTRICTION, for the same reason on the mint side: a seize
   transaction in this class mints only the seized policy. (SHAPE S1R's mint
   field is `Shape.mintOne mCS mTn mQ` with `mQ` FREE and possibly positive; a
   positive mint of a policy that is *not* the seized one is not contained by
   anything the seize validator checks, and would make `p2` FALSE. §3.4 is the
   proof-level statement of that, and it is a real limit of the leaf, not of this
   module.)

`escH ≠ plc` is NOT required: §3.3 handles the second output for every `escH`.

**THE CLASS IS NOT EMPTY.** §5 re-certifies `WSC.P2RWitness.ctxAccept` — the
SHAPE-S1R witness that satisfies `validRewardingContext`, both halves of Conway's
`redeemersExactAllPlutus`, and real-CEK acceptance at K = 3004 — as a member (`mlCS = mCS
= key = "MMM"`, withdrawals at `AASEIZE`/`ZZILS`, base `PROGLOGIC`).

════════════════════════════════════════════════════════════════════════════
SCORECARD — the number to quote
════════════════════════════════════════════════════════════════════════════
| leaf | discharged BY | acceptance hypothesis used? |
|---|---|---|
| `p2` | **THE BYTECODE** — `WSC.P2b_R_containment`, production `programmableSeize` @ 3800, via `bridge_S1R` + `WSC.LR_BUDGET_seize` | **YES** (`NodeAcceptsSeize`) |
| `p1` | the SHAPE + the LEDGER RULE (no global withdrawal ⟹ the transfer validator cannot run) | no — bound as `_` |
| `p4` | the SHAPE (the seize credential IS withdrawn at — custody arm 3) | no — bound as `_` |
| `nopre` | the SHAPE (neither output decodes as a directory node) | — |

ONE of four leaves is the bytecode; three are the shape. Same ratio as the
transfer side, opposite leaf.
-/
import WSC.Props.Shaped.RealizableLeaves
import WSC.Props.Shaped.P2ShapedR
import WSC.Props.Shaped.NonVacuity
import WSC.Runs
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace WSC
namespace RealizableLeaves

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptInfo ScriptHash
                          ScriptPurpose TokenName TxInInfo TxOut findRedeemer
                          validScriptContext validScriptInfo validRewardingContext adaSymbol
                          credentialInWithdrawals)
open CardanoLedgerApi.V1.Value (valueOf)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §1 The SHAPE-S1R shape bridge

The `WSC/ShapeBridge.lean` pattern at the re-cut seize shape (`bridge_S1`/`exec_S1`
there are the SHAPE-S1 originals, and S1's class is proved EMPTY, which is why
they cannot be used). LEVEL 2 by `rfl`, LEVEL 3′ by `blaster`. The right-hand side
is the RAW metered CEK run `WSC.LR_BUDGET_seize` names. -/

/-- **LEVEL 2, SHAPE S1R.** Kernel-checked; no solver, no `admit`. -/
theorem exec_S1R
    (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    appliedSeizeRShaped3800.exec ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee
      = Runs.seizeRun 3800 ppCS
          (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 spRed mtRed ilRed fee) := rfl

/-- **LEVEL 3′, SHAPE S1R** — the bridge at the level `WSC.P2b_R_containment`
lives on. -/
theorem bridge_S1R
    (ppCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer) :
    isSuccessful (appliedSeizeRShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee)
      ↔ isSuccessful
          (Runs.seizeRun 3800 ppCS
            (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
              wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
              escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
              pHash pCS pTn pAda pQty dirCS plc glc slc
              nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
              w0 w1 a0 a1 spRed mtRed ilRed fee)) := by blaster

/-! ## §2 The class -/

/-- The GLOBAL mirror of `RealizableLeaves.NoSeizeWdrl`: this transaction does not
withdraw at the deployment's global (transfer) credential. -/
def NoGlobalWdrl (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = false

/-- **`Composition.WithinBudget`'s missing seize clause**, carried by the class.
Same form and same constant as its three published siblings. -/
def SeizeWithinBudget (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  ∀ ctx', Composition.SameTx ctx ctx' →
    WSC.nodeStepsSeize hp.protocolParamsCS ctx' ≤ WSC.K_seize

/-- **SHAPE S1R as a class of ledger transactions.** `key` — the seized policy —
appears THREE times on purpose: as the directory node's key (where the validator
reads it), as the mini-ledger UTxO's policy, and as the minted policy. Those last
two are the module header's restrictions 5 and 6. -/
def S1RCore (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  ∃ plc w0 key, hp.progLogicCred = Credential.ScriptCredential plc ∧
    hp.seizeLogicCred = Credential.ScriptCredential w0 ∧
    ∃ mlH inStk i0Ada mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
      oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mTn mQ
      pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      next tlsH ilsH gsCS w1 a0 a1 spRed mtRed ilRed fee,
      ctx.scriptContextTxInfo =
        (seizeRCtx mlH inStk i0Ada key mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty key mTn mQ
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
          w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo

/-- The full class: the shape, no global withdrawal, and the seize step bound. -/
def S1RShape (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  S1RCore hp ctx ∧ NoGlobalWdrl hp ctx ∧ SeizeWithinBudget hp ctx

/-! ## §3 The four leaves -/

/-! ### §3.1 `LeafSet.p1` — BY THE SHAPE, through the same ledger rule as
`RealizableLeaves.p2_of_noSeizeWdrl`

`validScriptInfo`'s `RewardingScript` clause
(`CardanoLedgerApi/V3/Contexts.lean:1014`) requires the running credential to be
in `txInfoWdrl`, so a transaction that does not withdraw at the global credential
cannot have the transfer validator run on it. **The acceptance hypothesis is
UNUSED and bound as `_`**: no bytecode result about `programmableLogicGlobal` is
involved here, and a reader must not read it as one. -/
theorem p1_of_noGlobalWdrl (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (hng : ∀ ctx, Shape ctx → NoGlobalWdrl hp ctx) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.globalLogicCred →
      WSC.NodeAcceptsGlobal hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
      ¬ WSC.coveringIn hp.directoryNodeCS cs (WSC.dirPreState ctx) →
        Composition.Contain hp.progLogicCred cs tn ctx := by
  intro ctx ctx' cs tn _hdep _hoc hsh _hbud hsame hoc' hsi _hacc _hcs _hcov
  exfalso
  have hvsc : validScriptContext ctx' = true := WSC.LR_CTX ctx' hoc'
  have hvsi : validScriptInfo ctx' = true := by
    simp only [validScriptContext, Bool.and_eq_true] at hvsc; exact hvsc.1
  have hin : credentialInWithdrawals hp.globalLogicCred
      ctx'.scriptContextTxInfo.txInfoWdrl = true := by
    rw [validScriptInfo, hsi] at hvsi
    simp only [Bool.and_eq_true] at hvsi
    exact hvsi.2.2
  have hno := hng ctx hsh
  rw [Composition.SameTx] at hsame
  rw [hsame] at hin
  rw [NoGlobalWdrl] at hno
  rw [hno] at hin
  exact Bool.noConfusion hin

/-! ### §3.2 Vocabulary: the composition's sums ARE P2's sums

`Composition.outAtB` folds `Composition.atBaseB base = (payCred o == base)`;
`WSC.P2.sumOutAtBase` folds `WSC.outAtBase base o = (payCred o == base)`. Same
function, two names, one import boundary apart — proved rather than assumed. -/

theorem sumOutsIf_eq_sumOutAtBase (base : Credential) (cs : CurrencySymbol)
    (tn : TokenName) (os : List TxOut) :
    Composition.sumOutsIf (Composition.atBaseB base) cs tn os
      = WSC.P2.sumOutAtBase base cs tn os := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
      simp [Composition.sumOutsIf, WSC.P2.sumOutAtBase, Composition.atBaseB,
        WSC.outAtBase, ih]

theorem sumInsIf_eq_sumInAtBase (base : Credential) (cs : CurrencySymbol)
    (tn : TokenName) (is : List TxInInfo) :
    Composition.sumInsIf (Composition.atBaseB base) cs tn is
      = WSC.P2.sumInAtBase base cs tn is := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
      simp [Composition.sumInsIf, WSC.P2.sumInAtBase, Composition.atBaseB,
        WSC.inAtBase, WSC.outAtBase, ih]

/-- Off the minted policy the mint field holds nothing — SHAPE S1R's mint is
`Shape.mintOne`, one policy and one token name. -/
theorem valueOf_mintOne_off (cs0 tn0 : ByteString) (q : Integer) (cs tn : ByteString)
    (h : cs ≠ cs0) : valueOf cs tn (Shape.mintOne cs0 tn0 q) = 0 := by
  have hcs0 : (Data.B cs == Data.B cs0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hh; injection hh with hh; exact h hh
  simp [valueOf, Shape.mintOne, valueOf.visit, hcs0]

/-! ### §3.3 `LeafSet.p2` at SHAPE S1R — **the bytecode discharge**

The seize-side twin of `RealizableLeaves.§4`, link for link:

1. `WSC.LR_CTX` at `ctx'` gives `validScriptContext ctx'`, whose `validScriptInfo`
   conjunct pins `ctx'`'s redeemer to the `Rewarding w0` entry of SHAPE S1R's own
   redeemer map (`WSC.seizeR_findRewarding0`) — so `ctx'` IS the shape's context.
   Without this step the existentially-quantified redeemer
   `WSC.LR_WDRL_RUNS_VALIDATOR` hands the composition would leave `ctx'` and the
   shaped theorem's context different in their redeemer field and the bridge
   would silently not apply.
2. `SeizeWithinBudget` (the class's own clause, §2) gives
   `nodeStepsSeize … ctx' ≤ K_seize = 3800`.
3. `WSC.LR_BUDGET_seize` at 3800 — its non-vacuity hypothesis DISCHARGED by
   `WSC.NonVacuity.seizeNonVacuous_at_3800` (`native_decide` on the real CEK, no
   project axiom) — turns `NodeAcceptsSeize` into
   `isSuccessful (Runs.seizeRun 3800 …)`. **This is the FIRST use of
   `LR_BUDGET_seize` anywhere in the library** (audit F15: five of seven published
   budgets were consumed by nothing; this makes it four).
4. `bridge_S1R` (§1) turns that into the `.prop` term the P2 theorems quantify
   over. `PropExecFaithful` (audit F8) binds this step exactly as it binds T1R's.
5. `WSC.P2b_R_containment` — `✅ Valid`, budget 3800, witness K = 3004 — gives the
   containment inequality at the SEIZED policy `key`, for every token name.
6. Every other policy holds nothing at the mini-ledger and is not minted (the
   class's conjuncts 5/6), so containment there is `0 ≥ 0 + 0` — with the ONE
   subtlety that the second output may itself sit at the base credential, which
   only helps, by `WSC.NONNEG`.

**WHAT STEP 6 COSTS, stated plainly.** It is the reason conjuncts 5 and 6 exist.
`P2b_R_containment` is about the seized policy alone; the composition's `p2`
quantifies over all of them. The general gap — "structure preserved ⟹ contained
for a non-seized policy" — is the UNWRITTEN lemma `LeafSet.p2`'s docstring names,
and it is NOT written here. What is done instead is to restrict the class to
transactions where the question does not arise. A seize transaction that mints a
DIFFERENT policy and sends it off-base is outside this class, and `p2` is FALSE
for it on the seize acceptance alone (nothing the seize validator checks
constrains another policy's mint) — that is a limit of the leaf as stated, and the
custody leaf `p4` is what would have to answer it. -/
theorem p2_on_S1RShape (hp : WSC.HonestParams) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → S1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
      WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
        Composition.Contain hp.progLogicCred cs tn ctx := by
  intro ctx ctx' cs tn _hdep hoc hsh _hbud hsame hoc' hsi hacc hcs
  obtain ⟨⟨plc, w0, key, hplc, hw0, mlH, inStk, i0Ada, mlTn, i0Qty, dIn,
    wallet, i1Ada, i1CS, i1Tn, i1Qty, oStk, o0Ada, o0Qty, dOut,
    escH, o1Ada, o1CS, o1Tn, o1Qty, mTn, mQ,
    pHash, pCS, pTn, pAda, pQty, dirCS, glc, slc, nHash, nCS, nTn, nAda, nQty,
    next, tlsH, ilsH, gsCS, w1, a0, a1, spRed, mtRed, ilRed, fee, hEq⟩, _hng, hsb⟩ := hsh
  have hti' : ctx'.scriptContextTxInfo =
      (seizeRCtx mlH inStk i0Ada key mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty key mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo := by
    rw [hsame, hEq]
  -- STEP 1: `LR_CTX` pins `ctx'`'s redeemer, so `ctx'` IS the shape's own context.
  have hvsc : validScriptContext ctx' = true := WSC.LR_CTX ctx' hoc'
  have hvsi : validScriptInfo ctx' = true := by
    simp only [validScriptContext, Bool.and_eq_true] at hvsc; exact hvsc.1
  have hred : ctx'.scriptContextRedeemer = seizeShapedRedeemer := by
    simp only [validScriptInfo, Bool.and_eq_true, beq_iff_eq] at hvsi
    have h1 := hvsi.1
    rw [hsi, hw0, hti'] at h1
    simp only [seizeRCtx, ScriptInfo.toScriptPurpose, WSC.seizeR_findRewarding0] at h1
    exact Option.some.inj h1.symm
  have hctx' : ctx' =
      seizeRCtx mlH inStk i0Ada key mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty key mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 spRed mtRed ilRed fee := by
    refine RealizableLeaves.scriptContext_ext _ _ hti' ?_ ?_
    · rw [hred]; rfl
    · rw [hsi, hw0]; rfl
  -- STEP 2 + 3: the seize budget bridge, at 3800, with its non-vacuity discharged.
  have hsteps : WSC.nodeStepsSeize hp.protocolParamsCS ctx' ≤ WSC.K_seize := hsb ctx' hsame
  have hrun : isSuccessful (Runs.seizeRun WSC.K_seize hp.protocolParamsCS ctx') :=
    (WSC.LR_BUDGET_seize WSC.K_seize WSC.NonVacuity.seizeNonVacuous_at_3800
      hp.protocolParamsCS ctx' hoc' hsteps).mp hacc
  rw [hctx'] at hrun hvsc
  -- STEP 4: the shape bridge.
  have hprop : isSuccessful (appliedSeizeRShaped3800.prop hp.protocolParamsCS
      mlH inStk i0Ada key mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
      oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty key mTn mQ
      pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
      w0 w1 a0 a1 spRed mtRed ilRed fee) := (bridge_S1R ..).mpr hrun
  have hvrc : validRewardingContext
      (seizeRCtx mlH inStk i0Ada key mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty key mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 spRed mtRed ilRed fee) = true := hvsc
  -- STEP 5 / 6
  rw [Composition.Contain, Composition.outAtB, Composition.inAtB, hEq, hplc,
    sumOutsIf_eq_sumOutAtBase, sumInsIf_eq_sumInAtBase]
  by_cases hslot : cs = key
  · subst hslot
    exact WSC.P2b_R_containment hp.protocolParamsCS mlH inStk i0Ada cs mlTn i0Qty dIn
      wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty
      cs mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc
      nHash nCS nTn nAda nQty cs next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee tn
      hvrc hprop
  · -- every other policy: nothing at the mini-ledger, nothing minted
    have hmint : WSC.mintOf cs tn
        (seizeRCtx mlH inStk i0Ada key mlTn i0Qty dIn
          wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut
          escH o1Ada o1CS o1Tn o1Qty key mTn mQ
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
          w0 w1 a0 a1 spRed mtRed ilRed fee).scriptContextTxInfo.txInfoMint = 0 := by
      simp only [seizeRCtx, WSC.mintOf]
      exact valueOf_mintOne_off key mTn mQ cs tn hslot
    have hi0 : valueOf cs tn (Shape.adaPlusOne i0Ada key mlTn i0Qty) = 0 :=
      RealizableLeaves.valueOf_adaPlusOne_off i0Ada key mlTn i0Qty cs tn hcs
        (fun h => hslot h.1)
    have ho0 : valueOf cs tn (Shape.adaPlusOne o0Ada key mlTn o0Qty) = 0 :=
      RealizableLeaves.valueOf_adaPlusOne_off o0Ada key mlTn o0Qty cs tn hcs
        (fun h => hslot h.1)
    -- the second output may itself sit at the base credential; `NONNEG` covers it
    have hnn := (WSC.NONNEG ctx hoc).2.2
    have ho1mem : seizeShapedOut1 escH o1Ada o1CS o1Tn o1Qty
        ∈ ctx.scriptContextTxInfo.txInfoOutputs := by
      rw [hEq]; simp [seizeRCtx]
    have ho1 : 0 ≤ valueOf cs tn (Shape.adaPlusOne o1Ada o1CS o1Tn o1Qty) :=
      hnn _ ho1mem cs tn
    rw [hmint]
    simp only [seizeRCtx, WSC.P2.sumOutAtBase, WSC.P2.sumInAtBase, seizeShapedIn0,
      seizeShapedIn1, seizeShapedOut0, seizeShapedOut1, WSC.outAtBase, WSC.inAtBase,
      WSC.payCred, hi0, ho0]
    split <;> split <;> simp_all <;> omega

/-! ### §3.4 `LeafSet.p4` and `LeafSet.nopre` — BY THE SHAPE -/

/-- The head case of CLAB's withdrawal-map membership test. (`Recursor.any`
compiles to a HYGIENIC `let rec`, so its auxiliary cannot be named in a `simp`
set; the one-step unfolding is a `rfl` and this lemma is where that is done
once.) -/
theorem credentialInWithdrawals_head (c : Credential) (a : Integer)
    (rest : CardanoLedgerApi.V3.Withdrawals) :
    credentialInWithdrawals c ((c, a) :: rest) = true := by
  have h : credentialInWithdrawals c ((c, a) :: rest)
      = ((c == c) || credentialInWithdrawals c rest) := rfl
  rw [h, beq_self_eq_true, Bool.true_or]

/-- **`LeafSet.p4` at SHAPE S1R.** Custody arm 3: the transaction DOES withdraw at
the seize credential — it is a seize transaction — so the third disjunct holds by
computation. No bytecode, and `NodeAcceptsMinting` is unused and bound as `_`.

Note this is the OPPOSITE disjunct from SHAPE T1R's (which mints nothing and takes
arm 4). Both are the shape, neither is the issuance policy's bytecode. -/
theorem p4_on_S1RShape (hp : WSC.HonestParams) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (mlh : ScriptHash),
      WSC.Deployed hp → WSC.OnChain ctx → S1RShape hp ctx → Composition.WithinBudget hp ctx →
      Composition.SameTx ctx ctx' → WSC.OnChain ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.MintingScript cs →
      WSC.NodeAcceptsMinting hp.protocolParamsCS mlh ctx' →
      cs ≠ adaSymbol →
        WSC.noEscape hp.progLogicCred cs ctx.scriptContextTxInfo.txInfoOutputs = true
        ∨ credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
        ∨ credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
        ∨ WSC.mintPos cs ctx.scriptContextTxInfo.txInfoMint = false := by
  intro ctx _ctx' cs _mlh _hdep _hoc hsh _hbud _hsame _hoc' _hsi _hacc _hcs
  obtain ⟨⟨plc, w0, key, _hplc, hw0, mlH, inStk, i0Ada, mlTn, i0Qty, dIn,
    wallet, i1Ada, i1CS, i1Tn, i1Qty, oStk, o0Ada, o0Qty, dOut,
    escH, o1Ada, o1CS, o1Tn, o1Qty, mTn, mQ,
    pHash, pCS, pTn, pAda, pQty, dirCS, glc, slc, nHash, nCS, nTn, nAda, nQty,
    next, tlsH, ilsH, gsCS, w1, a0, a1, spRed, mtRed, ilRed, fee, hEq⟩, _hng, _hsb⟩ := hsh
  refine Or.inr (Or.inr (Or.inl ?_))
  rw [hEq, hw0]
  simp only [seizeRCtx, seizeShapedWdrl]
  exact credentialInWithdrawals_head _ _ _

/-- An output whose datum is a raw `Data.B` cannot decode as a directory node. -/
theorem dirNodeKey_eq_none_of_B (o : TxOut) (b : ByteString)
    (h : o.txOutDatum = .OutputDatum (Data.B b)) : WSC.dirNodeKey o = none := by
  simp [WSC.dirNodeKey, WSC.dirNodeDatum, h]
  rfl

/-- **`LeafSet.nopre` at SHAPE S1R.** SHAPE S1R's two outputs carry a raw
`Data.B` datum and `NoOutputDatum` respectively, so neither decodes as a directory
node, `registeredIn` is false and the obligation is discharged by `absurd` — a
seize transaction registers no policy. Same disposition, and the same scope
caveat, as `RealizableLeaves.nopre_on_T1RShape`: this observes that the general
problem does not arise in this class, it does not solve it. -/
theorem nopre_on_S1RShape (hp : WSC.HonestParams) :
    ∀ (L : Composition.Ledger) (ctx : ScriptContext) (L' : Composition.Ledger)
      (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → Composition.LedgerStep L ctx L' →
      Composition.HonestTx hp (S1RShape hp) ctx →
      ¬ Composition.RegisteredIn hp L cs →
      WSC.registeredIn hp.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoOutputs →
        Composition.OutOfBase hp.progLogicCred cs tn L = 0
        ∧ Composition.NonEscape hp.progLogicCred cs tn ctx := by
  intro _L ctx _L' cs _tn _hdep _hstep htx _hreg hnew
  obtain ⟨_, _, hsh⟩ := htx
  obtain ⟨⟨plc, w0, key, _hplc, _hw0, mlH, inStk, i0Ada, mlTn, i0Qty, dIn,
    wallet, i1Ada, i1CS, i1Tn, i1Qty, oStk, o0Ada, o0Qty, dOut,
    escH, o1Ada, o1CS, o1Tn, o1Qty, mTn, mQ,
    pHash, pCS, pTn, pAda, pQty, dirCS, glc, slc, nHash, nCS, nTn, nAda, nQty,
    next, tlsH, ilsH, gsCS, w1, a0, a1, spRed, mtRed, ilRed, fee, hEq⟩, _hng, _hsb⟩ := hsh
  rw [hEq] at hnew
  simp only [seizeRCtx] at hnew
  obtain ⟨o, ho, _, hkey⟩ := hnew
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h
  · rw [h, dirNodeKey_eq_none_of_B _ dOut rfl] at hkey; exact absurd hkey (by simp)
  · rw [h, RealizableLeaves.dirNodeKey_eq_none _ rfl] at hkey; exact absurd hkey (by simp)

/-! ## §4 THE `LeafSet` AND THE COMPOSED RESULT — seize side, no leaf assumption -/

/-- **A complete `LeafSet` over the SEIZE class.** `p2` is the production
`programmableSeize` bytecode with its acceptance hypothesis CONSUMED; `p1`, `p4`
and `nopre` are the shape, with theirs unused. -/
theorem realizableLeavesS1R (hp : WSC.HonestParams) :
    Composition.LeafSet hp (S1RShape hp) :=
  { p4 := p4_on_S1RShape hp
  , p1 := p1_of_noGlobalWdrl hp (S1RShape hp) (fun _ h => h.2.1)
  , p2 := p2_on_S1RShape hp
  , nopre := nopre_on_S1RShape hp }

/-- **THE TOP CLAIM OVER THE SEIZE CLASS, ON NO LEAF ASSUMPTION.**
*Along any trace of honest SHAPE-S1R seize transactions from genesis, no UTxO
outside the mini-ledger holds a registered programmable token.*

BUDGETS AND SHAPE, so the bound travels with the claim: every step is a
transaction whose `TxInfo` is an instance of SHAPE S1R (two inputs — the
mini-ledger UTxO and a wallet input; two outputs — the continuing base output and
one other; a one-policy mint of the SEIZED policy; two script withdrawals, one of
them the seize script; a four-entry redeemer map covering all four script
witnesses; two reference inputs — protocol params and the directory node whose
key is the seized policy) and whose seize-validator run halts within
`K_seize = 3800` CEK steps. The accepting witness costs **K = 3004**. -/
theorem containment_on_seize_class (hp : WSC.HonestParams) (hdep : WSC.Deployed hp) :
    ∀ (L : Composition.Ledger), Composition.Reachable hp (S1RShape hp) L →
      Composition.I hp L :=
  Composition.top_claim hp (S1RShape hp) (realizableLeavesS1R hp) hdep

/-- The plain-English form. -/
theorem no_tokens_outside_mini_ledger_on_seize_class
    (hp : WSC.HonestParams) (hdep : WSC.Deployed hp)
    (L : Composition.Ledger) (hR : Composition.Reachable hp (S1RShape hp) L)
    (cs : CurrencySymbol) (tn : TokenName)
    (hcs : cs ≠ adaSymbol) (hreg : Composition.RegisteredIn hp L cs) :
    ∀ u ∈ L, WSC.payCred u.utxoOut ≠ hp.progLogicCred →
      valueOf cs tn u.utxoOut.txOutValue = (0:Int) :=
  Composition.no_programmable_tokens_outside_mini_ledger hp (S1RShape hp)
    (realizableLeavesS1R hp) hdep L hR cs tn hcs hreg

/-! ## §5 THE SEIZE CLASS IS NOT EMPTY

`WSC.P2RWitness.ctxAccept` is the SHAPE-S1R instance task C2 certified: it
satisfies `validRewardingContext`, both halves of Conway's `redeemersExactAllPlutus`, and
is ACCEPTED by the real compiled `programmableSeize` in 3,004 CEK steps
(`WSC.s1r_realizable`, `WSC.NonVacuity.seizeNonVacuous_at_3800`). Its leaves make
every conjunct of §2 true: base `PROGLOGIC`, seize credential `AASEIZE`, seized
policy `MMM`, mini-ledger policy `MMM`, minted policy `MMM`, withdrawals at
`AASEIZE` and `ZZILS` — so a deployment whose global credential is `GLOBAL` has
no global withdrawal in it.

The `SeizeWithinBudget` conjunct is about `WSC.nodeStepsSeize`, an OPAQUE AXIOM
(the node's step count), so like `WSC.OnChain` it cannot be discharged for any
concrete context in this library — §5.1 therefore certifies the two conjuncts that
CAN be checked and says so, rather than quietly dropping the third. -/

/-- A deployment whose parameters are the S1R witness's own leaves. -/
def witnessParamsS1R : WSC.HonestParams :=
  { protocolParamsCS := WSC.P2RWitness.ppCS
  , directoryNodeCS := ByteString.mk "DIRCS"
  , progLogicCred := .ScriptCredential (ByteString.mk "PROGLOGIC")
  , globalLogicCred := .ScriptCredential (ByteString.mk "GLOBAL")
  , seizeLogicCred := .ScriptCredential (ByteString.mk "AASEIZE") }

/-- **THE SHAPE AND THE NO-GLOBAL-WITHDRAWAL CONJUNCTS HOLD AT THE CERTIFIED
WITNESS.** (The third conjunct, `SeizeWithinBudget`, is a statement about the
opaque `nodeStepsSeize` and is not checkable here — see §5.) -/
theorem s1RShape_witness :
    S1RCore witnessParamsS1R WSC.P2RWitness.ctxAccept
    ∧ NoGlobalWdrl witnessParamsS1R WSC.P2RWitness.ctxAccept :=
  ⟨⟨ByteString.mk "PROGLOGIC", ByteString.mk "AASEIZE", ByteString.mk "MMM", rfl, rfl,
    ByteString.mk "PROGLOGIC", ByteString.mk "USERSTK", 300, ByteString.mk "TOK", 10,
    ByteString.mk "DTM", ByteString.mk "WALLET", 100, ByteString.mk "ZZZP",
    ByteString.mk "WT", 1, ByteString.mk "USERSTK", 300, 12, ByteString.mk "DTM",
    ByteString.mk "CHANGE", 50, ByteString.mk "ZZZP", ByteString.mk "WT", 1,
    ByteString.mk "TOK", 2,
    ByteString.mk "PANCHOR", ByteString.mk "PARAMS", ByteString.mk "PTOK", 100, 1,
    ByteString.mk "DIRCS", ByteString.mk "GLOBAL", ByteString.mk "SEIZELOGIC",
    ByteString.mk "DIRNODE", ByteString.mk "DIRCS", ByteString.mk "NODETOK", 100, 1,
    ByteString.mk "ZZZ", ByteString.mk "TLS", ByteString.mk "ZZILS", ByteString.mk "GS",
    ByteString.mk "ZZILS", 0, 0, ByteString.mk "SPRED", ByteString.mk "MTRED",
    ByteString.mk "ILRED", 50, rfl⟩,
   by rw [NoGlobalWdrl]; rfl⟩

/-- **THE INHABITANT IS ACCEPTED BY THE PRODUCTION BYTECODE, on the very term the
budget bridge names.** `WSC.P2RWitness.exec_accepts_at_3800` is `native_decide` on
the real CEK through `appliedSeizeRShaped3800.exec`; `exec_S1R` (§1, `rfl`) is what
carries it to `Runs.seizeRun 3800`. Exact cost K = 3004, pinned two-sided by
`WSC.P2RWitness.K_is_3004_and_3328`.

This matters more here than on the transfer side, because §2's conjuncts 5 and 6
RESTRICT the class: the check that they did not restrict it out of the accept
class is this theorem, not an argument. -/
theorem inhabitant_accepted_by_bytecode :
    isSuccessful (Runs.seizeRun 3800 WSC.P2RWitness.ppCS WSC.P2RWitness.ctxAccept) := by
  have h := WSC.P2RWitness.exec_accepts_at_3800
  rw [exec_S1R] at h
  exact h

/-- **AND THE INHABITANT IS NODE-REALIZABLE** — ledger-valid, redeemer-exact under
the Conway rule as C3 transcribed it, and accepted by the production bytecode. -/
theorem realizable_inhabitant_S1R :
    S1RCore witnessParamsS1R WSC.P2RWitness.ctxAccept
    ∧ NoGlobalWdrl witnessParamsS1R WSC.P2RWitness.ctxAccept
    ∧ CardanoLedgerApi.V3.validRewardingContext WSC.P2RWitness.ctxAccept = true
    ∧ CardanoLedgerApi.V3.Contexts.redeemersExactAllPlutus
        WSC.P2RWitness.ctxAccept.scriptContextTxInfo = true
    ∧ isSuccessful (Runs.seizeRun 3800 WSC.P2RWitness.ppCS WSC.P2RWitness.ctxAccept) :=
  ⟨s1RShape_witness.1, s1RShape_witness.2,
   WSC.P2RWitness.all_four_valid.1, by native_decide, inhabitant_accepted_by_bytecode⟩

/-! ## §6 AXIOM AUDIT, printed at build time -/

#print axioms exec_S1R
#print axioms bridge_S1R
#print axioms p1_of_noGlobalWdrl
#print axioms p2_on_S1RShape
#print axioms p4_on_S1RShape
#print axioms nopre_on_S1RShape
#print axioms realizableLeavesS1R
#print axioms containment_on_seize_class
#print axioms no_tokens_outside_mini_ledger_on_seize_class
#print axioms s1RShape_witness
#print axioms inhabitant_accepted_by_bytecode
#print axioms realizable_inhabitant_S1R

end RealizableLeaves
end WSC
