/-
WSC/Props/Shaped/P4DelegateShaped.lean — **P4's two DELEGATING custody arms,
PROVED at UPLC level against the real compiled issuance bytecode, over SHAPE DT1
and SHAPE DS1** (task V3 rungs 2 and 3).

With WSC/Props/Shaped/P4Shaped.lean (`BurnOnly`, SHAPE M1/M2) and
WSC/Props/Shaped/P4LocalShaped.lean (`Local`, SHAPE L1), this module completes the
**arm-by-arm coverage of the four-way P4 custody disjunction** (ARCHITECTURE
§3-P4) at UPLC against the real bytecode:

| arm | ground-truth predicate | shape | module | K of its witness |
|---|---|---|---|---|
| 1 `Local` | `LocalCustodyOk` | L1 | P4LocalShaped.lean | 1681 |
| 2 `DelegateTransfer` | `DelegateTransferOk` | **DT1** | **this file** | **1257** |
| 3 `DelegateSeize` | `DelegateSeizeOk` | **DS1** | **this file** | **1466** |
| 4 `BurnOnly` | `BurnOnlyOk` | M1 / M2 | P4Shaped.lean, P4ShapedIdx.lean | 784 |

READ THE HONESTY NOTE IN `P4_disjunction_at_DT1` BEFORE QUOTING THIS AS "P4 IS
PROVED": the disjunction is proved SHAPE BY SHAPE because a shape fixes the
redeemer's constructor tag and the tag selects the arm. Four shaped theorems whose
shapes differ only in the redeemer are strictly weaker than one theorem over a
symbolic redeemer, and no shape-coverage argument exists
(WSC/SHAPING-RESULTS.md §7).

════════════════════════════════════════════════════════════════════════════
PLAIN ENGLISH
════════════════════════════════════════════════════════════════════════════
**SHAPE DT1 / arm 2.** *If the real compiled issuance policy accepts a
`DelegateTransfer` mint of shape DT1, then (a) the token's minting-logic script
ran, (b) the minted policy's directory NFT is present on a REFERENCE INPUT — not
merely on an output — and (c) the mini-ledger's global transfer validator is
itself running on this transaction, because its credential (the one the params
datum publishes) is in the withdrawal map.* Custody is delegated, and the
delegation is real: the delegate is provably invoked.

**SHAPE DS1 / arm 3.** *If the real compiled issuance policy accepts a
`DelegateSeize` mint of shape DS1, then (a) the minting-logic script ran, (b) the
minted policy's directory NFT is present on a reference input, and (c) some
redeemer of the transaction is a `SeizeAct` for the params datum's SEIZE
credential whose own `directoryNodeIdx` resolves to a reference input carrying
that same policy's directory NFT* — i.e. the seizure is scoped to this policy's
node and cannot be a seizure of somebody else's token smuggled in as
authorization.

════════════════════════════════════════════════════════════════════════════
WHAT THESE TWO ARMS DO *NOT* GIVE YOU (read before using them)
════════════════════════════════════════════════════════════════════════════
Both are DELEGATION theorems. They prove that the script which is supposed to
enforce custody is running; they do not prove what that script enforces. Arm 2's
custody content is exactly the strength of P1 (containment in the global transfer
validator) and arm 3's is exactly the strength of P2 (seize structure +
quantities). Neither P1 nor P2 is proved at UPLC — see the OBLIGATION STATUS
blocks in WSC/Props/P1_Transfer.lean and WSC/Props/P2_Seize.lean, which record
what is proved on the SOURCE MODELS and what is missing.

Consequence for the campaign: **`Local` (P4LocalShaped.lean) is the only arm whose
no-escape guarantee is presently a theorem about bytecode rather than a forward
reference.** That asymmetry is the single most important thing to carry out of
this module.

════════════════════════════════════════════════════════════════════════════
SCOPE — TWO BOUNDS, BOTH BINDING
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 2500** (ADDENDUM E1), bridged to node acceptance by
`LR_BUDGET_minting` (WSC/Honest.lean). The concrete witnesses cost K = 1257 (DT1)
and K = 1466 (DS1), pinned as theorems below.

**Bound 2 — SHAPE DT1 / SHAPE DS1**, published in full in
WSC/Shaped/MintingDelegateShaped.lean's header. Both are SHAPE L1's skeleton
(WSC/Shaped/MintingLocalShaped.lean) with the redeemer replaced: one pubkey input
carrying ada plus `ownCS`, exactly two reference inputs (params node then claimed
registration node), exactly two script-address outputs, a one-policy/one-token
mint with a symbolic SIGNED quantity, a 2-entry all-script withdrawal map, empty
cert/signatory/datum/vote/proposal lists.
* DT1: redeemer `DelegateTransfer 0 0 1 1`; ONE redeemer-map entry.
* DS1: redeemer `DelegateSeize 0 0 1 1`; **TWO** redeemer-map entries, the second
  `(Rewarding (ScriptCredential sCred), SeizeAct sIdx [] 0 0 0 0)` with `sCred`
  and `sIdx` FREE.

**Bound 2b — the minting redeemer's index fields are concrete** (`0 0 1 1` in
both). They are self-validating hints re-checked by `pcheckedDrop`/`phead` plus
the branch conditions (Issuance.hs:126-130). NOT concrete, and deliberately so:
the `SeizeAct`'s OWN `plgrDirectoryNodeIdx` (`sIdx`), because the scope-binding
conjunct Issuance.hs:238 is precisely `pdirectoryNodeIdx #== pfromData
nodeRefIdx` and pinning `sIdx = 1` would have made it `rfl`-true.

**DEFECT D1 — NOW ACTUALLY EXERCISED, AND IT PASSES.** SHAPE DS1 carries a
two-entry redeemer map `[Minting …, Rewarding …]`. WSC/Props/Shaped/P4Shaped.lean's
header warns that "a shaped theorem over a 2-entry redeemer map would hit D1 head
on"; that warning is now STALE. CLAB's `ltScriptPurpose` has since been corrected
to the ledger's emitted order `Spending < Minting < Certifying < Rewarding <
Voting < Proposing` (CardanoLedgerApi/V3/Contexts.lean:66-120), so
`validRedeemerMap` accepts the map, `validMintingContext` is satisfiable, and the
SHAPE DS1 vacuity probe is `Falsified` with a concrete accepting witness to match.
Under the pre-fix order this whole shape would have been ledger-UNSATISFIABLE and
every theorem over it silently vacuous — which is why the probe and the witness
matter here and are not a formality.

════════════════════════════════════════════════════════════════════════════
NOT TRUE BY CONSTRUCTION
════════════════════════════════════════════════════════════════════════════
* DT1's conclusion (c) is about the withdrawal map. `w0`, `w1` are free and
  `validMintingContext` constrains them only to be sorted (`validWithdrawals`),
  while the params datum's `glc` is a THIRD free variable. So both "`mlh` is at
  index 0" and "`glc` is at index 1" are earned from the bytecode. The witness
  below fixes them to `MINTLOGIC` and `SGLOBAL`, but the theorem does not.
* DS1's conclusion (c) is about the redeemer map. `sCred` is free and `slc` (the
  params datum's `seizeLogicCred`) is a different free variable, so
  `pdata seizeCred #== pseizeLogicCred` (Issuance.hs:237) is earned; `sIdx` is
  free, so the scope binding (:238) is earned; and the registration node's
  `nCS`/`nTn`/`nQty` are free and different from `dirCS`/`ownCS`, so
  `hasNodeNFT` at the resolved index is earned too.
* In both shapes the params node's value policy `pCS` differs from the script
  parameter `ppCS`, so `pparamsAtRefIdx`'s `phasCSH` gate
  (ProgrammableLogicBase.hs:832) has to be cleared by the accept path — the
  params record the postconditions name is the one the validator actually read at
  `mrParamsRefIdx = 0` (the lesson of the SHAPE G2 falsification,
  WSC/SHAPING-RESULTS.md §6.1).

════════════════════════════════════════════════════════════════════════════
SOURCE FIDELITY (Issuance.hs, wsc-poc worktree `new-session-3c417d`, read
2026-07-25)
════════════════════════════════════════════════════════════════════════════
Arm 2, `PDelegateTransfer` (:200-219). Conjuncts at :216-219:
`mintingLogicInvokedAt # wdrlIdx` (:216, defined :150-151); `regByRefOk` (:217),
defined :207-209 as `hasNodeNFT # pfromData pdirectoryNodeCS` applied to
`ptxInInfoResolved` of the reference input at `nodeRefIdx` — REFERENCE INPUT ONLY,
with the normative F-1 justification in the comment at :204-206; `globalInvoked`
(:218), defined :212-213 as
`(pfstBuiltin # (phead # (pcheckedDrop # pfromData globalWdrlIdx #
withdrawalEntries))) #== pglobalLogicCred`. Ground-truth counterpart:
`DelegateTransferOk` (WSC/Spec.lean:281-285).

Arm 3, `PDelegateSeize` (:221-245). Conjuncts at :242-245: C1 again;
`regByRefOk` (:226-227, identical to arm 2's); `seizeScopeOk` (:229-240) — the
redeemer-map entry at `seizeRedeemerIdx` (`seizeEntry`, :230), its purpose
`punsafeCoerce`d to `PScriptPurpose` and matched against `PRewarding seizeCred`
(:233-234), its redeemer `punsafeCoerce`d to
`PProgrammableLogicGlobalRedeemer` and matched against `PSeizeAct` (:235-236),
then `pdata seizeCred #== pseizeLogicCred` **and**
`pfromData pdirectoryNodeIdx #== pfromData nodeRefIdx` (:237-238). Ground-truth
counterpart: `seizeScopedToNodeOf` / `DelegateSeizeOk` (WSC/Spec.lean:248-296).

E1 CAVEAT (binding on every theorem here): what is proved is a statement about
`cekExecuteProgram … 2500`. A real node budgets in ExUnits, not CEK steps; the
bridge is `LR_BUDGET_minting` in WSC/Honest.lean, which this task does not
discharge.
-/
import WSC.Shaped.MintingDelegateShaped
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxOut TxInInfo validMintingContext ownCurrencySymbol
                          credentialInWithdrawals)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## ARM 2 — `DelegateTransfer` over SHAPE DT1 -/

/-- **P4's disjunct 2 over SHAPE DT1 — PROVED AT UPLC.** `DelegateTransferOk` in
full: the minting-logic script ran, the minted policy's directory NFT is on a
REFERENCE INPUT, and the params datum's `globalLogicCred` is in the withdrawal
map — so the global transfer validator is running on this transaction.

Ground truth only (WSC/Spec.lean:281-285): withdrawal-map membership, reference
inputs' resolved `Value`s, and the params datum's own fields. Validator source:
Issuance.hs:200-219.

MEASURED: `✅ Valid`, ≈1.6 s, budget 2500. -/
theorem P4_delegateTransfer_arm_shaped :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = true := by blaster

/-- **The delegation itself, isolated — PROVED AT UPLC.** The one conjunct that
distinguishes arm 2 from arm 1: the credential the params datum publishes as
`globalLogicCred` is in this transaction's withdrawal map. With
`LR_WDRL_RUNS_VALIDATOR` (WSC/Honest.lean) that is what makes the global transfer
validator unavoidable on every shape-DT1 mint. MEASURED: `✅ Valid`. -/
theorem P4_delegateTransfer_globalRuns_shaped :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      credentialInWithdrawals (Credential.ScriptCredential glc)
        (localShapedWdrl w0 w1 a0 a1) := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE DT1 — PROVED AT UPLC.**

HONESTY NOTE — WHAT THIS DOES *NOT* SAY (identical in force to the one in
WSC/Props/Shaped/P4LocalShaped.lean). The disjunction is proved SHAPE BY SHAPE,
because the shape fixes the redeemer's constructor tag and the tag selects the
arm. All four arms are now covered — L1, DT1, DS1, M1/M2 — but by four separate
theorems over four separate (and pairwise disjoint) shape classes, NOT by one
theorem over a symbolic redeemer. Making the tag symbolic is what re-introduces
the branch structure that shaping removes; that is the shape-coverage gap of
WSC/SHAPING-RESULTS.md §7 and it is NOT closed here.

MEASURED: `✅ Valid`. -/
theorem P4_disjunction_at_DT1 :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || BurnOnlyOk mlh ownCS
         (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) = true := by blaster

/-- Negative control for arm 2: a shape-DT1 context that fails
`DelegateTransferOk` is rejected by the real bytecode. MEASURED: `✅ Valid`.
(E9: also satisfied by budget-`Error`, hence the vacuity probe and witness.) -/
theorem P4_delegateTransfer_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ (DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = true) →
    isUnsuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := by blaster

/-- Tightness for arm 2: expected and MEASURED `Falsified`. -/
def P4_delegateTransfer_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ (DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = true)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateTransfer_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE DT1.** Expected and MEASURED:
`✅ Falsified` — accepting shape-DT1 contexts exist inside 2500 CEK steps. -/
def P4_delegateTransfer_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validMintingContext
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateTransfer_vacuity_probe]

/-! ## ARM 3 — `DelegateSeize` over SHAPE DS1 -/

/-- **P4's disjunct 3 over SHAPE DS1 — PROVED AT UPLC.** `DelegateSeizeOk` in
full: the minting-logic script ran, the minted policy's directory NFT is on a
reference input, and some redeemer of the transaction is a `SeizeAct` for the
params datum's `seizeLogicCred` whose OWN `directoryNodeIdx` resolves to a
reference input carrying that policy's directory NFT.

The last conjunct is the SCOPE BINDING, and it is genuinely earned: the
`SeizeAct`'s node index `sIdx` is a free variable in SHAPE DS1 (see the module
header's Bound 2b), so the bytecode has to force it to agree with the index the
NFT check used. Ground truth: `seizeScopedToNodeOf` (WSC/Spec.lean:248-260).
Validator source: Issuance.hs:229-240.

MEASURED: `✅ Valid`, budget 2500. -/
theorem P4_delegateSeize_arm_shaped :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
      DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) = true
      := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE DS1 — PROVED AT UPLC.** Same
honesty note as `P4_disjunction_at_DT1`. MEASURED: `✅ Valid`. -/
theorem P4_disjunction_at_DS1 :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)
       || BurnOnlyOk mlh ownCS
         (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)) = true
      := by blaster

/-- Negative control for arm 3. MEASURED: `✅ Valid`. -/
theorem P4_delegateSeize_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    ¬ (DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) = true) →
    isUnsuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) := by blaster

/-- Tightness for arm 3: expected and MEASURED `Falsified`. -/
def P4_delegateSeize_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    ¬ (DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) = true)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateSeize_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE DS1** — and, uniquely in this tree, also a
live test of the D1 fix (see the module header): under CLAB's OLD `ScriptPurpose`
order a two-entry `[Minting, Rewarding]` redeemer map was unsorted, hence
`validMintingContext` unsatisfiable, hence this probe would have been `Valid`
(= genuinely vacuous) and every DS1 theorem empty.

Expected and MEASURED: `✅ Falsified`. -/
def P4_delegateSeize_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (sCred : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) →
    ¬ isSuccessful
      (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateSeize_vacuity_probe]

/-! ## CONCRETE accepting witnesses of EXACTLY SHAPE DT1 and SHAPE DS1

Executable, no SMT: the real CEK machine on the shaped applied terms, closed by
`native_decide`. Both witnesses mint **+3** of `OWNCS.TOK` (strictly positive) and
carry the `DIRCS.OWNCS` directory NFT on reference input 1. -/

namespace P4DelegateShapedWitness

set_option maxRecDepth 1000000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-! ### SHAPE DT1 witness — the delegation to the global transfer validator

Withdrawal 1's credential IS the params datum's `globalLogicCred` (`SGLOBAL`), and
the map is still sorted (`MINTLOGIC < SGLOBAL`) — so the arm's `globalInvoked`
conjunct is met by a genuinely sorted, ledger-legal withdrawal map. -/

def ctxDT : ScriptContext :=
  dtShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "SGLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "SGLOBAL") 0 0
    50

theorem ctxDT_valid : validMintingContext ctxDT = true := by native_decide

theorem ctxDT_mints_positive :
    mintPos ownCS ctxDT.scriptContextTxInfo.txInfoMint = true := by native_decide

theorem ctxDT_post :
    DelegateTransferOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "SGLOBAL") (ByteString.mk "SEIZE")) ownCS ctxDT = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE (SHAPE DT1).** -/
theorem ctxDT_exec_accepts_at_2500 :
    isSuccessful
      (appliedMintDTShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "SGLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") (ByteString.mk "SGLOBAL") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1257`, to the step**, and **1257 is EXACTLY the
measured step count of the off-chain golden
`programmableTokenMinting.mint-delegate-transfer-topup`**
(WSC/goldens/K-MEASUREMENTS.md §3). SHAPE DT1 therefore reproduces the real
production `DelegateTransfer` transaction's cost exactly — the third such match in
the tree, after SHAPE M1's 784 and SHAPE L1's 1681. -/
theorem ctxDT_K_is_1257 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDT) 1257) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDT) 1256) = false := by native_decide

/-! ### SHAPE DS1 witness — the seize-scope binding, with a 2-entry redeemer map

The `Rewarding` redeemer entry carries `SeizeAct 1 [] 0 0 0 0` and its credential
IS the params datum's `seizeLogicCred` (`SEIZE`); `sIdx = 1` agrees with the
minting redeemer's `mrNodeRefIdx = 1`, which is the reference input holding the
`DIRCS.OWNCS` directory NFT. Because `sIdx` is a FREE leaf of the shape, this
witness is an *instance* of the scope binding, not a definition of it. -/

def ctxDS : ScriptContext :=
  dsShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
    (ByteString.mk "SEIZE") 1
    50

/-- **The D1 fix, demonstrated executably.** This context's redeemer map has TWO
entries, `[Minting "OWNCS", Rewarding (ScriptCredential "SEIZE")]`, and it
satisfies `validMintingContext` — i.e. `validRedeemerMap` accepts it under CLAB's
corrected `ScriptPurpose` order. Under the pre-fix order it would have been
rejected and every SHAPE DS1 theorem would have been vacuous. -/
theorem ctxDS_valid : validMintingContext ctxDS = true := by native_decide

theorem ctxDS_mints_positive :
    mintPos ownCS ctxDS.scriptContextTxInfo.txInfoMint = true := by native_decide

theorem ctxDS_post :
    DelegateSeizeOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")) ownCS ctxDS = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE (SHAPE DS1).** -/
theorem ctxDS_exec_accepts_at_2500 :
    isSuccessful
      (appliedMintDSShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
        (ByteString.mk "SEIZE") 1
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1466`.** No `DelegateSeize` golden exists in
WSC/goldens (K-MEASUREMENTS §3 lists 784 / 1257 / 1681 for burn / delegate-transfer
/ local), so unlike the other three shapes this K has no off-chain counterpart to
match. It sits between the delegate-transfer and local costs, which is what the
arm's structure predicts: one extra redeemer-map walk, no output scan. -/
theorem ctxDS_K_is_1466 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDS) 1466) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDS) 1465) = false := by native_decide

end P4DelegateShapedWitness

end WSC
