/-
WSC/Props/Shaped/P4DelegateShapedR.lean — **P4's two DELEGATING custody arms,
re-proved over the NODE-REALIZABLE SHAPES DT1R and DS1R** (task C2).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED FROM `WSC/Props/Shaped/P4DelegateShaped.lean`
════════════════════════════════════════════════════════════════════════════
Only the redeemer map, and in DS1R also which credential carries the `SeizeAct`:

* **DT1 → DT1R**: 1 redeemer entry → **3** (`Minting ownCS`, then one `Rewarding`
  per script withdrawal). The withdrawal map is unchanged — the
  `DelegateTransfer` arm genuinely needs BOTH entries to be script credentials
  (Issuance.hs:216 and :210-211), so this shape could not shrink the way M1R/L1R
  did.
* **DS1 → DS1R**: 2 redeemer entries → **3**, and the seize credential is no
  longer the free-floating `sCred` but **`w1`, the transaction's second
  withdrawal**. SHAPE DS1's `sCred` was a `Rewarding` REDEEMER entry with no
  matching withdrawal, which is exactly what
  `ShapeRealizability.ds1_uncovered_wdrl_exists` shows leaves DS1 short of
  coverage. `mrSeizeRedeemerIdx` moves 1 → 2 to name the new position.

Everything else is identical: same flat, same budget 2500, same postconditions
(`DelegateTransferOk` / `DelegateSeizeOk` from `WSC/Spec.lean`, ground truth), same
reference inputs, outputs, input, mint and withdrawal maps.

**`sIdx` IS STILL FREE.** The `SeizeAct`'s own `plgrDirectoryNodeIdx` is a
universally quantified leaf of SHAPE DS1R, so `seizeScopedToNodeOf`'s binding of
the seize's scope to `ownCS`'s directory node is EARNED from the bytecode and not
`rfl`-true. That was the design requirement of SHAPE DS1 and the re-cut preserves
it exactly.

════════════════════════════════════════════════════════════════════════════
SCOPE
════════════════════════════════════════════════════════════════════════════
Budget 2500 (ADDENDUM E1, `LR_BUDGET_minting`); SHAPES DT1R / DS1R as published in
`WSC/Shaped/MintingDelegateShapedR.lean`; one arm per shape (the redeemer tag
selects it). Realizability is CLAB-level — see `WSC/Realizability.lean`'s
`Realizable` docstring for what is still not modelled.

**WHAT THESE ARMS DO *NOT* GIVE YOU** (unchanged from the DT1/DS1 module):
`DelegateTransferOk` proves the global transfer validator RUNS; `DelegateSeizeOk`
proves a `SeizeAct` for the params seize credential is scoped to this policy's
node. Neither says what those validators then enforce — that is P1 and P2. The
`Local` arm (`WSC/Props/Shaped/P4LocalShapedR.lean`) is where the no-escape
guarantee is a theorem about the issuance policy itself.
-/
import WSC.Shaped.MintingDelegateShapedR
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

/-! ## ARM 2 — `DelegateTransfer` over SHAPE DT1R -/

/-- **P4's disjunct 2 over SHAPE DT1R — PROVED AT UPLC, over a REALIZABLE class.**
`DelegateTransferOk` in full: the minting-logic script ran, the minted policy's
directory NFT is on a REFERENCE INPUT, and the params datum's `globalLogicCred` is
in the withdrawal map. Ground truth only (WSC/Spec.lean). Validator source:
Issuance.hs:200-219. -/
theorem P4_delegateTransfer_arm_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    isSuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
      DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) = true
      := by blaster

/-- **The delegation itself, isolated — PROVED AT UPLC.** The credential the params
datum publishes as `globalLogicCred` is in this transaction's withdrawal map. With
`LR_WDRL_RUNS_VALIDATOR` that makes the global transfer validator unavoidable on
every shape-DT1R mint. -/
theorem P4_delegateTransfer_globalRuns_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    isSuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
      credentialInWithdrawals (Credential.ScriptCredential glc)
        (delegateRWdrl w0 w1 a0 a1) := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE DT1R — PROVED AT UPLC.** -/
theorem P4_disjunction_at_DT1R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    isSuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)
       || BurnOnlyOk mlh ownCS
         (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)) = true
      := by blaster

/-- Negative control for arm 2 at SHAPE DT1R. -/
theorem P4_delegateTransfer_R_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential glc)
        (delegateRWdrl w0 w1 a0 a1) →
    isUnsuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) := by blaster

/-- Tightness stanza at SHAPE DT1R. Expected: `Falsified`. -/
def P4_delegateTransfer_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    isSuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    ¬ credentialInWithdrawals (Credential.ScriptCredential glc)
        (delegateRWdrl w0 w1 a0 a1)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateTransfer_R_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND SHAPE DT1R.** -/
def P4_delegateTransfer_R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed glRed : ByteString)
    (fee : Integer),
    validMintingContext
      (dtRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee) →
    ¬ isSuccessful
      (appliedMintDTRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed glRed fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateTransfer_R_vacuity_probe]

/-! ## ARM 3 — `DelegateSeize` over SHAPE DS1R -/

/-- **P4's disjunct 3 over SHAPE DS1R — PROVED AT UPLC, over a REALIZABLE class.**
`DelegateSeizeOk`: the minting-logic script ran, the minted policy is registered by
REFERENCE INPUT, and a `SeizeAct` redeemer for the params seize credential is
SCOPED to this policy's directory node.

The last conjunct is the scope binding and it is genuinely earned: `sIdx`, the
`SeizeAct`'s node index, is a FREE leaf of SHAPE DS1R, and `w1`, the credential
carrying that redeemer, is a different free variable from the params datum's `slc`.
Ground truth: `seizeScopedToNodeOf` (WSC/Spec.lean). Validator source:
Issuance.hs:229-240. -/
theorem P4_delegateSeize_arm_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    isSuccessful
      (appliedMintDSRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
      DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) = true
      := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE DS1R — PROVED AT UPLC.** -/
theorem P4_disjunction_at_DS1R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    isSuccessful
      (appliedMintDSRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)
       || BurnOnlyOk mlh ownCS
         (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)) = true
      := by blaster

/-- Negative control for arm 3 at SHAPE DS1R: if no redeemer entry scopes a
`SeizeAct` for the params seize credential to this policy's node, the bytecode
rejects. -/
theorem P4_delegateSeize_R_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    ¬ (DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) = true) →
    isUnsuccessful
      (appliedMintDSRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) := by blaster

/-- Tightness stanza at SHAPE DS1R. Expected: `Falsified`. -/
def P4_delegateSeize_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    isSuccessful
      (appliedMintDSRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    ¬ (DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) = true)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateSeize_R_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND SHAPE DS1R.** Load-bearing twice
over: the redeemer map grew AND `mrSeizeRedeemerIdx` moved from 1 to 2, either of
which could have emptied the accept set. -/
def P4_delegateSeize_R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer) (mlRed : ByteString) (sIdx : Integer)
    (fee : Integer),
    validMintingContext
      (dsRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee) →
    ¬ isSuccessful
      (appliedMintDSRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 mlRed sIdx fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_delegateSeize_R_vacuity_probe]

/-! ## CONCRETE accepting witnesses of EXACTLY SHAPES DT1R and DS1R, and their
REALIZABILITY -/

namespace DelegateRWitness

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

/-! ### SHAPE DT1R witness -/

def ctxDT : ScriptContext :=
  dtRCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
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
    (ByteString.mk "MLRED") (ByteString.mk "GLRED")
    50

theorem ctxDT_valid : validMintingContext ctxDT = true := by native_decide

theorem ctxDT_covered : Realizability.redeemerCovered ctxDT = true := by native_decide

/-- **REALIZABILITY OF SHAPE DT1R.** The `w0 ≠ w1` side condition of
`dtR_wdrl_covered` is discharged by `decide` at the witness; on the class it is
supplied by `validWithdrawals`. -/
theorem ctxDT_realizable : Realizability.Realizable ctxDT := by
  refine ⟨by native_decide, ctxDT_covered, ?_, ?_, ?_⟩
  · apply dtR_wdrl_covered; decide
  · apply dtR_spend_covered
  · apply dtR_mint_covered

theorem ctxDT_mints_positive :
    mintPos ownCS ctxDT.scriptContextTxInfo.txInfoMint = true := by native_decide

theorem ctxDT_post :
    DelegateTransferOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "SGLOBAL") (ByteString.mk "SEIZE")) ownCS ctxDT = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE (SHAPE DT1R).** -/
theorem ctxDT_exec_accepts_at_2500 :
    isSuccessful
      (appliedMintDTRShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
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
        (ByteString.mk "MLRED") (ByteString.mk "GLRED")
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT (SHAPE DT1R) — `K = 1257`**, identical to SHAPE DT1's
witness and to the `mint-delegate-transfer-topup` golden's measured K. The
`DelegateTransfer` arm never walks the redeemer map, so growing it 1 → 3 entries
costs nothing. -/
theorem ctxDT_K_is_1257 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDT) 1257) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDT) 1256) = false := by native_decide

/-! ### SHAPE DS1R witness — the seize-scope binding over a COVERED redeemer map

Withdrawal 1's credential is `SEIZE`, which IS the params datum's `seizeLogicCred`,
and the redeemer entry at index 2 — the one `mrSeizeRedeemerIdx = 2` names — is
that credential's own `SeizeAct 1 [] 0 0 0 0`. `sIdx = 1` agrees with the minting
redeemer's `mrNodeRefIdx = 1`, the reference input holding the `DIRCS.OWNCS`
directory NFT. Because `sIdx` is a FREE leaf, this witness is an INSTANCE of the
scope binding, not a definition of it. -/

def ctxDS : ScriptContext :=
  dsRCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "SEIZE") 0 0
    (ByteString.mk "MLRED") 1
    50

theorem ctxDS_valid : validMintingContext ctxDS = true := by native_decide

theorem ctxDS_covered : Realizability.redeemerCovered ctxDS = true := by native_decide

/-- **REALIZABILITY OF SHAPE DS1R.** -/
theorem ctxDS_realizable : Realizability.Realizable ctxDS := by
  refine ⟨by native_decide, ctxDS_covered, ?_, ?_, ?_⟩
  · apply dsR_wdrl_covered; decide
  · apply dsR_spend_covered
  · apply dsR_mint_covered

theorem ctxDS_mints_positive :
    mintPos ownCS ctxDS.scriptContextTxInfo.txInfoMint = true := by native_decide

theorem ctxDS_post :
    DelegateSeizeOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")) ownCS ctxDS = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE (SHAPE DS1R).** -/
theorem ctxDS_exec_accepts_at_2500 :
    isSuccessful
      (appliedMintDSRShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") (ByteString.mk "SEIZE") 0 0
        (ByteString.mk "MLRED") 1
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT (SHAPE DS1R) — `K = 1466`**, identical to SHAPE DS1's
witness. Measured by search in `WSC/Shaped/Probe/DSRK.lean` and pinned here. Two
changes could have moved it and neither did: the redeemer map grew from 2 entries
to 3, and `mrSeizeRedeemerIdx` moved 1 → 2 so `pcheckedDrop` walks one entry
further. The first is free because the context reaches the machine as ONE constant
term (`CardanoLedgerApi/V3/Contexts.lean:723-726`); the second is free because
`pdropFast` dispatches on the index rather than stepping per element. -/
theorem ctxDS_K_is_1466 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDS) 1466) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctxDS) 1465) = false := by native_decide

end DelegateRWitness

end WSC
