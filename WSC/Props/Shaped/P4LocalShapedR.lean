/-
WSC/Props/Shaped/P4LocalShapedR.lean — **P4's `Local` custody arm, re-proved over
the NODE-REALIZABLE SHAPE L1R** (task C2).

════════════════════════════════════════════════════════════════════════════
WHAT CHANGED FROM `WSC/Props/Shaped/P4LocalShaped.lean`
════════════════════════════════════════════════════════════════════════════
Only the shape, and only in its withdrawal/redeemer maps: 2 script withdrawals + 1
redeemer entry (an EMPTY class of ledger transactions —
`ShapeRealizability.l1_class_is_empty_under_coverage`) becomes 1 script withdrawal
+ 2 redeemer entries (`mint-local-registered-by-ref`'s own shape, redeemer-covered
by construction — `WSC.localR_{wdrl,spend,mint}_covered`). Same flat, same budget
2500, same postconditions, same ground-truth vocabulary, same two-output no-escape
scan.

THE HEADLINE IS UNCHANGED AND NOW COMPOSABLE-IN-PRINCIPLE: *if the real compiled
issuance policy accepts a `Local`-arm transaction of shape L1R, then EVERY output
whose payment credential is not the mini-ledger base credential holds ZERO of the
minted policy* — and shape L1R is a non-empty class.

════════════════════════════════════════════════════════════════════════════
SCOPE — every bound of `P4LocalShaped.lean` still binds
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 2500**, bridged by `LR_BUDGET_minting`. The witness
below measures `K = 1681`, EXACTLY the `mint-local-registered-by-ref` golden's
measured step count and exactly SHAPE L1's witness K — so the re-cut is
cost-neutral and still reproduces the production transaction to the step.

**Bound 2 — SHAPE L1R**, published in `WSC/Shaped/MintingLocalShapedR.lean`.

**Bound 2a — the arm** is fixed by the redeemer tag (0 = `Local`).

**Bound 2b — ONE OUTPUT COUNT AT A TIME, and TWO is required.** SHAPE L1R keeps
exactly two outputs. This is not inherited decoration: with ONE output the ledger
balance rule forces that output to carry `ownCS`, the per-output disjunction
collapses to a credential comparison, and the `¬hasCS` branch is never taken. At
two, output 1 (ada-only) discharges through the value branch and output 0 through
the credential branch. A statement for all output counts needs an induction the
shaped layer cannot express (`WSC/SHAPING-RESULTS.md` §7) and is NOT closed here.

**Bound 2c — the index fields stay concrete AT SHAPE L1R.**
`mrMintingLogicWdrlIdx = 0`, `mrParamsRefIdx = 0`, registration index `= 1`. The
registration index is LOOSENED in the SHAPE L2R rung at the foot of this module,
which supersedes the SHAPE L1R no-escape theorem in strength; the other two index
fields stay concrete everywhere here.

**Bound 3 — realizability is CLAB-level, not node-level.** See
`WSC/Realizability.lean`'s `Realizable` docstring for the list of what CLAB still
does not model. The claim is narrow and exact: the ONE defect audit F2 named is
gone.

════════════════════════════════════════════════════════════════════════════
THE SHAPE L2 RUNG IS NOW RE-CUT TOO (audit finding **F19**)
════════════════════════════════════════════════════════════════════════════
SHAPE L2 (`WSC/Shaped/MintingLocalShapedIdx.lean`, the free-registration-index
rung) carries `P4_local_noEscape_shapedIdx` over a class
`ShapeRealizability.l1_class_is_empty_under_coverage` proves EMPTY, which is why
`WSC/README.md` and `WSC/STATUS.md` say it must not be quoted. **SHAPE L2R**
(`WSC/Shaped/MintingLocalShapedRIdx.lean`) is that rung over the realizable cut,
and the stanzas at the foot of this module give it the full four-item bar:
`P4_local_noEscape_RIdx` (the theorem), `P4_local_RIdx_vacuity_probe` (its own
probe at its own prep term and shape), `L2RWitness.exec_accepts_at_2500` +
`L2RWitness.K_is_1681` (a concrete accepting CEK run, `K` pinned two-sided), and
`L2RWitness.ctx_realizable` on top of the class-level
`localRIdx_{wdrl,spend,mint}_covered`.

`P4_local_noEscape_shapedIdx` is superseded and should be cited only as the
historical measurement. **Quote `P4_local_noEscape_RIdx` instead.**

What remains NOT re-cut is the L2 REGISTRATION conjunct, which was
`⚠️ Undetermined` at SHAPE L2 after a 300 s Z3 cap (`WSC/Shaped/Probe/L2Reg.lean`)
and is not attempted at SHAPE L2R either — the split measurement (`noEscape`
index-independent, registration index-DEPENDENT) is the rung's whole content and
it is preserved.

════════════════════════════════════════════════════════════════════════════
SOURCE FIDELITY
════════════════════════════════════════════════════════════════════════════
Unchanged from `WSC/Props/Shaped/P4LocalShaped.lean`'s stanza (same flat, same
mirrors, same three conjuncts at Issuance.hs:194-198, :150-151/:136, :172-173,
:179-193). The re-cut touches no field any of the three reads except the
withdrawal map C1 indexes, which is still a free script credential.
-/
import WSC.Shaped.MintingLocalShapedR
import WSC.Shaped.MintingLocalShapedRIdx
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

/-! ## The headline obligation — the policy's own no-escape scan -/

/-- **P4-Local's no-escape scan over SHAPE L1R — PROVED AT UPLC, over a
REALIZABLE class.** Ground truth (`WSC/Spec.lean`'s `noEscape`): output addresses,
output `Value`s, the params datum's `progLogicCred`, the minted currency symbol.
Validator source: Issuance.hs:179-193 + :197. -/
theorem P4_local_noEscape_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
      noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true := by blaster

/-! ## The other two conjuncts of the arm -/

/-- **C1 over SHAPE L1R — PROVED AT UPLC.** An accepted shape-L1R `Local` mint runs
the token's minting-logic script. At this shape the withdrawal map is the SINGLETON
`[(ScriptCredential w0, a0)]` with `w0` free, so the conclusion is the equality
`w0 = mlh` and `validWithdrawals` (vacuous on a singleton) contributes nothing. -/
theorem P4a_local_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (localRWdrl w0 a0) := by blaster

/-- **Registration over SHAPE L1R — PROVED AT UPLC.** Ground truth
`anyRefInputHasNodeNFT` (WSC/Spec.lean), the index-free consequence of
Issuance.hs:172-173. -/
theorem P4_local_registration_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
      anyRefInputHasNodeNFT dirCS ownCS
        [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
        , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] = true := by blaster

/-! ## The arm predicate, and P4's four-way disjunction -/

/-- **P4's disjunct 1 over SHAPE L1R — PROVED AT UPLC.** `WSC/Spec.lean`'s
`LocalCustodyOk` for the params record the validator itself read at reference
index 0, as one blaster obligation. -/
theorem P4_local_arm_R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
      LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) = true := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE L1R — PROVED AT UPLC.**
`ARCHITECTURE §3-P4` verbatim. As at SHAPE L1 the disjunction is proved SHAPE BY
SHAPE (the redeemer tag selects the arm), so this is disjunct 1 being satisfied,
stated as the disjunction. The re-cut coverage of the four arms:

| arm | re-cut shape | where | witness K |
|---|---|---|---|
| 1 `Local` | **L1R** | this module | 1681 |
| 2 `DelegateTransfer` | **DT1R** | WSC/Props/Shaped/P4DelegateShapedR.lean | 1257 |
| 3 `DelegateSeize` | **DS1R** | WSC/Props/Shaped/P4DelegateShapedR.lean | 1466 |
| 4 `BurnOnly` | **M1R** | WSC/Props/Shaped/P4ShapedR.lean | 784 |
-/
theorem P4_disjunction_at_L1R :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)
       || BurnOnlyOk mlh ownCS
         (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)) = true := by blaster

/-! ## Polarity controls (ADDENDUM E9) — the full four-stanza set at SHAPE L1R -/

/-- Negative control (≡ the contrapositive of the no-escape theorem over SHAPE
L1R). -/
theorem P4_local_R_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true) →
    isUnsuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) := by blaster

/-- Tightness stanza at SHAPE L1R. Expected: `Falsified`. -/
def P4_local_R_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true)

#blaster (gen-cex: 0) (solve-result: 1) [P4_local_R_tightness]

/-- **MANDATORY VACUITY PROBE AT THE NEW TERM AND THE NEW SHAPE.** "No accepting
shape-L1R context exists within 2500 CEK steps" must be FALSIFIED. This probe is
load-bearing for the re-cut: shrinking the withdrawal map to one entry is exactly
the kind of change that can empty an accept set, and it is what would have caught a
PUBKEY entry at index 0. -/
def P4_local_R_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer),
    validMintingContext
      (localRCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee) →
    ¬ isSuccessful
      (appliedMintLocalRShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_local_R_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE L1R, and its REALIZABILITY

Leaf values are SHAPE L1's witness verbatim except for the withdrawal/redeemer
maps: the policy `OWNCS` mints **+3** of `OWNCS.TOK` (strictly positive — token
CREATION, which is what the no-escape scan is about); the input holds 2; output 0
sits at `ScriptCredential "PROGLOGIC"` (the params datum's `progLogicCred`) and
holds all 5; output 1 sits at `ScriptCredential "OTHER"`, outside the mini-ledger,
ada-only. 200 lovelace in, 100 + 50 out, 50 fee. Reference input 1 carries exactly
one `DIRCS.OWNCS` token — the directory NFT named after the minted policy.
Withdrawals `[(ScriptCredential "MINTLOGIC", 0)]`; redeemers
`[(Minting "OWNCS", Local 0 0 (RegisteredByReferenceInput 1)),
  (Rewarding (ScriptCredential "MINTLOGIC"), B "MLRED")]`. -/

namespace L1RWitness

set_option maxRecDepth 1000000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"

/-- The witness context: SHAPE L1R at the leaf values above. -/
def ctx : ScriptContext :=
  localRCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis IN FULL. -/
theorem ctx_valid : validMintingContext ctx = true := by native_decide

/-- **AND the `MissingRedeemers` row CLAB is missing** — the conjunct
`WSC.P4LocalShapedWitness.ctx` cannot satisfy. -/
theorem ctx_covered : Realizability.redeemerCovered ctx = true := by native_decide

/-- **REALIZABILITY OF SHAPE L1R — the acceptance criterion.** -/
theorem ctx_realizable : Realizability.Realizable ctx := by
  refine ⟨by native_decide, ctx_covered, ?_, ?_, ?_⟩
  · apply localR_wdrl_covered
  · apply localR_spend_covered
  · apply localR_mint_covered

/-- The witness genuinely mints a STRICTLY POSITIVE quantity of its own policy. -/
theorem ctx_mints_positive : mintPos ownCS ctx.scriptContextTxInfo.txInfoMint = true := by
  native_decide

/-- The witness satisfies the full arm-1 predicate `LocalCustodyOk`. -/
theorem ctx_post_localCustody :
    LocalCustodyOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")) ownCS ctx = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-L1R
context at budget 2500, through the SHAPED applied term the theorems quantify
over. -/
theorem exec_accepts_at_2500 :
    isSuccessful
      (appliedMintLocalRShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1681`, to the step**, i.e. IDENTICAL to SHAPE L1's
witness and to the `mint-local-registered-by-ref` golden's measured K. The re-cut
is cost-neutral: shrinking the withdrawal map and growing the redeemer map changes
no CEK step, because the redeemer map is not walked on this arm and the context is
handed to the machine as ONE constant term
(`CardanoLedgerApi/V3/Contexts.lean:717-720`). -/
theorem K_is_1681 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1681) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1680) = false := by native_decide

/-! ### EXCLUDED-CASE WITNESS — the escaping output is real, REALIZABLE, and rejected

The only change from `ctx` is output 0's payment-credential hash: `EVIL` instead of
`PROGLOGIC`, so the minted tokens sit outside the mini-ledger. Nothing about the
balance, the value canonicity, the registration NFT, the withdrawal map or the
REDEEMER COVERAGE changes — so this is a transaction a real attacker could actually
build, which is more than could be said of SHAPE L1's version of this control. -/

def ctxEscape : ScriptContext :=
  localRCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "EVIL") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
    50

/-- The escaping context IS ledger-valid, IS redeemer-covered, DOES mint a positive
quantity, and genuinely VIOLATES the no-escape postcondition. -/
theorem ctxEscape_valid_and_escaping :
    validMintingContext ctxEscape = true ∧
    Realizability.redeemerCovered ctxEscape = true ∧
    mintPos ownCS ctxEscape.scriptContextTxInfo.txInfoMint = true ∧
    noEscape (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")) ownCS
      ctxEscape.scriptContextTxInfo.txInfoOutputs = false := by native_decide

/-- …and the REAL compiled bytecode REJECTS it at budget 2500. -/
theorem exec_rejects_escaping_output :
    isHaltB
      (appliedMintLocalRShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "EVIL") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
        50) = false := by native_decide

end L1RWitness

/-! ════════════════════════════════════════════════════════════════════════
## SHAPE L2R — the LOOSENING RUNG, re-cut over the realizable class (**F19**)
════════════════════════════════════════════════════════════════════════════

SHAPE L2R (`WSC/Shaped/MintingLocalShapedRIdx.lean`) is SHAPE L1R with the `Local`
arm's REGISTRATION reference-input index a free `Integer` leaf instead of the
constant 1, so the theorem below SUPERSEDES `P4_local_noEscape_R` in strength — the
shape class is strictly larger, and `localRCtxIdx_at_one` proves the containment
DEFINITIONALLY (`regIdx = 1` gives back `localRCtx` as the same term).

Everything else is byte-for-byte SHAPE L1R: the same single script withdrawal (the
C1 floor, Issuance.hs:150-151), the same two-entry redeemer map covering every
script witness, the same TWO reference inputs, the same TWO outputs, all values
symbolic. The coverage facts are unchanged and re-proved at every leaf assignment
(`localRIdx_{wdrl,spend,mint}_covered`), because the loosened index lives in the
redeemer PAYLOAD and not in the map's KEYS.

Same flat, same imported program object, same budget 2500, same ground-truth
postcondition (`WSC/Spec.lean`'s `noEscape`), same non-degeneracy: two outputs,
both disjuncts of the per-output condition (Issuance.hs:189-192) live.

════════════════════════════════════════════════════════════════════════════
HOW THE HEADLINE IS DISCHARGED HERE — and the measurement that forced it
════════════════════════════════════════════════════════════════════════════
The obvious route, `noEscape` as a direct `blaster` goal, is **`⚠️ Undetermined`
at SHAPE L2R**: measured in `WSC/Shaped/Probe/L2RProbe.lean` at a **300 s Z3 cap**,
module wall **303 s**. That is a SOLVER LIMIT and not an empty class, and the probe
says so on its own evidence: `L2R_vacuity` at the same term and shape is
**`✅ Falsified`**, i.e. accepting shape-L2R contexts exist within 2500 CEK steps.

Compare SHAPE L2, where the same goal closes in 2.2 s. The blow-up is the
COMPOUNDING of the two loosenings — SHAPE L2 has a ONE-entry redeemer map with a
symbolic index; SHAPE L1R has a TWO-entry redeemer map with a concrete index;
SHAPE L2R has both, and the extra `Rewarding` entry (symbolic `w0`, `mlRed`) sits
inside the same `Data` blob the symbolic `pcheckedDrop` must be reasoned about
against.

**The route that does close is the NEGATIVE CONTROL, which is `✅ Valid`** at the
same 300 s cap (`L2RProbe.L2R_negative_control`). That is not a weaker statement:
`isUnsuccessful = isErrorState` and `isSuccessful = isHaltState` are predicates on
DISJOINT constructors of `PlutusCore.UPLC.CekMachine.State`
(`PlutusCore/UPLC/Utils.lean:24-36`), so

    (¬post → run ERRORS)   ⟹   (run HALTS → post)

and the converse fails — a budget-exhausted run is neither. The negative control is
therefore STRICTLY STRONGER than the headline, and `P4_local_noEscape_RIdx` below is
derived from it by `halt_not_error` with **no further solver call**. The headline
statement, its class, its budget and its ground-truth vocabulary are all exactly what
a direct proof would have given.

WHAT IS *NOT* CLOSED AT SHAPE L2R: the **C1** conjunct (`credentialInWithdrawals`),
`⚠️ Undetermined` at the 300 s cap (`L2RProbe.L2R_C1`). It is NOT stated as a theorem
here. C1 at the concrete-index shape L1R is `P4a_local_R` above, which is unaffected. -/

/-- A `Halt` state is not an `Error` state — `isHaltState` and `isErrorState` are
`True` on disjoint constructors (`PlutusCore/UPLC/Utils.lean:24-36`). This is the
only bridge the derivation below needs, and it is pure Lean: no solver, no axiom. -/
theorem halt_not_error (s : PlutusCore.UPLC.CekMachine.State) :
    isSuccessful s → isUnsuccessful s → False := by
  cases s <;> simp [isSuccessful, isUnsuccessful,
    PlutusCore.UPLC.Utils.isHaltState, PlutusCore.UPLC.Utils.isErrorState]

/-- **Negative control at SHAPE L2R — PROVED AT UPLC, `✅ Valid` at a 300 s Z3 cap.**
A shape-L2R context in which some output outside the mini-ledger base credential
holds the minted policy is REJECTED — the run ERRORS — whatever reference-input
index the registration witness names.

This is the LOAD-BEARING result of the rung: `P4_local_noEscape_RIdx` is derived
from it. The index ranges over `1` (the directory node, the accepting value), `0`
(the params reference input, which carries no `DIRCS.OWNCS` NFT), every
out-of-range value (`phead` on the emptied list errors) and every NEGATIVE value,
which `pcheckedDrop` REJECTS EXPLICITLY rather than clamping (Issuance.hs:126-130 —
the comment at `:128-129` records that `pdropList` would otherwise treat a negative
count as zero).

Ground truth: `WSC/Spec.lean`'s `noEscape`. Validator source: Issuance.hs:183-193
+ `:197`. -/
theorem P4_local_RIdx_negative_control :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true) →
    isUnsuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) := by
  blaster (timeout: 300)

/-- **P4-Local's no-escape scan over SHAPE L2R — REGISTRATION INDEX SYMBOLIC, over a
REALIZABLE class. THE F19 HEADLINE.**

*If the real compiled issuance policy accepts a `Local`-arm transaction of shape
L2R, then every output whose payment credential is not the mini-ledger base
credential holds ZERO of the minted policy* — whatever reference-input index the
registration witness names.

This SUPERSEDES `P4_local_noEscape_R` in strength (SHAPE L2R strictly contains
SHAPE L1R — `localRCtxIdx_at_one`) and it is the replacement for
`P4_local_noEscape_shapedIdx`, whose SHAPE L2 class is PROVED EMPTY
(`ShapeRealizability.l1_class_is_empty_under_coverage`). **Cite this one.**

Discharged from `P4_local_RIdx_negative_control` — which the solver proved `Valid`
against the real bytecode — by `halt_not_error` alone. No solver call of its own;
see the module header for why the direct route is `⚠️ Undetermined` and why this
one loses nothing. -/
theorem P4_local_noEscape_RIdx :
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
      noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true := by
  intro ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
    pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
    key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee hvalid hsucc
  cases hb : noEscape (Credential.ScriptCredential plc) ownCS
      (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) with
  | false =>
      exact absurd
        (P4_local_RIdx_negative_control ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
          o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee hvalid
          (fun h => Bool.noConfusion (hb.symm.trans h)))
        (fun he => halt_not_error _ hsucc he)
  | true => rfl

/-- Tightness stanza at SHAPE L2R: the NEGATION of the no-escape postcondition
under an accepting run must be FALSIFIABLE. Expected: `Falsified`. -/
def P4_local_RIdx_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [P4_local_RIdx_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE L2R'S OWN PREP TERM AND SHAPE.** This is the
one stanza the re-cut cannot inherit from anywhere: neither SHAPE L1R's probe (a
different prep term, a different class) nor SHAPE L2's (a different, proved-EMPTY
withdrawal/redeemer shape) covers it. Freeing the registration index while ALSO
shrinking the withdrawal map is exactly the combination that could have produced an
accept-UNSAT class, and SHAPE G6 at budget 2500 is the campaign's proof that this
happens silently and that only the probe catches it. "No accepting shape-L2R
context exists within 2500 CEK steps" must be FALSIFIED. -/
def P4_local_RIdx_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 : Integer) (mlRed : ByteString)
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localRCtxIdx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee) →
    ¬ isSuccessful
      (appliedMintLocalRShapedIdx2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0
        c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 mlRed regIdx fee)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [P4_local_RIdx_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE L2R, and its REALIZABILITY

SHAPE L1R's witness leaves verbatim, with the registration index passed as the
ORDINARY ARGUMENT `regIdx = 1` — so the context is `L1RWitness.ctx` on the nose
(`localRCtxIdx_at_one`) while the applied term is SHAPE L2R's, in which the index
was never reduced at prep time. -/

namespace L2RWitness

set_option maxRecDepth 1000000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"

/-- The witness context: SHAPE L2R at `regIdx = 1` and SHAPE L1R's leaves. -/
def ctx : ScriptContext :=
  localRCtxIdx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
    1
    50

/-- AUDIT: it is `L1RWitness.ctx`, definitionally. -/
theorem ctx_eq_L1R : ctx = L1RWitness.ctx := rfl

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis IN FULL. -/
theorem ctx_valid : validMintingContext ctx = true := by native_decide

/-- **AND the `MissingRedeemers` row CLAB is missing** — the conjunct no SHAPE L2
context can satisfy, because SHAPE L2's class is proved empty on exactly this row. -/
theorem ctx_covered : Realizability.redeemerCovered ctx = true := by native_decide

/-- **REALIZABILITY OF SHAPE L2R — the acceptance criterion.** A concrete member of
the class satisfying CLAB's strongest ledger predicate AND redeemer coverage, with
the three ∀-form coverage facts supplied by the SHAPE-LEVEL theorems, so they hold
at every other member and every other index too, not only here. -/
theorem ctx_realizable : Realizability.Realizable ctx := by
  refine ⟨by native_decide, ctx_covered, ?_, ?_, ?_⟩
  · apply localRIdx_wdrl_covered
  · apply localRIdx_spend_covered
  · apply localRIdx_mint_covered

/-- The witness genuinely mints a STRICTLY POSITIVE quantity of its own policy —
token CREATION, which is what the no-escape scan is about. -/
theorem ctx_mints_positive : mintPos ownCS ctx.scriptContextTxInfo.txInfoMint = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-L2R
context at budget 2500, through the SHAPED applied term the theorems above quantify
over — the one in which `regIdx` is an argument, not a prep-time constant. -/
theorem exec_accepts_at_2500 :
    isSuccessful
      (appliedMintLocalRShapedIdx2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
        1
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1681`, PINNED TWO-SIDED** (halts at 1681,
budget-errors at 1680). Identical to `L1RWitness.K_is_1681`, to SHAPE L1's witness
and to the `mint-local-registered-by-ref` golden's measured K: the loosening costs
ZERO CEK steps at its own witness, because the context reaches the machine as ONE
constant term (`CardanoLedgerApi/V3/Contexts.lean:717-720`) and at `regIdx = 1`
`pcheckedDrop` takes the branch it takes for the literal 1. -/
theorem K_is_1681 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1681) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1680) = false := by native_decide

/-! ### THE LOOSENED INDEX IS GENUINELY LIVE — the `regIdx = 0` excluded case

Without this stanza "the index is symbolic" would be a claim about the prep term
only. The sole change from `ctx` is `regIdx = 1 → 0`, which points the registration
witness at the PARAMS reference input instead of the directory node. That reference
input carries `PARAMS.PTOK`, not the `DIRCS.OWNCS` directory NFT, so `hasNodeNFT`
(Issuance.hs:156-157) is false there and `registrationOk` (`:196`) fails. -/

def ctxIdx0 : ScriptContext :=
  localRCtxIdx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
    0
    50

/-- The `regIdx = 0` member is a FULLY LEDGER-LEGAL, REDEEMER-COVERED shape-L2R
transaction — it differs from the accepted witness in the redeemer payload alone —
and it still SATISFIES the no-escape postcondition. So the theorem's class contains
members the bytecode rejects for a reason unrelated to its conclusion, which is
what "the index is genuinely quantified over" means. -/
theorem ctxIdx0_valid_and_covered :
    validMintingContext ctxIdx0 = true ∧
    Realizability.redeemerCovered ctxIdx0 = true ∧
    noEscape (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")) ownCS
      ctxIdx0.scriptContextTxInfo.txInfoOutputs = true := by native_decide

/-- …and the REAL compiled bytecode REJECTS it at budget 2500. -/
theorem exec_rejects_regIdx0 :
    isHaltB
      (appliedMintLocalRShapedIdx2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "PROGLOGIC") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") 0 (ByteString.mk "MLRED")
        0
        50) = false := by native_decide

end L2RWitness

end WSC
