/-
WSC/Props/Shaped/P4LocalShaped.lean — **P4's `Local` custody arm, PROVED at UPLC
level against the real compiled issuance bytecode, over SHAPE L1** (task V3).

════════════════════════════════════════════════════════════════════════════
PLAIN ENGLISH — what is now a theorem about the real bytecode
════════════════════════════════════════════════════════════════════════════
*If the real compiled issuance policy accepts a `Local`-arm transaction of shape
L1, then EVERY output of that transaction whose payment credential is not the
mini-ledger base credential holds ZERO of the minted policy.* The tokens the
policy creates cannot escape the mini-ledger — and the policy proves this itself,
with its own scan, without delegating to the global transfer validator or to the
seize validator.

Two further conjuncts come with it: the token's minting-logic script ran (C1),
and the minted policy is registered in the directory (a reference input carries
its directory NFT). Together the three ARE `WSC/Spec.lean`'s `LocalCustodyOk`,
i.e. disjunct 1 of the four-way P4 custody disjunction (ARCHITECTURE §3-P4).

WHY THIS IS THE VALUABLE ARM. `Local` is the only arm in which the ISSUANCE
POLICY ITSELF enforces custody (Issuance.hs:159-198, scan at :179-193). The
`DelegateTransfer` and `DelegateSeize` arms discharge custody by proving another
script is running, so their custody content is only as strong as P1 / P2, which
are still unproven at UPLC. `BurnOnly` (already shaped in
WSC/Props/Shaped/P4Shaped.lean) creates nothing. So this module is where the
no-escape guarantee stops being an assumption about a sibling validator and
becomes a theorem about the bytecode in front of us.

GROUND-TRUTH FORM (ARCHITECTURE Tier 0.1, hard gate). The postcondition is
`WSC/Spec.lean`'s `noEscape`, which mentions ONLY ledger data: each output's
address payment credential, each output's `Value`, the `progLogicCred` field of
the params datum, and the minted currency symbol. It is NOT "the validator's scan
returned true", which would be a tautology. Nothing in it is a validator-computed
value.

════════════════════════════════════════════════════════════════════════════
SCOPE — TWO BOUNDS, BOTH BINDING. Never quote a theorem below without both.
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 2500** (ADDENDUM E1). `#prep_uplc … 2500` bakes the
budget into `appliedMintLocalShaped2500.prop`; exhaustion is `Error`, so
`isSuccessful` is false and the implications say nothing past the bound. Bridged
to real node acceptance by `LR_BUDGET_minting` (WSC/Honest.lean). 2500 was chosen
because the cheapest accepting `Local` golden needs **1,681** steps
(WSC/goldens/K-MEASUREMENTS.md §3) and the concrete SHAPE L1 witness below needs
**exactly the same K = 1681** (`P4LocalShapedWitness.K_is_1681`); shaped prep is
budget-independent (1.1 s at 2500), so the margin is free.

**Bound 2 — SHAPE L1.** Every fixed dimension is enumerated in
WSC/Shaped/MintingLocalShaped.lean's header. In one line: one pubkey input
carrying ada plus `ownCS`, exactly two reference inputs (params node then claimed
registration node), exactly two script-address outputs (the first ada plus one
free policy, the second ada-only), a one-policy/one-token mint with a symbolic
SIGNED quantity, a 2-entry all-script withdrawal map, one redeemer entry, empty
cert/signatory/datum/vote/proposal lists, and the redeemer fixed to
`Local 0 0 (RegisteredByReferenceInput 1)`.

**Bound 2a — the arm is fixed by the redeemer tag.** Fixing the constructor to
tag 0 restricts the class to the `Local` arm. That is the point of this module;
the other three arms are separate shapes (M1/M2 for `BurnOnly`, and see the
FOUR-WAY DISJUNCTION section below).

**Bound 2b — ONE OUTPUT COUNT AT A TIME.** SHAPE L1 has exactly two outputs. The
`noEscape` scan is a `pall` over a list whose LENGTH the shape fixes, so this is
a theorem about two-output transactions, not about all transactions. Two is the
smallest count at which the scan is not degenerate: with ONE output the ledger
balance rule alone forces that output to carry `ownCS`, so the per-output
disjunction collapses to a single credential comparison and the `¬hasCS` branch
is never taken. At two, output 1 discharges through the value branch and output 0
through the credential branch. A statement for ALL output counts needs an
induction the shaped layer cannot express; that is the shape-coverage gap of
WSC/SHAPING-RESULTS.md §7 and it is not closed here.

**Bound 2c — the index fields are concrete, and the loosening rung was MEASURED.**
SHAPE L1 pins `mrMintingLogicWdrlIdx = 0`, `mrParamsRefIdx = 0` and the
registration index `= 1`. These are self-validating hints re-checked by
`pcheckedDrop`/`phead` plus the branch conditions (Issuance.hs:126-130, :150-151,
:172-173). **SHAPE L2** (`WSC/Shaped/MintingLocalShapedIdx.lean`) frees the
REGISTRATION index, and the answer splits cleanly:

| obligation at SHAPE L2 | Z3 cap | outcome | wall |
|---|---|---|---|
| **`noEscape`** (the headline) | 300 s | **`✅ Valid`** | **2.2 s** (whole module) |
| vacuity probe at SHAPE L2 | 300 s | `✅ Falsified` (non-empty) | — |
| `anyRefInputHasNodeNFT` (registration) | 300 s | **`⚠️ Undetermined`** (cap fired) | 4 m 53 s (`WSC/Shaped/Probe/L2Reg.lean`) |

So the no-escape guarantee — the thing this module is for — does NOT depend on the
registration index being concrete, and `P4_local_noEscape_shapedIdx` below states
it at SHAPE L2, SUPERSEDING `P4_local_noEscape_shaped` in strength. The
REGISTRATION conjunct does depend on it, for the same reason SHAPE G3 does
(WSC/SHAPING-RESULTS.md §6.2): a symbolic index turns `pcheckedDrop` into a
symbolic `dropList`, which puts the branch structure back into the residual. That
is a solver limit and not an empty class — the SHAPE L2 vacuity probe is
`Falsified`.

**DEFECT D1 STILL DODGED.** `validMintingContext` includes CLAB's
`validRedeemerMap`, whose `ScriptPurpose` order disagrees with the ledger's
(WSC/STATUS.md §3 D1). SHAPE L1 has exactly ONE redeemer entry, so it is sorted
under either order. This is a scope statement, not a fix.

════════════════════════════════════════════════════════════════════════════
NOT TRUE BY CONSTRUCTION
════════════════════════════════════════════════════════════════════════════
Full argument in WSC/Shaped/MintingLocalShaped.lean's "NOT TRUE BY CONSTRUCTION"
stanza. In summary: `o0h` (output 0's payment-credential hash) and `plc` (the
params datum's `progLogicCred` hash) are DIFFERENT free variables, and so are
`c0` (output 0's non-ada policy) and `ownCS`; the registration node's `nCS`/`nTn`
are different free variables from `dirCS`/`ownCS`; the params node's `pCS` is a
different free variable from the script parameter `ppCS`; and both withdrawal
hashes are free. So all three conjuncts of `LocalCustodyOk` are earned from the
bytecode.

The sharpest evidence that the no-escape conjunct is not hypothesis-implied is
`P4LocalShapedWitness.exec_rejects_escaping_output` at the bottom of this file: a
LEDGER-VALID shape-L1 context whose output 0 sits at a NON-base credential while
holding the minted tokens, which the real CEK machine rejects.

════════════════════════════════════════════════════════════════════════════
SOURCE FIDELITY (read 2026-07-25 from the wsc-poc worktree `new-session-3c417d`,
src/programmable-tokens-onchain/lib/SmartTokens/Contracts/Issuance.hs)
════════════════════════════════════════════════════════════════════════════
The `Local` branch is Issuance.hs:159-198. The three `pvalidateConditions`
conjuncts (:194-198) that the theorems below certify:

1. `mintingLogicInvokedAt # wdrlIdx` (:195), defined at :150-151 as
   `(pfstBuiltin # (phead # (pcheckedDrop # pfromData wdrlIdx # withdrawalEntries)))
    #== mintingLogicCred`, with `mintingLogicCred = pdata $ pcon $
   PScriptCredential mintingLogicHash'` (:136). Ground-truth counterpart:
   `mintingLogicInvoked` (WSC/Spec.lean:142-144).
2. `registrationOk` (:196), the `PRegisteredByReferenceInput` arm at :172-173:
   `hasNodeNFT # directoryNodeCS # pfromData ptxOut'value` on the reference input
   at the witnessed index, where `hasNodeNFT` (:156-157) is
   `pvalueOf # value # directoryNodeCS # ownAsTokenName #== 1` and
   `ownAsTokenName = pcon $ PTokenName (pto ownCS)` (:141). Ground-truth
   counterpart: `hasNodeNFT` / `anyRefInputHasNodeNFT` (WSC/Spec.lean:155-164).
3. `noEscape` (:197), defined :179-193: a `pall` over `ptxInfo'outputs` that, for
   each output, takes `txOutFields = psndBuiltin # (pasConstr # pforgetData o)`,
   reads `addrData = phead # txOutFields` and `valueData = phead # (ptail #
   txOutFields)`, extracts `paymentCredData = phead # (psndBuiltin # (pasConstr #
   addrData))`, and returns `True` when that equals `pforgetData pprogLogicCred`
   (:182, :189-190) and otherwise `pnot # (phasCS # value # ownCS)` (:192).
   Ground-truth counterpart: `noEscape` (WSC/Spec.lean:187-191), with
   `hasCurrencySymbol` (CardanoLedgerApi/V1/Value.lean:170-173) for `phasCS` and
   decoded `Credential` equality for the raw `Data` comparison — equivalent by
   injectivity of the `Credential` `IsData` encoding.

`pprogLogicCred` and `pdirectoryNodeCS` come from `pparamsAtRefIdx
(pfromData protocolParamsCS) referenceInputs (pfromData paramsRefIdx)`
(Issuance.hs:161-162), i.e. ProgrammableLogicBase.hs:824-838 — the reference
input at the redeemer's own `mrParamsRefIdx`, gated by `phasCSH` (:832) and
decoded as `PProgrammableLogicGlobalParams` (:833-835). SHAPE L1 pins
`mrParamsRefIdx = 0` and `localShapedParams_isDatum` audits that reference input
0's inline datum IS the `GlobalParams` record the postconditions name — the
lesson of the SHAPE G2 falsification (WSC/SHAPING-RESULTS.md §6.1), where naming
the params record through a CHOSEN reference position instead of the redeemer's
own index produced a genuine counterexample.

E1 CAVEAT (verbatim, binding on every theorem in this file): what is proved is a
statement about `cekExecuteProgram … 2500`. A real node runs the same script with
an ExUnits budget, not a step budget; the bridge is the assumption
`LR_BUDGET_minting` in WSC/Honest.lean. Nothing here discharges it.
-/
import WSC.Shaped.MintingLocalShaped
import WSC.Shaped.MintingLocalShapedIdx
import WSC.Spec
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry` warnings
-- on blaster-proved theorems are expected and whitelisted.
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

/-- **P4-Local's no-escape scan over SHAPE L1 — PROVED AT UPLC.**

*Every output of an accepted shape-L1 `Local` mint whose payment credential is
not the mini-ledger base credential `progLogicCred` holds ZERO of the minted
policy `ownCS`.*

Stated in GROUND TRUTH (`WSC/Spec.lean`'s `noEscape`): output addresses, output
`Value`s, the params datum's `progLogicCred`, and the minted currency symbol.
It is not "the validator's scan returned true".

Both disjuncts of the per-output condition are live at the shape (`o0h ≠ plc` as
variables; `c0 ≠ ownCS` as variables), so neither the credential test nor the
value test is pre-satisfied. Output 1, being ada-only, discharges the scan
through the VALUE disjunct; output 0 must discharge it through the CREDENTIAL
disjunct, which the bytecode has to earn.

MEASURED: `✅ Valid`, ≈1.2 s, budget 2500. Validator source: Issuance.hs:179-193
+ :197. -/
theorem P4_local_noEscape_shaped :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true := by blaster

/-! ## The other two conjuncts of the arm -/

/-- **C1 over SHAPE L1 — PROVED AT UPLC.** An accepted shape-L1 `Local` mint runs
the token's minting-logic script: its credential appears in the withdrawal map.
This is the conjunct shared by all four arms (Issuance.hs:150-151, listed at
:195, :216, :242, :253); P4a was already proved at SHAPE M1/M2 for the `BurnOnly`
arm, and this is the same statement on the `Local` arm.

MEASURED: `✅ Valid`. -/
theorem P4a_local_shaped :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      credentialInWithdrawals (Credential.ScriptCredential mlh)
        (localShapedWdrl w0 w1 a0 a1) := by blaster

/-- **Registration over SHAPE L1 — PROVED AT UPLC.** An accepted shape-L1 `Local`
mint really does exhibit the minted policy's directory NFT: some reference input
carries exactly one token of the directory policy `dirCS` — the policy published
by the params datum the validator itself read at `mrParamsRefIdx = 0` — whose
token name is the bytes of `ownCS`.

Ground truth: `anyRefInputHasNodeNFT` (WSC/Spec.lean:161-164), the index-free
consequence of Issuance.hs:172-173. MEASURED: `✅ Valid`. -/
theorem P4_local_registration_shaped :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      anyRefInputHasNodeNFT dirCS ownCS
        [ localShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
        , localShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ] = true := by blaster

/-! ## The arm predicate, and P4's four-way disjunction -/

/-- **P4's disjunct 1 over SHAPE L1 — PROVED AT UPLC.** The conjunction of the
three theorems above IS `WSC/Spec.lean`'s `LocalCustodyOk` for the params record
the validator read at reference index 0. Stated as one blaster obligation rather
than assembled from the three, so that the `&&`-structure is certified by the
solver against the bytecode and not by Lean bookkeeping.

MEASURED: `✅ Valid`. -/
theorem P4_local_arm_shaped :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
        (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
          pHash pCS pTn pAda pQty dirCS plc glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) = true := by blaster

/-- **P4's FOUR-WAY CUSTODY DISJUNCTION over SHAPE L1 — PROVED AT UPLC.**
`ARCHITECTURE §3-P4`'s statement verbatim: an accepted mint satisfies at least
one of the four custody predicates. At SHAPE L1 it is disjunct 1 that is
satisfied, and this theorem states the disjunction so it can be quoted as P4
rather than as "P4's Local arm".

HONESTY NOTE — WHAT THIS DOES *NOT* SAY. The disjunction is proved SHAPE BY
SHAPE, because the shape fixes the redeemer's constructor tag and the tag selects
the arm. Present coverage:

| arm | shape | where | witness K |
|---|---|---|---|
| 1 `Local` | **L1** | this module | 1681 |
| 2 `DelegateTransfer` | DT1 | WSC/Props/Shaped/P4DelegateShaped.lean | 1257 |
| 3 `DelegateSeize` | DS1 | WSC/Props/Shaped/P4DelegateShaped.lean | 1466 |
| 4 `BurnOnly` | M1 / M2 | WSC/Props/Shaped/P4Shaped.lean, P4ShapedIdx.lean | 784 |

All four arms are covered, but by four theorems over four PAIRWISE DISJOINT shape
classes, not by one theorem over a symbolic redeemer.

A single theorem quantifying over the redeemer tag as well would need the tag to
be symbolic in the shape, which is precisely what makes the prep tractable; that
is the shape-coverage gap of WSC/SHAPING-RESULTS.md §7 and it is NOT closed here.

MEASURED: `✅ Valid`. -/
theorem P4_disjunction_at_L1 :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
      (LocalCustodyOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || DelegateTransferOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || DelegateSeizeOk mlh (localShapedParams dirCS plc glc slc) ownCS
         (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
       || BurnOnlyOk mlh ownCS
         (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
           pHash pCS pTn pAda pQty dirCS plc glc slc
           nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) = true := by blaster

/-! ## STRONGER RUNG — the same no-escape theorem with the REGISTRATION INDEX FREE

SHAPE L2 (`WSC/Shaped/MintingLocalShapedIdx.lean`) is SHAPE L1 with the
`RegisteredByReferenceInput` index a free `Integer` leaf instead of the constant 1.
The theorem below is `P4_local_noEscape_shaped` over that larger class, so it
SUPERSEDES it in strength; L1's version is kept because the concrete witness, the
excluded-case witness and the `LocalCustodyOk` / disjunction stanzas are stated
against it.

Measured ladder for this rung, including its one failure, in Bound 2c above. -/

/-- **P4-Local's no-escape scan over SHAPE L2 — PROVED AT UPLC, registration index
SYMBOLIC.** Same ground-truth postcondition as `P4_local_noEscape_shaped`, over a
strictly larger shape class: the reference-input index the `Local` arm's
registration witness names is a free variable, so the theorem covers every value
of it — including the negative values `pcheckedDrop` explicitly rejects
(Issuance.hs:126-130) and every out-of-range value.

MEASURED: `✅ Valid`, 2.2 s at a 300 s Z3 cap. Contrast the REGISTRATION conjunct
at the same shape, which is `Undetermined` (Bound 2c) — the no-escape property is
index-independent, the registration property is not. -/
theorem P4_local_noEscape_shapedIdx :
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
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) →
    isSuccessful
      (appliedMintLocalIdxShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) →
      noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true := by blaster

/-- **MANDATORY VACUITY PROBE AT SHAPE L2** — needed independently of L1's, because
freeing the index changes the class. Expected and MEASURED: `✅ Falsified`. It is
also what makes the `Undetermined` registration rung (Bound 2c) readable as a
SOLVER LIMIT rather than an empty class. -/
def P4_localIdx_vacuity_probe : Prop :=
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
    (regIdx : Integer) (fee : Integer),
    validMintingContext
      (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) →
    ¬ isSuccessful
      (appliedMintLocalIdxShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee)

#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1) [P4_localIdx_vacuity_probe]

/-! ## Polarity controls (ADDENDUM E9) — the full four-stanza set -/

/-- Negative control (≡ the contrapositive of the no-escape theorem over the
shape): a shape-L1 context in which SOME output outside the base credential holds
the minted policy is REJECTED by the real bytecode. MEASURED: `✅ Valid`.

NOTE (E9, binding): a negative control is also satisfied by budget-`Error`, so it
cannot by itself detect the 2500-step bound. That job belongs to the vacuity
probe and to the concrete witness below. -/
theorem P4_local_negative_control :
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true) →
    isUnsuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := by blaster

/-- Tightness stanza: the NEGATION of the no-escape postcondition under an
accepting run must be FALSIFIABLE (if it were `Valid` the theorem above would be
vacuous). Expected and MEASURED: `Falsified`. -/
def P4_local_tightness : Prop :=
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ (noEscape (Credential.ScriptCredential plc) ownCS
        (localShapedOutputs o0h outAda0 c0 tn0 qq0 o1h outAda1) = true)

#blaster (gen-cex: 0) (solve-result: 1) [P4_local_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE L1.** "No accepting shape-L1 context exists
within 2500 CEK steps" must be FALSIFIED — a shape class can easily be
accept-UNSAT, which would make every theorem above empty in a way no other
control detects.

Expected and MEASURED: `✅ Falsified`. The concrete witness below discharges the
same obligation a second time, executably and without the SMT solver. -/
def P4_local_vacuity_probe : Prop :=
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
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0
        o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (gen-cex: 0) (solve-result: 1) [P4_local_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE L1 — executable, no SMT

A concrete accepting instance of the exact shape, run through the REAL CEK machine
and closed by `native_decide`, so non-vacuity does not rest on a solver verdict.

Leaf values: the policy `OWNCS` mints **+3** of `OWNCS.TOK` (a STRICTLY POSITIVE
mint — token creation, which is what the no-escape scan is about); the input
holds 2 of them; output 0 sits at `ScriptCredential "PROGLOGIC"` — exactly the
`progLogicCred` the params datum publishes — and holds all 5; output 1 sits at
`ScriptCredential "OTHER"`, outside the mini-ledger, and is ada-only. 200 lovelace
in, 100 + 50 out, 50 fee. Reference input 0 is the params node, whose value
carries the script parameter policy `PARAMS` and whose datum publishes
`directoryNodeCS = DIRCS`, `progLogicCred = ScriptCredential PROGLOGIC`; reference
input 1 is the registration node, carrying exactly one `DIRCS.OWNCS` token — the
directory NFT named after the minted policy. Withdrawals
`[(ScriptCredential "MINTLOGIC", 0), (ScriptCredential "ZZZ", 0)]` — sorted, with
the minting-logic credential at index 0, which is the index the redeemer names. -/

namespace P4LocalShapedWitness

set_option maxRecDepth 1000000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"

/-- The witness context: SHAPE L1 at the leaf values above. -/
def ctx : ScriptContext :=
  localShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
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
    50

/-- Bool reflection of `isSuccessful` (a `Prop`), for `native_decide`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the theorems' ledger-normalization hypothesis IN FULL. -/
theorem ctx_valid : validMintingContext ctx = true := by native_decide

/-- The witness names `OWNCS` as the minting policy. -/
theorem ctx_ownCS : ownCurrencySymbol ctx = some ownCS := by native_decide

/-- The witness genuinely mints a STRICTLY POSITIVE quantity of its own policy —
so it is a token-CREATION transaction, not a burn, and the no-escape scan is the
only thing standing between those tokens and the outside world. -/
theorem ctx_mints_positive : mintPos ownCS ctx.scriptContextTxInfo.txInfoMint = true := by
  native_decide

/-- The witness satisfies the full arm-1 predicate `LocalCustodyOk` — hence also
each of the three theorems' postconditions. -/
theorem ctx_post_localCustody :
    LocalCustodyOk mlh
      (localShapedParams (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC")
        (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")) ownCS ctx = true := by
  native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-L1
context at budget 2500, through the SHAPED applied term the theorems above
quantify over. -/
theorem exec_accepts_at_2500 :
    isSuccessful
      (appliedMintLocalShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
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
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 1681`, to the step.** This witness halts at 1681 and
budget-errors at 1680 (measured by binary search in `WSC/Shaped/Probe/L1K.lean`,
pinned here as a theorem).

**1681 is EXACTLY the measured step count of the off-chain `Local` golden**
`programmableTokenMinting.mint-local-registered-by-ref`
(WSC/goldens/K-MEASUREMENTS.md §3), so SHAPE L1 reproduces the real production
transaction's cost to the step — the same coincidence SHAPE M1 exhibits for the
burn golden (K = 784, WSC/SHAPING-RESULTS.md §4). That is the strongest available
evidence that this shape is not a toy: it is the real `Local` transaction's shape,
generalised only in the directions listed in the "NOT TRUE BY CONSTRUCTION"
stanza.

The budget is nevertheless set to 2500, not 1700, for two reasons: shaped prep is
budget-independent so the margin is free (1.1 s at 2500), and a tight budget
weakens the theorem — accepting contexts of the shape that cost slightly more than
the witness would fall outside the bound and be silently excluded. -/
theorem K_is_1681 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1681) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableTokenMinting900.script
              (mintingPolicyInputs900 ppCS mlh ctx) 1680) = false := by native_decide

/-! ### EXCLUDED-CASE WITNESS — the escaping output is real, and rejected

`P4_local_noEscape_shaped` is only interesting if a shape-L1 context with an
ESCAPING output is ledger-valid in the first place. It is, and the real CEK
machine rejects it. This is a sharper control than the tightness stanza: tightness
only says "some accepting context satisfies the postcondition", whereas this
exhibits the specific ledger-legal context the postcondition EXCLUDES and shows
the bytecode refusing it.

The only change from `ctx` is output 0's payment-credential hash: `EVIL` instead
of `PROGLOGIC`. The minted tokens now sit outside the mini-ledger. Nothing about
the ledger balance, the value canonicity, the registration NFT or the withdrawal
map changes — so this is a real transaction a real attacker could submit. -/

/-- SHAPE L1 with output 0 at a NON-base credential while holding the minted
tokens. -/
def ctxEscape : ScriptContext :=
  localShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 200 2
    (ByteString.mk "EVIL") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
    (ByteString.mk "OTHER") 50
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
    50

/-- The escaping context IS ledger-valid, it DOES mint a positive quantity of the
policy, and it genuinely VIOLATES the no-escape postcondition. -/
theorem ctxEscape_valid_and_escaping :
    validMintingContext ctxEscape = true ∧
    mintPos ownCS ctxEscape.scriptContextTxInfo.txInfoMint = true ∧
    noEscape (Credential.ScriptCredential (ByteString.mk "PROGLOGIC")) ownCS
      ctxEscape.scriptContextTxInfo.txInfoOutputs = false := by native_decide

/-- …and the REAL compiled bytecode REJECTS it at budget 2500. So
`P4_local_noEscape_shaped` excludes a non-empty, ledger-legal set of
transactions — the no-escape guarantee is not vacuous on its interesting case. -/
theorem exec_rejects_escaping_output :
    isHaltB
      (appliedMintLocalShaped2500.exec ppCS mlh (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
        (ByteString.mk "OWNER") 200 2
        (ByteString.mk "EVIL") 100 (ByteString.mk "OWNCS") (ByteString.mk "TOK") 5
        (ByteString.mk "OTHER") 50
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "OWNCS") 100 1
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
        (ByteString.mk "GS")
        (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0
        50) = false := by native_decide

end P4LocalShapedWitness

end WSC
