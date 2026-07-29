/-
WSC/Props/Shaped/P4LocalShapedRDirect.lean — **SHAPE L2R's TWO OPEN OBLIGATIONS,
CLOSED DIRECTLY, BY PINNING A MEASURED Z3 RANDOM SEED** (task X3 / consolidation
task).

════════════════════════════════════════════════════════════════════════════
WHAT THIS CLOSES
════════════════════════════════════════════════════════════════════════════
`WSC/STATUS.md` finding **F19** carries two riders, both of which this module
retires:

1. *"the headline is DERIVED from a `✅ Valid` negative control (the direct goal
   is `⚠️ Undetermined` at a 300 s cap) via `halt_not_error`"* —
   `L2R_noEscape_direct` below proves the headline DIRECTLY.  The derivation via
   `halt_not_error` was never wrong (it is strictly stronger — see
   `WSC/AUDIT.md`), but it was an indirection a reviewer had to check; now the
   direct statement stands on its own as well.
2. *"**C1 at L2R is `⚠️ Undetermined` and is not asserted**"* —
   `L2R_C1_direct` below asserts it.

Both were `⚠️ Undetermined` in `WSC/Shaped/Probe/L2RProbe.lean` at a 300 s cap.
Both are stated here as REAL THEOREMS closed by the `blaster` TACTIC, not by a
`#blaster` COMMAND: an `⚠️ Undetermined` in tactic position does NOT warn — it
leaves the goal open and HARD-FAILS the build.  So these two cannot silently
degrade.

════════════════════════════════════════════════════════════════════════════
THE ONLY DIFFERENCE FROM `L2RProbe.lean` IS `(random-seed: 7)`
════════════════════════════════════════════════════════════════════════════
Same shape, same prep (`appliedMintLocalRShapedIdx2500`), same hypotheses, same
conclusion, same 300 s cap.

`random-seed` reaches Z3 through `Blaster/Smt/Env.lean:614`
(`(set-option :smt.random-seed n)`).  **Note `Blaster/Command/Syntax.lean:101`
maps `0 → none`**, so `random-seed: 0` is the NO-SEED control, not "seed zero";
Z3's own default seed IS 0, and it is pathological on these two queries.

**Seed 7 is not a lucky one-off, and the hit rates are recorded because they
are very different maintenance stories.**  Driven straight at the SMT-LIB query
Blaster emits (reconstructed with `only-smt-lib` + `dump-smt-lib`), over
`smt.random-seed` 0–99 with z3 4.15.2:

| goal | seeds returning `unsat` | median win |
|---|---|---|
| the C1 goal | **94 / 100** (failures: 0, 28, 72, 73, 75, 78) | ≈ 0.5 s |
| the no-escape goal | **56 / 100** | ≈ 0.5 s |
| both at once | 54 / 100, including 3, 7, 9, 10, 15 | — |

`z3 -st` on the no-escape query explains the bimodality: at seed 7 it is `unsat`
in 0.28 s with 153 conflicts and 27.8 MB peak; at a losing seed it times out at
30 s having allocated 1.1 × 10¹¹ words.  A short refutation exists; the shipped
default search does not find it.  More TIME never helps — the behaviour is
bimodal, not slow — which is consistent with the recorded 296/1,748/3,208 s
identical-`Undetermined` measurements elsewhere in this library.

════════════════════════════════════════════════════════════════════════════
THREE THINGS A MAINTAINER MUST KNOW
════════════════════════════════════════════════════════════════════════════
1. **NEVER SET A SEED GLOBALLY.**  Measured: seed 17 turns
   `WSC/Shaped/Probe/L2Probe.lean`'s `L2_noEscape` — `✅ Valid` at the default —
   into `⚠️ Undetermined`.  A seed is pinned per stanza against a measured
   value or not at all.
2. **THE FAILURE MODE IS SAFE.**  A re-rolled seed (a z3 bump, a re-prep, an
   edit to the statement) breaks the build LOUDLY: `Undetermined` never admits.
   It cannot manufacture a false proof.  It is deterministic, not probabilistic
   — same seed + same query + same z3 ⟹ same answer, confirmed over 3/3 forced
   re-elaborations (a content-changing edit; `touch` alone replays a cached
   lake trace and proves nothing).
3. **A `Valid` IS AN `unsat` ON THE NEGATED GOAL, WHICH AN INCONSISTENT
   ENCODING WOULD ALSO PRODUCE.**  So the seed must never be shipped without a
   guard that is expected to be SAT at the same seed.  §2 is that guard.
-/
import WSC.Shaped.MintingLocalShapedRIdx
import WSC.Spec
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validMintingContext credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## §1 THE TWO THEOREMS -/

/-- **THE SHAPE-L2R HEADLINE, PROVED DIRECTLY.**  *At SHAPE L2R — the
node-realizable `Local` arm with the registration reference-input index left
SYMBOLIC — an accepted mint leaves no token of its own currency symbol outside
the mini-ledger.*

Previously available only via `P4_local_RIdx_negative_control` +
`halt_not_error` (`WSC/Props/Shaped/P4LocalShapedR.lean`). -/
theorem L2R_noEscape_direct :
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
  blaster (random-seed: 7) (timeout: 300)

/-- **C1 AT SHAPE L2R, PROVED DIRECTLY** — *an accepted `Local`-arm mint runs
the token's minting-logic script*.  This is the conjunct F19 recorded as
"`⚠️ Undetermined` and not asserted". -/
theorem L2R_C1_direct :
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
    credentialInWithdrawals (Credential.ScriptCredential mlh) (localRWdrl w0 a0) := by
  blaster (random-seed: 7) (timeout: 300)

/-! ## §2 THE SOUNDNESS GUARD AT THE SAME SEED — mandatory, not optional

The two `Valid`s above are `unsat` results on negated goals.  An INCONSISTENT
encoding produces `unsat` for everything, so a seed that unlocked an
inconsistency would look exactly like a seed that unlocked a proof.  The only
cheap discriminator is a stanza that must come back **SAT** at the SAME seed.

Both below are `✅ Expected Falsified` at seed 7 (also measured at seeds 1 and
42).  Their `Falsified` at seed 7 is what licenses reading §1's `Valid` as a
genuine refutation rather than an artifact. -/

/-- **VACUITY GUARD AT SEED 7.**  "No accepting context of SHAPE L2R" must be
FALSIFIED — the class is non-empty inside the prep budget.  Expected:
Falsified. -/
def L2R_vacuity_seed7 : Prop :=
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

#blaster (random-seed: 7) (timeout: 300) (gen-cex: 0) (solve-result: 1) [L2R_vacuity_seed7]

/-- **TIGHTNESS GUARD AT SEED 7.**  The NEGATION of §1's headline conclusion,
under §1's own hypotheses: acceptance must not force `¬ noEscape`.  Verbatim
`WSC/Shaped/Probe/L2RProbe.lean`'s `L2R_tightness`, re-run at the seed.
Expected: Falsified. -/
def L2R_tightness_seed7 : Prop :=
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

#blaster (random-seed: 7) (timeout: 300) (gen-cex: 0) (solve-result: 1) [L2R_tightness_seed7]

end WSC
