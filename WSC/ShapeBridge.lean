/-
WSC/ShapeBridge.lean — **THE SHAPE BRIDGE** (task U1).

WHAT THIS MODULE IS FOR.  Every shaped theorem in `WSC/Props/Shaped/*` is a
statement about `appliedXShaped.prop <leaves>`.  The composition
(`WSC/Composition.lean`) and the plain-English claim are statements about the
validator running on a `ScriptContext` the LEDGER supplied.  Nothing published
before this module connected the two.  This module is that connection.

================================================================================
## §ANATOMY — what the two terms actually are

`#prep_uplc name prog f K` (PlutusCoreBlaster
`PlutusCore/UPLC/PreProcess.lean:34-65`) elaborates to THREE declarations:

* `name.exec := fun x₁ … xₙ => cekExecuteProgram prog.script (f x₁ … xₙ) K`
  — built by `mkUplcApply` (`:142-153`): the conversion function is
  η-expanded, its telescope is re-abstracted, and the body is literally
  `cekExecuteProgram (PlutusScript.script prog) (f xs) K`.  A PLAIN LEAN
  FUNCTION of the leaves; `addAndCompile`d, so `native_decide`-executable.
* `name.prop := Optimize.main name.exec` — the SAME expression pushed through
  Blaster's elaboration-time `Expr → Expr` optimizer
  (`Blaster/Optimize/Basic.lean:293`, called at `PreProcess.lean:40`).
  `noncomputable` (it embeds `Classical.propDecidable`), so it can only be
  attacked by `blaster`, never by `decide`/`native_decide`.
* `name := ⟨lang, prop, exec⟩`.

`Optimize.main` is a MetaM transformation, NOT a Lean function of a `Term`.  So
"congruence on `Optimize.main`" is not available: the two `prop`s of two
separately-elaborated preps are two unrelated constants.  MEASURED:
`@appliedBase.prop = @appliedBase.exec` is **NOT** a definitional equality
(kernel error "Not a definitional equality", `WSC/Shaped/Probe/BridgeProbe2.lean`
in the U1 workspace) — the optimizer performs De Morgan / Bool-polarity /
`ite → Blaster.dite'` rewrites that are propositionally justified
(`Blaster/Optimize/Decidable.lean:36,43` prove `dite_equiv` and
`ite_to_dite'_equiv`) but not defeq.

## §THE ONE NON-TRIVIAL STEP, AND WHY IT IS FREE HERE

The task's identified crux is *"the shaped inputs fn's `Data` term equals
`toTerm (shapedCtx args)` as a `Term`"*.  In this codebase that step is
**definitional**, because no shape was ever written as a raw `Data` literal:
every `σ` in `WSC/Shaped/*` builds a Lean `ScriptContext` and the shaped inputs
function is literally

    shapedInputs leaves = <params> :: purposeInputs (σ leaves)

with the SAME `purposeInputs` (`spendingInputs`/`mintingInputs`/
`rewardingInputs`) the unshaped prep uses.  So

    shapedInputs leaves  ≡δ  unshapedInputs (paramsOf leaves) (σ leaves)

and therefore, `cekExecuteProgram` being a function,

    appliedXShaped.exec leaves  ≡  cekExecuteProgram prog (unshapedInputs … (σ leaves)) K.

Both are `rfl` below (§LEVEL 1, §LEVEL 2) for all sixteen shaped preps.  This is
the bridge at the only level where both sides ARE functions — kernel-checked, no
solver, no `admit`, no axiom.

## §WHAT REMAINS, AND AT WHICH LEVEL

Two different residuals, and they must not be confused:

1. **Tier A — shapes whose validator HAS an unshaped prep at the SAME budget K.**
   B1@600 (`appliedBase`, and `K_base = 600`), M1/M2@900 (`appliedMinting900`,
   `K_mint = 900`), G1/GIdx/GNIdx@1600 (`appliedGlobal1600`, `K_global_nonmember = 1600`
   after task U2 republished `K_global` to 4400).
   For these the FULL prop-level bridge

       isSuccessful (appliedXShaped.prop leaves)
         ↔ isSuccessful (appliedX_K.prop (paramsOf leaves) (σ leaves))

   is proved below by `blaster` (§LEVEL 3) with discriminating negative controls
   (§CONTROLS).  **NO new axiom and no residual.**  This is genuinely non-trivial
   content: it says *shaping commutes with the optimizer* — the left side
   optimizes the closed skeleton BEFORE instantiation, the right side optimizes
   a symbolic context and instantiates AFTER.
   These are exactly the budgets `WSC/Honest.lean` publishes as `K_base` (600),
   `K_mint` (900) and `K_global_nonmember` (1600), i.e. exactly the preps
   `LR_BUDGET_base` / `LR_BUDGET_minting` / `LR_BUDGET_global`-at-1600 name after
   task U2's hygiene repairs.  `K_global` itself is now 4400 and has NO unshaped
   prep — see §UNSHAPED-PREP-REACH and `WSC/SHAPE-BRIDGE.md` §8.

2. **Tier B — shapes at budgets where NO unshaped prep exists** (2500 minting,
   3300/4400 global, 3800 seize; see §UNSHAPED-PREP-REACH for why one cannot be
   built).  For these the bridge lands on the RAW metered run
   (`Runs.baseRun`/`Runs.mintingRun`/`Runs.globalRun`/`Runs.seizeRun`, task A1's
   leaf module `WSC/Runs.lean`), which mentions no optimizer:

       isSuccessful (appliedXShaped.prop leaves)
         ↔ isSuccessful (Runs.XRun K (paramsOf leaves) (σ leaves))

   `blaster` proves these too (§LEVEL 3′), but READ THE HEALTH WARNING in
   `WSC/SHAPE-BRIDGE.md` §5: `blaster` discharges them by re-running the SAME
   `Optimize.main` on both sides, so the verdict is evidence that the optimizer is
   DETERMINISTIC and IDEMPOTENT, not independent evidence that it is FAITHFUL.
   The precisely-stated residual is `PropExecFaithful` (§RESIDUAL) — deliberately
   a `Prop`-valued `def` and **NOT an axiom**, because it is a pre-existing,
   previously unnamed dependency of the whole campaign (every P-theorem is about
   `.prop`; every executable witness runs `.exec`), not something U1 introduced.

**UPDATE (task A1) — the Tier A / Tier B split no longer matters for the LEDGER
bridge, only for the OPTIMIZER-commutation content.**  `WSC/Honest.lean`'s four
`LR_BUDGET_*` axioms are now stated against `Runs.XRun K` for every budget, so
Tier B's right-hand side is exactly what the ledger side names and the two tiers
have the same consumer.  What Tier A still adds — and Tier B still lacks — is an
INDEPENDENT statement about the optimizer: Tier A's right-hand side went through
`Optimize.main` on a symbolic context, Tier B's did not go through it at all, so
Tier B's verdict cannot witness optimizer faithfulness.  The `PropExecFaithful`
residual is therefore UNCHANGED in substance and UNCHANGED in scope for the
shaped layer: every shaped P-theorem is still stated on `appliedXShaped.prop`.
Where A1 does remove it is the base/keystone path — `WSC/Props/P3_BaseRun.lean`
proves P3 with its accept hypothesis on `Runs.baseRun K_base`, so
`Composition.p3_lifted` no longer mentions `.prop` at all.  That module also
MEASURES that the same restatement is feasible for the P-theorems generally
(`✅ Valid` in 3.7 s, with a `✅ Expected Falsified` vacuity probe at the run
term), which is the identified route to deleting `PropExecFaithful` campaign-wide.
It is NOT done, and no claim here depends on it being done.

## §NOT ESTABLISHED HERE — SHAPE COVERAGE

The bridge says "shaped theorem ⟹ statement about the `ScriptContext`s the shape
denotes".  It says NOTHING about which transactions the shapes cover.  §COVERAGE
records what a coverage argument would require and does not invent one.

WORKSPACE / PROVENANCE: task U1, branch `wsc-containment-proofs`, canonical HEAD
at start `0e2a99d`.  Probes retained under `WSC/Shaped/Probe/BridgeProbe*.lean`.
Task A1 moved §RUN's four definitions to `WSC/Runs.lean` and repointed the
`LR_BUDGET_*` axioms at them; the 25 verdicts of this module are unchanged in
statement (they name the same constants under their new home) and were re-run.
-/
import WSC.Shaped.BaseShaped
import WSC.Shaped.MintingShaped
import WSC.Shaped.MintingShapedIdx
import WSC.Shaped.GlobalShaped
import WSC.Shaped.GlobalShapedIdx
import WSC.Shaped.GlobalMemberShaped
import WSC.Shaped.MintingLocalShaped
import WSC.Shaped.MintingLocalShapedIdx
import WSC.Shaped.MintingDelegateShaped
import WSC.Shaped.SeizeShaped
import WSC.Shaped.GlobalShapedP1Prep
import WSC.Shaped.GlobalShapedP1MintPrep
import WSC.Shaped.GlobalShapedP1OutPrep
import WSC.Prep.Global1600
import WSC.Prep.Seize
import WSC.Runs
import Blaster

set_option maxHeartbeats 0

namespace WSC
namespace ShapeBridge

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          spendingInputs mintingInputs rewardingInputs)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## §RUN — the ledger side, optimizer-free

`Runs.baseRun` / `Runs.mintingRun` / `Runs.globalRun` / `Runs.seizeRun` are *the
validator running on a ledger-supplied `ScriptContext` under a `K`-step meter*,
and nothing else: the imported production bytecode, the audited parameter-evidence
inputs function of `WSC/Prep/*`, and `cekExecuteProgram`.  They are the
right-hand side of the bridge for every shape.

**MOVED OUT OF THIS MODULE BY TASK A1** into the leaf module `WSC/Runs.lean`, so
that `WSC/Honest.lean` can name them without an import cycle.  That was audit
finding **F3**'s repair: the four `LR_BUDGET_*` axioms are now stated against
these very constants, so the sixteen kernel-checked `exec_*` `rfl`s below are the
connective between a shaped theorem and the ledger side.  The definitions are
unchanged; `WSC/Runs.lean`'s header states what the restatement buys and what it
does not. -/

/-! ## §LEVEL 1 + §LEVEL 2 — the kernel-checked bridge, shape by shape

`inputs_<S>` : the shaped inputs function is the unshaped one at `σ leaves`.
`exec_<S>`   : hence the shaped applied term IS the raw metered run on `σ leaves`.

Both are `rfl`.  Sixteen shaped preps, i.e. every shaped prep in the campaign. -/

/-! ### SHAPE B1 — `appliedBaseShaped`, budget 600 -/

/-- LEVEL 1, SHAPE B1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_B1
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    baseShapedInputs gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid
      = baseInputs (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
          (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) := rfl

/-- LEVEL 2, SHAPE B1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_B1
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    appliedBaseShaped.exec gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid
      = Runs.baseRun 600 (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
          (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) := rfl

/-! ### SHAPE M1 — `appliedMintShaped900`, budget 900 -/

/-- LEVEL 1, SHAPE M1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_M1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    mintShapedInputs ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid
      = mintingPolicyInputs900 ppCS mlh
          (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) := rfl

/-- LEVEL 2, SHAPE M1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_M1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    appliedMintShaped900.exec ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid
      = Runs.mintingRun 900 ppCS mlh
          (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid) := rfl

/-! ### SHAPE M2 — `appliedMintShapedIdx900`, budget 900 -/

/-- LEVEL 1, SHAPE M2: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_M2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer) :
    mintShapedInputsIdx ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx
      = mintingPolicyInputs900 ppCS mlh
          (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) := rfl

/-- LEVEL 2, SHAPE M2: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_M2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer) :
    appliedMintShapedIdx900.exec ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx
      = Runs.mintingRun 900 ppCS mlh
          (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx) := rfl

/-! ### SHAPE G1 — `appliedGlobalShaped1600`, budget 1600 -/

/-- LEVEL 1, SHAPE G1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_G1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    globalShapedInputs ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE G1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_G1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShaped1600.exec ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.globalRun 1600 ppCS
          (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE GIdx — `appliedGlobalShapedIdx1600`, budget 1600 -/

/-- LEVEL 1, SHAPE GIdx: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_GIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (pIdx nIdx : Integer) :
    globalShapedInputsIdx ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee pIdx nIdx
      = globalInputs1600 ppCS
          (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            pIdx nIdx) := rfl

/-- LEVEL 2, SHAPE GIdx: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_GIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (pIdx nIdx : Integer) :
    appliedGlobalShapedIdx1600.exec ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee pIdx nIdx
      = Runs.globalRun 1600 ppCS
          (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            pIdx nIdx) := rfl

/-! ### SHAPE GNIdx — `appliedGlobalShapedNIdx1600`, budget 1600 -/

/-- LEVEL 1, SHAPE GNIdx: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_GNIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer) :
    globalShapedInputsNIdx ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee nIdx
      = globalInputs1600 ppCS
          (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            0 nIdx) := rfl

/-- LEVEL 2, SHAPE GNIdx: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_GNIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer) :
    appliedGlobalShapedNIdx1600.exec ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee nIdx
      = Runs.globalRun 1600 ppCS
          (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            0 nIdx) := rfl

/-! ### SHAPE G6 — `appliedGlobalMemberShaped3300`, budget 3300 -/

/-- LEVEL 1, SHAPE G6: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_G6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    memberShapedInputs ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
            pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE G6: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_G6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalMemberShaped3300.exec ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee
      = Runs.globalRun 3300 ppCS
          (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
            pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE L1 — `appliedMintLocalShaped2500`, budget 2500 -/

/-- LEVEL 1, SHAPE L1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_L1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    localShapedInputs ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = mintingPolicyInputs900 ppCS mlh
          (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE L1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_L1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedMintLocalShaped2500.exec ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.mintingRun 2500 ppCS mlh
          (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE L2 — `appliedMintLocalIdxShaped2500`, budget 2500 -/

/-- LEVEL 1, SHAPE L2: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_L2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (regIdx : Integer)
    (fee : Integer) :
    localIdxShapedInputs ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee
      = mintingPolicyInputs900 ppCS mlh
          (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) := rfl

/-- LEVEL 2, SHAPE L2: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_L2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (regIdx : Integer)
    (fee : Integer) :
    appliedMintLocalIdxShaped2500.exec ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee
      = Runs.mintingRun 2500 ppCS mlh
          (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee) := rfl

/-! ### SHAPE DT1 — `appliedMintDTShaped2500`, budget 2500 -/

/-- LEVEL 1, SHAPE DT1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_DT1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    dtShapedInputs ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = mintingPolicyInputs900 ppCS mlh
          (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE DT1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_DT1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedMintDTShaped2500.exec ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.mintingRun 2500 ppCS mlh
          (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE DS1 — `appliedMintDSShaped2500`, budget 2500 -/

/-- LEVEL 1, SHAPE DS1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_DS1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
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
    (fee : Integer) :
    dsShapedInputs ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee
      = mintingPolicyInputs900 ppCS mlh
          (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) := rfl

/-- LEVEL 2, SHAPE DS1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_DS1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
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
    (fee : Integer) :
    appliedMintDSShaped2500.exec ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee
      = Runs.mintingRun 2500 ppCS mlh
          (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee) := rfl

/-! ### SHAPE S1 — `appliedSeizeShaped3800`, budget 3800 -/

/-- LEVEL 1, SHAPE S1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_S1
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
    (fee : Integer) :
    seizeShapedInputs ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = seizeInputs ppCS
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty
            oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE S1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_S1
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
    (fee : Integer) :
    appliedSeizeShaped3800.exec ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.seizeRun 3800 ppCS
          (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty
            oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE T1 — `appliedGlobalShapedT1`, budget 4400 -/

/-- LEVEL 1, SHAPE T1: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_T1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    p1ShapedInputs ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE T1: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_T1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShapedT1.exec ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.globalRun 4400 ppCS
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE T2 — `appliedGlobalShapedT2`, budget 4400 -/

/-- LEVEL 1, SHAPE T2: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_T2
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    p1ShapedMintInputs ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE T2: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_T2
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShapedT2.exec ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.globalRun 4400 ppCS
          (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE T6 — `appliedGlobalShapedT6`, budget 4400 -/

/-- LEVEL 1, SHAPE T6: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_T6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    p1ShapedOutInputs ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE T6: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_T6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShapedT6.exec ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.globalRun 4400 ppCS
          (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ### SHAPE T7 — `appliedGlobalShapedT7`, budget 4400 -/

/-- LEVEL 1, SHAPE T7: the shaped inputs function IS the unshaped one at the
context the shape denotes.  `rfl` — the two sides are the same `δ`-expansion. -/
theorem inputs_T7
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    p1ShapedOutMintInputs ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalInputs1600 ppCS
          (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- LEVEL 2, SHAPE T7: **the shape bridge at the level where both sides are
functions.**  Kernel-checked, no solver, no `admit`. -/
theorem exec_T7
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShapedT7.exec ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = Runs.globalRun 4400 ppCS
          (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-! ## §LEVEL 3 / §LEVEL 3′ — the bridge at the level the theorems live on

`bridge_<S>` closes the gap between `appliedXShaped.prop` (what every shaped
theorem quantifies over) and the ledger side.  Two forms, per §WHAT REMAINS:

* **Tier A** (`B1`, `M1`, `M2`, `G1`, `GIdx`, `GNIdx`) — right-hand side is the
  UNSHAPED prep's `prop` at the same budget.  Complete: no residual.
* **Tier B** (`G6`, `L1`, `L2`, `DT1`, `DS1`, `S1`, `T1`, `T2`, `T6`, `T7`) —
  right-hand side is the RAW metered run `Runs.XRun K` (`WSC/Runs.lean`) — which
  is exactly what `LR_BUDGET_*` now names.  Read with `PropExecFaithful`.

All are discharged by `blaster`, i.e. they carry the same trust status as every
other WSC bytecode theorem (solver verdict + `admit`; see ARCHITECTURE Tier 4). -/

/-- **LEVEL 3, SHAPE B1 — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_B1
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    isSuccessful (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
      ↔ isSuccessful
          (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
            (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)) := by blaster

/-- **LEVEL 3, SHAPE M1 — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_M1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) :
    isSuccessful (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
      ↔ isSuccessful
          (appliedMinting900.prop ppCS mlh
            (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)) := by blaster

/-- **LEVEL 3, SHAPE M2 — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_M2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString) (wIdx : Integer) :
    isSuccessful (appliedMintShapedIdx900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx)
      ↔ isSuccessful
          (appliedMinting900.prop ppCS mlh
            (mintShapedCtxIdx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid wIdx)) := by blaster

/-- **LEVEL 3, SHAPE G1 — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_G1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalShaped1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (appliedGlobal1600.prop ppCS
            (globalShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3, SHAPE GIdx — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_GIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (pIdx nIdx : Integer) :
    isSuccessful (appliedGlobalShapedIdx1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee pIdx nIdx)
      ↔ isSuccessful
          (appliedGlobal1600.prop ppCS
            (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            pIdx nIdx)) := by blaster

/-- **LEVEL 3, SHAPE GNIdx — THE SHAPE BRIDGE, prop level.**  The shaped prep's
optimized term accepts exactly when the UNSHAPED prep's optimized term accepts on
the `ScriptContext` the shape denotes.  Solver-verified (`blaster`). -/
theorem bridge_GNIdx
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (nIdx : Integer) :
    isSuccessful (appliedGlobalShapedNIdx1600.prop ppCS cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee nIdx)
      ↔ isSuccessful
          (appliedGlobal1600.prop ppCS
            (globalShapedCtxIdx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
            dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
            0 nIdx)) := by blaster

/-- **LEVEL 3′, SHAPE G6 — run-form shape bridge.**  No unshaped prep exists at
budget 3300 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_G6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.globalRun 3300 ppCS
            (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
            pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE L1 — run-form shape bridge.**  No unshaped prep exists at
budget 2500 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_L1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedMintLocalShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.mintingRun 2500 ppCS mlh
            (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE L2 — run-form shape bridge.**  No unshaped prep exists at
budget 2500 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_L2
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (regIdx : Integer)
    (fee : Integer) :
    isSuccessful (appliedMintLocalIdxShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee)
      ↔ isSuccessful
          (Runs.mintingRun 2500 ppCS mlh
            (localIdxShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 regIdx fee)) := by blaster

/-- **LEVEL 3′, SHAPE DT1 — run-form shape bridge.**  No unshaped prep exists at
budget 2500 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_DT1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedMintDTShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.mintingRun 2500 ppCS mlh
            (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE DS1 — run-form shape bridge.**  No unshaped prep exists at
budget 2500 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_DS1
    (ppCS : CurrencySymbol) (mlh : ScriptHash)
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
    (fee : Integer) :
    isSuccessful (appliedMintDSShaped2500.prop ppCS mlh ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1 pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)
      ↔ isSuccessful
          (Runs.mintingRun 2500 ppCS mlh
            (dsShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 sCred sIdx fee)) := by blaster

/-- **LEVEL 3′, SHAPE S1 — run-form shape bridge.**  No unshaped prep exists at
budget 3800 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_S1
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
    (fee : Integer) :
    isSuccessful (appliedSeizeShaped3800.prop ppCS mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.seizeRun 3800 ppCS
            (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
            wallet i1Ada i1CS i1Tn i1Qty
            oStk o0Ada o0Qty dOut
            escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
            pHash pCS pTn pAda pQty dirCS plc glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
            w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE T1 — run-form shape bridge.**  No unshaped prep exists at
budget 4400 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_T1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.globalRun 4400 ppCS
            (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE T2 — run-form shape bridge.**  No unshaped prep exists at
budget 4400 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_T2
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalShapedT2.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.globalRun 4400 ppCS
            (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE T6 — run-form shape bridge.**  No unshaped prep exists at
budget 4400 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_T6
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalShapedT6.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.globalRun 4400 ppCS
            (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-- **LEVEL 3′, SHAPE T7 — run-form shape bridge.**  No unshaped prep exists at
budget 4400 (see §UNSHAPED-PREP-REACH), so the right-hand side is the RAW metered
CEK run on the denoted `ScriptContext`, with no optimizer in it at all. -/
theorem bridge_T7
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    isSuccessful (appliedGlobalShapedT7.prop ppCS cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
      ↔ isSuccessful
          (Runs.globalRun 4400 ppCS
            (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)) := by blaster

/-! ## §CONTROLS — the bridge verdicts are DISCRIMINATING

A bridge proved by a solver is worthless without evidence that the solver can
tell the two sides apart at all.  Each control perturbs the RIGHT-hand side by
exactly one validator-relevant decision and must come back `Falsified`.

METHODOLOGICAL WARNING, recorded because it bit this task: a perturbation that
looks like a change may be a SYMMETRY of the statement.  Swapping the shape's two
withdrawal credentials `w0 ↔ w1` on one side only comes back **`Valid`** — and
correctly so, because both are universally quantified and the base validator's
membership test is symmetric in them.  That is not a false positive; it is a
badly-chosen control.  The controls below perturb asymmetrically. -/

/-- CONTROL B1-a — the first base parameter is handed to the unshaped prep as a
PUBKEY credential (`Data.Constr 0`) instead of a SCRIPT one (`Constr 1`), so the
right side loses the `globalCred ∈ wdrl` disjunct.  Expected `Falsified`. -/
def control_B1_pubkey_param : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.PubKeyCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [control_B1_pubkey_param]

/-- CONTROL B1-b — the shape's SECOND withdrawal credential is collapsed onto the
first on the right side only, so that side's map offers strictly fewer hashes.
Expected `Falsified`. -/
def control_B1_collapsed_wdrl : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isSuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w0 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [control_B1_collapsed_wdrl]

/-- CONTROL B1-c — POLARITY.  Expected `Falsified`; a `Valid` here would mean the
bridge is being read off an accept-UNSAT class. -/
def control_B1_polarity : Prop :=
  ∀ (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedBaseShaped.prop gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)
    ↔ isUnsuccessful
      (appliedBase.prop (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [control_B1_polarity]

/-- CONTROL M1-a — SHAPE M1's two withdrawal credentials collapsed onto `w1` on
the right side only.  The `BurnOnly` arm reads the minting-logic credential out of
that map at the redeemer's index, so this is asymmetric.  Expected `Falsified`. -/
def control_M1_collapsed_wdrl : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    ↔ isSuccessful
      (appliedMinting900.prop ppCS mlh
        (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w1 w1 a0 a1 fee txid oidx lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [control_M1_collapsed_wdrl]

/-- CONTROL M1-b — the minted quantity is NEGATED on the right side only.  The
`BurnOnly` scan (Issuance.hs:251-254) is a sign test on exactly that leaf, so the
bridge must notice.  Expected `Falsified`. -/
def control_M1_negated_q : Prop :=
  ∀ (ppCS : CurrencySymbol) (mlh : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString),
    (isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)
    ↔ isSuccessful
      (appliedMinting900.prop ppCS mlh
        (mintShapedCtx ownCS tn (-q) owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee txid oidx lo hi tid)))

#blaster (gen-cex: 0) (solve-result: 1) [control_M1_negated_q]

/-- CONTROL T1 — POLARITY at the Tier-B run form, budget 4400.  Expected
`Falsified`: the run-form bridges are not being read off an empty class either. -/
def control_T1_polarity : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    (isSuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
    ↔ isUnsuccessful
      (Runs.globalRun 4400 ppCS
        (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
          dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)))

#blaster (gen-cex: 0) (solve-result: 1) [control_T1_polarity]

/-! ## §CONCRETE — one accepting instance carried across all four corners

The task's rung: take a shaped theorem's accepting witness, build the
corresponding `ScriptContext`, and check that BOTH sides accept.  SHAPE M1's
witness is used because it is the campaign's only concrete accepting instance
that is also `validMintingContext`-true (`WSC/Props/Shaped/P4Shaped.lean:294`).

The four corners are: shaped `exec`, raw `Runs.mintingRun` on the denoted
`ScriptContext` (these two are the SAME term by `exec_M1`), shaped `prop`, and —
the composition-facing one — the UNSHAPED prep's `prop` at `K_mint = 900` applied
to the denoted `ScriptContext`. -/

namespace Witness

set_option maxRecDepth 1000000

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def mlh   : ScriptHash     := ByteString.mk "MINTLOGIC"
def ownCS : CurrencySymbol := ByteString.mk "OWNCS"
def tn    : TokenName      := ByteString.mk "TOK"

/-- SHAPE M1 at `WSC/Props/Shaped/P4Shaped.lean:281`'s leaf values: burn 3 of
`OWNCS.TOK` out of an input holding 5, producing an output holding 2, 40 lovelace
fee out of 100, withdrawal map `[(Script "MINTLOGIC",0),(Script "ZZZ",0)]`. -/
def ctx : ScriptContext :=
  mintShapedCtx ownCS tn (-3) (ByteString.mk "OWNER") 100 5 (ByteString.mk "DEST") 60 2
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The instance is ledger-normalized (`validMintingContext`). -/
theorem ctx_valid : CardanoLedgerApi.V3.validMintingContext ctx = true := by native_decide

/-- CORNER 1 — the SHAPED applied term's executable form accepts. -/
theorem corner1_shaped_exec :
    isSuccessful
      (appliedMintShaped900.exec ppCS mlh ownCS tn (-3) (ByteString.mk "OWNER") 100 5
        (ByteString.mk "DEST") 60 2 (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) :=
  isHaltB_sound _ (by native_decide)

/-- CORNER 2 — the RAW metered run of the production bytecode on the
`ScriptContext` the shape denotes accepts at budget 900.  By `exec_M1` this is
the very same term as CORNER 1; both are stated so the bridge is visible on a
closed instance. -/
theorem corner2_ledger_run :
    isSuccessful (Runs.mintingRun 900 ppCS mlh ctx) :=
  isHaltB_sound _ (by native_decide)

/-- CORNER 3 — the SHAPED prep's OPTIMIZED term (what every P4 theorem
quantifies over) accepts.  `blaster`, since `.prop` is `noncomputable`. -/
theorem corner3_shaped_prop :
    isSuccessful
      (appliedMintShaped900.prop ppCS mlh ownCS tn (-3) (ByteString.mk "OWNER") 100 5
        (ByteString.mk "DEST") 60 2 (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
        (ByteString.mk "") 0 0 1 (ByteString.mk "")) := by blaster

/-- CORNER 4 — **the composition-facing corner.**  The UNSHAPED prep's optimized
term at `K_mint = 900` accepts the denoted `ScriptContext`.  This is the exact
proposition `LR_BUDGET_minting` trades against `NodeAcceptsMinting`, so
`bridge_M1` is non-vacuous where it matters. -/
theorem corner4_unshaped_prop :
    isSuccessful (appliedMinting900.prop ppCS mlh ctx) := by blaster

/-- REJECTING instance, SHAPE B1: neither base parameter is in the withdrawal
map, and the bytecode refuses — so the B1 bridge is not being read off a class on
which the validator is constant.  (`#eval` cross-check in
`WSC/Shaped/Probe/B1Accept.lean`: `w0 = "GLOBAL"` and `w0 = "SEIZE"` both accept,
`w0 = "AAA"` does not.) -/
theorem b1_rejects_when_neither_cred_present :
    isHaltB (Runs.baseRun 600 (Credential.ScriptCredential (ByteString.mk "GLOBAL"))
      (Credential.ScriptCredential (ByteString.mk "SEIZE"))
      (baseShapedCtx (ByteString.mk "") 0 (ByteString.mk "BASE") 100
        (ByteString.mk "AAA") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk "")))
      = false := by native_decide

/-- …and it ACCEPTS when the global credential IS present.  Same shape, one leaf
changed. -/
theorem b1_accepts_when_global_present :
    isSuccessful (Runs.baseRun 600 (Credential.ScriptCredential (ByteString.mk "GLOBAL"))
      (Credential.ScriptCredential (ByteString.mk "SEIZE"))
      (baseShapedCtx (ByteString.mk "") 0 (ByteString.mk "BASE") 100
        (ByteString.mk "GLOBAL") (ByteString.mk "ZZZ") 0 0 40 0 0 1 (ByteString.mk ""))) :=
  isHaltB_sound _ (by native_decide)

end Witness

/-! ## §BONUS — `GlobalNonVacuous appliedGlobal1600.prop`, DISCHARGED

Not part of the bridge, but found while building it and directly unblocking task
U2's first `LR_BUDGET_global` instantiation.

`WSC/Honest.lean`'s `GlobalNonVacuous globalProp` (U2's prep-parametric form) is
`∃ pcs ctx, validRewardingContext ctx = true ∧ isSuccessful (globalProp pcs ctx)`.
U2 records it as **NOT DISCHARGED at any global prep**, on the grounds that the
SYMBOLIC vacuity probe over `appliedGlobal1600.prop` returned no verdict in 87
minutes and that "`exec` acceptance does not transfer to `prop`"
(`WSC/Honest.lean` §GlobalNonVacuous; `WSC/Composition.lean` §9.5b).

Both observations are correct, and neither is needed: non-vacuity is an ∃, so a
**closed** goal suffices, and `blaster` on a closed goal is the idiom that already
discharges `BaseNonVacuous` (`WSC/Props/P3_Base.lean:209`).  Applied to
`WSC.P5ShapedWitness`'s SHAPE G1 context — which is `validRewardingContext`-true
with zero failing conjuncts — it closes in **< 1 s**.

Trust status: identical to `BaseNonVacuous` / `mintingNonVacuous` (a `blaster`
verdict on a fully concrete goal, `sorryAx` via `admit`).  Strictly stronger than
the `exec`-only evidence U2 had, because it is about the `prop` term itself. -/

namespace G1NonVacuity

set_option maxRecDepth 1000000

/-- The script parameter of `WSC.P5ShapedWitness` (`WSC/Props/Shaped/P5Shaped.lean:421`). -/
def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- `WSC.P5ShapedWitness.ctx` re-declared here so this module does not have to
import `WSC/Props/Shaped/P5Shaped.lean` (whose `blaster` obligations cost minutes).
SHAPE G1 at P5's leaf values: 7 of `MMM.TOK` minted and claimed exempt via
`NonMember 1`; directory node with `key = AAA`, `next = ZZZ` so `AAA < MMM < ZZZ`;
params node publishing `directoryNodeCS = DIRCS`; 200 lovelace in, 150 out, 50 fee. -/
def ctx : ScriptContext :=
  globalShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "DEST") 150 7
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

theorem ctx_valid : CardanoLedgerApi.V3.validRewardingContext ctx = true := by native_decide

/-- The UNSHAPED 1600 prep's OPTIMIZED term accepts it. -/
theorem prop_accepts_1600 : isSuccessful (appliedGlobal1600.prop ppCS ctx) := by blaster

/-- **`WSC.GlobalNonVacuous appliedGlobal1600.prop`, unfolded and PROVED.**  Stated
in unfolded form so this module need not import `WSC/Honest.lean` (which pulls
`WSC.Imports`, i.e. the 600/800/1300 minting preps).  A `Composition.lean` owner can
close the named obligation with
`theorem _ : WSC.GlobalNonVacuous appliedGlobal1600.prop := ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`. -/
theorem globalNonVacuous_at_1600 :
    ∃ (pcs : CurrencySymbol) (c : ScriptContext),
      CardanoLedgerApi.V3.validRewardingContext c = true
        ∧ isSuccessful (appliedGlobal1600.prop pcs c) :=
  ⟨ppCS, ctx, ctx_valid, prop_accepts_1600⟩

end G1NonVacuity

/-! ## §RESIDUAL — `PropExecFaithful`, stated and NOT axiomatized

This is the ONE thing the Tier-B bridges (`G6`, `L1`, `L2`, `DT1`, `DS1`, `S1`,
`T1`, `T2`, `T6`, `T7`) rest on that a Blaster verdict cannot honestly certify:
that `Optimize.main` is SEMANTICS-PRESERVING, i.e. `X.prop = X.exec` pointwise.

WHY `blaster` DOES NOT DISCHARGE IT.  `blaster` begins by running the very same
`Optimize.main` on the goal.  Presented with `isSuccessful X.prop ↔ isSuccessful
X.exec` it optimizes the right side into (a term equal to) the left, and the SMT
query it then emits is trivial.  MEASURED: the verdict is `Valid` in ≈1 s at
budget 600 and again at budget 4400 (`WSC/Shaped/Probe/BridgeProbe3.lean`,
`BridgeProbe7.lean`), a cost that is only explicable by syntactic collapse.  So
the verdict is real evidence that the optimizer is DETERMINISTIC and IDEMPOTENT —
and that is exactly what the Tier-B bridges need in practice — but it is NOT
independent evidence of faithfulness, and this module does not pretend otherwise.

WHY IT IS NOT A NEW ASSUMPTION.  The whole campaign already depends on it and
never named it: every `P*` theorem is about `.prop`, while every executable
witness, every measured `K`, and every golden replay runs `.exec`
(`WSC/Props/P3_Base.lean:202` vs `:209`; `WSC/Goldens/Witnesses.lean:143` vs
`:151`).  Those pairs are only jointly meaningful if `PropExecFaithful` holds.
U1 IDENTIFIES this dependency; it does not introduce it.

EVIDENCE FOR IT.  Each rewrite the optimizer performs has a PROVED equivalence
lemma in Blaster (`Blaster/Optimize/Decidable.lean:36` `dite_equiv`, `:43`
`ite_to_dite'_equiv`; `Blaster/Optimize/Lemmas/LemmasProp.lean:10,15,20`).  What
is missing is a reification of the COMPOSITE transformation — `Optimize.main` is
`MetaM Expr → MetaM Expr`, so there is no Lean-level function to state soundness
of.  Note also defect D6 (`WSC/Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean`),
where the optimizer emits a KERNEL-ILL-TYPED `Blaster.dite'` after a
Bool-polarity rewrite: proof that the transformation is not unconditionally
well-behaved, and a concrete reason not to axiomatize it blind.

WHAT WOULD DISCHARGE IT.  Substrate work, in decreasing order of preference:
(i) have `#prep_uplc` emit a third declaration `X.prop_eq_exec : X.prop = X.exec`
    assembled from the per-rewrite equivalence lemmas it already applies — this is
    a certificate-producing optimizer and is a small change to
    `PreProcess.lean:36-58`;
(ii) verify `Optimize.main` once and for all against a reified rewrite relation;
(iii) restrict the campaign to Tier-A budgets, where the bridge needs no such
    property at all (see `bridge_B1`/`bridge_M1`/`bridge_M2`/`bridge_G1`).

Tier A does NOT depend on this: `bridge_B1`, `bridge_M1`, `bridge_M2`,
`bridge_G1`, `bridge_GIdx`, `bridge_GNIdx` relate two `.prop`s and never mention
`.exec`. -/

/-- The residual, stated for the record.  Deliberately a `def`, not an `axiom`:
nothing in this module consumes it, and the Tier-B bridges above are stated
without it (they are `prop ↔ run`, proved by `blaster`).  It is here so that a
reader can see exactly what a Tier-B bridge means if one distrusts the
optimizer. -/
def PropExecFaithful {α : Type} (prop exec : α) : Prop := prop = exec

/-- Instances of the residual, one per validator, spelled out. -/
def PropExecFaithful_base   : Prop := PropExecFaithful @appliedBase.prop   @appliedBase.exec
def PropExecFaithful_mint   : Prop := PropExecFaithful @appliedMinting900.prop @appliedMinting900.exec
def PropExecFaithful_global : Prop := PropExecFaithful @appliedGlobal1600.prop @appliedGlobal1600.exec

/-! ## §UNSHAPED-PREP-REACH — why Tier B is Tier B

The Tier-A form of the bridge needs an UNSHAPED `#prep_uplc` at the shape's own
budget.  Measured cost of building one (this session unless stated):

| validator | budget | unshaped symbolic prep | verdict |
|---|---|---|---|
| `programmableLogicBase` | 600 | 1.0 s | Tier A |
| `programmableTokenMinting` | 600 / 900 | 11.1 s / 27.6 s (K-MEASUREMENTS §5.1) | Tier A at 900 |
| `programmableTokenMinting` | 1200 | 131.6 s (K-MEASUREMENTS §5.1) | — |
| `programmableTokenMinting` | 1700 | **never completed in 48.6 min** (K-MEASUREMENTS §5.1) | 2500 unreachable |
| `programmableLogicGlobal` | 1600 | **39 s** (measured; `lake build WSC.Prep.Global1600`) | Tier A |
| `programmableLogicGlobal` | 3300 | **did not complete in 10 min**, killed (`WSC/Shaped/Probe/UnshapedCost.lean`) | 3300 / 4400 not reached |
| `programmableSeize` | 2000 | never completed in 77 min (SPIKE-FINDINGS) | 3800 unreachable |

By contrast every SHAPED prep is cheap — measured here: B1 0.7 s, M1 0.75 s,
M2 0.81 s, G1 0.83 s, G6 1.1 s, L1 1.2 s, DT1/DS1 1.2 s, S1 3.5 s,
T1 1.0 s, T2 1.2 s, T6/T7 2.1 s.  That asymmetry is the whole reason the shaped
programme exists, and it is also exactly why Tier B cannot be lifted to Tier A by
spending more compute.

## §COVERAGE — what this module does NOT establish

The bridge is a statement of the form

    shaped theorem about σ's leaves  ⟹  statement about every ScriptContext in range σ.

It gives NO information about `ScriptContext`s outside `range σ`.  Sixteen shapes,
each pinning every list length, constructor tag and `Option` in the `Data`
skeleton, cover a finite set of transaction SKELETONS — not the set of
transactions.  Concretely, SHAPE M1 fixes "1 input, 1 output, 0 reference inputs,
2 withdrawals, 1 redeemer, redeemer tag 3"; a two-input burn is outside it.

A coverage argument would require ONE of:

1. **An enumeration with a closure argument** — a finite list of shapes
   `σ₁ … σₙ` plus a theorem
   `∀ ctx, validMintingContext ctx = true → nodeSteps … ctx ≤ K → ∃ i leaves, ctx = σᵢ leaves`.
   For that to be true the shapes would have to be parameterised over list
   LENGTHS as well as leaves, which the current `#prep_uplc` mechanism cannot do —
   baking the skeleton in is precisely what fixes the lengths.  A budget-based
   finiteness argument is conceivable (a `K`-step run can only traverse boundedly
   many list cells, so only boundedly many skeletons are distinguishable), but it
   is a meta-theorem about the CEK machine that the substrate does not have
   (SPIKE-FINDINGS: "budget monotonicity is a meta-theorem SMT doesn't have"), and
   the bound it would give is astronomically larger than sixteen.
2. **A shape-generalization lemma** — e.g. "if the validator accepts a context
   with `n` inputs then it accepts the projection onto the relevant one", which
   would let a 1-input shape stand for all `n`.  This is FALSE in general for
   these validators (the global validator's containment check aggregates over ALL
   inputs and outputs — see `WSC/Props/Shaped/P1Shaped.lean`), so it would have to
   be proved per property with genuine side conditions.
3. **Dropping to the source model** with a separately argued
   compilation-fidelity bridge (`WSC/Model/*`, which quantify over arbitrary
   contexts but carry a faithfulness axiom each).

NO SUCH ARGUMENT IS OFFERED HERE.  The honest framing stays the one ARCHITECTURE
already publishes: **bounded model checking beneath the axiomatic layer**, now
bounded in two dimensions (step budget `K`, shape `σ`) with the second dimension
formally connected to the ledger-supplied context by this module.

The coverage obligation is written down as a `Prop` so it can be pointed at, and
is NOT proved and NOT axiomatized. -/

/-- The shape-coverage obligation for the minting policy, spelled out for SHAPE
M1 alone (the full version would be a disjunction over all minting shapes).
**UNPROVED and DELIBERATELY NOT AN AXIOM** — it is false as stated for M1 alone
(a 2-input burn is a counterexample), and stating it is the point: it shows what
would have to be added to turn the shaped programme into a universal claim. -/
def M1Covers : Prop :=
  ∀ ctx : ScriptContext,
    CardanoLedgerApi.V3.validMintingContext ctx = true →
    ∃ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
      (owner : ByteString) (inAda qIn : Integer)
      (dest : ByteString) (outAda qOut : Integer)
      (w0 w1 : ScriptHash) (a0 a1 : Integer)
      (fee : Integer) (txid : ByteString) (oidx : Integer)
      (lo hi : Integer) (tid : ByteString),
      ctx = mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut w0 w1 a0 a1 fee
              txid oidx lo hi tid

/-! ## §AXIOM-AUDIT — machine-rechecked on every build

`#print axioms` on one representative of each level.  The point of the stanza is
the LEVEL-2 row: `exec_*` carries **no `sorryAx`**, so the shape bridge at the
functional level is a genuine kernel-checked theorem, not a solver verdict.

Measured output (this build):

| declaration | axioms | reading |
|---|---|---|
| `inputs_M1` | *none at all* | pure `δ`-equality |
| `exec_M1`, `exec_T1` | `propext, Classical.choice, Quot.sound` | Lean's standard three — **no `sorryAx`** |
| `bridge_M1`, `bridge_T1` | `… + sorryAx` | `blaster` closes via `admit` (campaign-wide idiom) |
| `Witness.corner2_ledger_run` | `… + Lean.ofReduceBool, Lean.trustCompiler` | `native_decide` |
| `Witness.corner4_unshaped_prop` | `… + sorryAx` | `blaster` on a closed goal |
-/

#print axioms inputs_M1
#print axioms exec_M1
#print axioms exec_T1
#print axioms bridge_M1
#print axioms bridge_T1
#print axioms Witness.corner2_ledger_run
#print axioms Witness.corner4_unshaped_prop

end ShapeBridge
end WSC
