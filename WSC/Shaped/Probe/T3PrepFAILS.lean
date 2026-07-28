/-
WSC/Shaped/Probe/T3PrepFAILS.lean — **REGRESSION TEST for upstream Blaster
defect D6. THE FILENAME IS HISTORICAL: THIS MODULE NOW BUILDS.**

It is retained under its old name because ~20 files across `WSC/` cite it by
path; renaming it would churn modules owned by other units for no proof value.
Read the name as "the module that used to fail".

════════════════════════════════════════════════════════════════════════════
WHAT IT USED TO DO, AND WHAT CHANGED (task N6, 2026-07-28)
════════════════════════════════════════════════════════════════════════════
SHAPE T3 (`WSC/Shaped/GlobalShapedP1.lean:476`) is SHAPE T1 with TWO token names
per policy, so `poutputsContainExpectedValueAtCred`'s dispatch
(`ProgrammableLogicBase.hs:676-699`) leaves the single-asset scan (PATH A, which
SHAPES T1/T2/T6/T7 exercise) and takes `checkWholesaleThenBuiltin` — PATH B
(wholesale `Data` equality, :648-674) falling through to PATH C (builtin
`pvalueContains`, :619-647).

Until 2026-07-28 `#prep_uplc` produced a residual that was SEMANTICALLY CORRECT
but KERNEL-ILL-TYPED:

    (kernel) application type mismatch
      Blaster.dite' (true = PlutusCore.Value.containedInner … ) (fun x => Halt) (fun x => Error)
    argument has type    false = containedInner … → State
    but function has type (¬true = containedInner … → State) → State

i.e. the optimizer rewrote the ELSE branch's binder TYPE (`¬(true = b)` ⇝
`false = b`) without updating the `Blaster.dite'` motive — defect **D6**.

**D6 IS FIXED** in Blaster `wsc-d6-dite-branch-retype` @ `4d320dd`
(`Blaster/Optimize/Rewriting/OptimizeITE.lean`, task N5): `optimizeDITE` now
rebuilds BOTH branch binder types from the final condition. MEASURED at that
commit, warm:

    lake build WSC.Shaped.Probe.T3PrepFAILS   -> exit 0, 0 errors, 2.4 s
    lake build WSC.Shaped.Probe.T4PrepFAILS   -> exit 0, 0 errors, 9.4 s

so this module and `T4PrepFAILS.lean` are now REGRESSION TESTS: if D6 ever
returns, they go red again.

════════════════════════════════════════════════════════════════════════════
WHAT THIS DOES AND DOES NOT BUY THE CAMPAIGN — READ BEFORE QUOTING
════════════════════════════════════════════════════════════════════════════
**RETRACTED.** The previous version of this docstring ended:

> CONSEQUENCE FOR THE CAMPAIGN: PATHS B and C of the containment dispatch are
> NOT reachable at UPLC with this substrate, at any shape […] ARCHITECTURE.md
> Tier 3.1's "all three paths" therefore stands at 1 of 3 at UPLC.

**That claim is now FALSE and is withdrawn.** The prep completes, the residual is
kernel-well-typed, and SHAPE T3's accept class is NON-EMPTY — `T3_vacuity_probe`
below returns `✅ Expected Falsified` in ≈ 4.6 s, i.e. Z3 exhibits a model in
which the post-#112 bytecode ACCEPTS at a shape that reaches Path B/C. Paths B
and C are reachable at UPLC.

**BUT NO P1 RESULT AT T3 IS CLAIMED, AND ONE SHOULD NOT BE STATED HERE AS THINGS
STAND.** SHAPE T3 is a PRE-RE-CUT shape and is *provably unbuildable* on a real
node, exactly like the old SHAPES T1/T2 before the C1/C2 re-cut (audit **F2**).
Counted from the builder:

  * script inputs  : 1  (input 0 at `.ScriptCredential plc`, :437-439)
  * mint policies  : 0  (`txInfoMint := []`, :467)
  * script wdrls   : 2  (`p1ShapedWdrl w0 w1 a0 a1`, :250-251)
  * ⇒ Conway's `hasExactSetOfRedeemers` requires 1 + 0 + 2 = **3** redeemer
    entries; T3 supplies **1** (`txInfoRedeemers := [(.Rewarding …w0…, …)]`, :466).

So a P1 theorem at T3 today would live over an EMPTY class of node-realizable
transactions and would be worth nothing — which is precisely the trap the re-cut
campaign exists to avoid.

**THE HONEST STATUS OF PATHS B/C** was therefore: *no longer blocked by the
substrate; blocked only by the absence of a re-cut.* — **AND THAT RE-CUT NOW
EXISTS (task H2, 2026-07-28).** SHAPE **T3R** is SHAPE T3 with two further
redeemer entries so the map is exact (`WSC/Shaped/GlobalShapedP1BC.lean` §1); its
prep is `appliedGlobalShapedT3R` at the same budget 4400
(`WSC/Shaped/GlobalShapedP1BCPrep.lean`), and P1 is proved over it for BOTH token
names to the full four-point bar in `WSC/Props/Shaped/P1ShapedBC.lean`, together
with the executable evidence that PATH A is excluded and PATH C is executed.
SHAPE T4R does the same for `T4PrepFAILS.lean`'s shape.

**THIS MODULE IS THEREFORE A REGRESSION TEST AND NOTHING ELSE.** Nothing here is
a P1 result; the probe below is retained because it is the historical measurement
that the accept class was non-empty BEFORE the re-cut existed, and because a
returning D6 must go red somewhere. Quote `WSC/AUDIT.md` entry **H2**, not this
file, for the dispatch-path status.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.Global1600
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (CurrencySymbol validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

#prep_uplc appliedGlobalShapedT3 programmableLogicGlobal1600 p1ShapedTwoInputs 4400

/-! ## The evidence that Paths B/C are genuinely reachable (task N6)

A prep that merely COMPLETES proves only that the optimizer stopped crashing. It
does not prove the residual is satisfiable, and a residual nobody can satisfy is
the classic vacuous green tick this library's four-point bar exists to catch. So
the claim above is backed by a probe at T3's OWN prep term and OWN shape.

MEASURED: `✅ Expected Falsified` in ≈ 4.6 s — an accepting context exists inside
the 4400-step budget, so Path B/C's accept class is not empty. -/
def T3_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn0 tn1 : ByteString)
    (plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (p1ShapedTwoCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT3.prop ppCS cs tn0 tn1 plc owner inAda qIn0 qIn1
        ext in2Ada qX0 qX1 outAda qOut0 qOut1 dest escAda qE0 qE1
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [T3_vacuity_probe]

end WSC
