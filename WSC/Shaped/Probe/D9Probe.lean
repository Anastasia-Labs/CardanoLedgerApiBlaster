/-
WSC/Shaped/Probe/D9Probe.lean — **DEFECT D9 BISECTION** (task N4, 2026-07-28).

WHAT D9 IS. Against the PR #112 global bytecode, solver stanzas over the
mint-side shapes die with

    Unexpected smt error: (error "… Overflow encountered when expanding vector")

instead of returning a verdict. All four solver stanzas of
`WSC/Props/Shaped/P6ShapedR.lean` (both theorems and BOTH mandatory probes) fail
this way, so P6 currently has no verdict at all.

D9 is NOT defect D6 and is NOT caused by D6's fix. D6 was a KERNEL type error
raised by `addDecl` on the optimizer's output; the goals never reached the
solver. D9 is raised by the SMT backend on a goal that now translates fine. The
D6 fix is what lets these goals get far enough to hit D9.

WHAT THIS MODULE TESTS. The hypothesis is that D9 comes from the CIP-153
`unionValue` 128-bit `Quantity` range guard (the `±2^127` bounds visible in D6's
own error text), which PR #112 introduced on the transfer validator's MINT-MERGE
path (`ProgrammableLogicBase.hs:1245-1268`) where the old code used a hand-rolled
sorted walk. If that is right, the split is exactly:

* shapes whose `txInfoMint` is EMPTY take the `pnull` branch at
  `ProgrammableLogicBase.hs:1227-1229`, never reach `punionValue`, and should
  solve normally — SHAPES **T1R** and **T8R**;
* shapes with a NONZERO mint take the builtin merge and should hit D9 — SHAPES
  **G1R** (P5's), **G6R** (P6's), T2R, T7R.

Both probes below are the MANDATORY vacuity probes for their shapes stated at
their own prep terms, so this module earns its keep twice: it bisects D9, and
whatever it returns is point (b) of the four-point bar for T1R and T8R.

Deliberately imports NOTHING from `WSC.Props.*` or `WSC.Honest`, so it is
independent of defect D7 (the seize flat does not decode, blocking
`WSC.Runs` → `WSC.Honest` → `P1_Transfer`/`P5_NonMember`). That is the only
reason the P1-side shapes can be exercised at all right now.

EXPECTED for both: `✅ Expected Falsified` — an accepting context exists inside
the budget.
-/
import WSC.Shaped.GlobalShapedP1RPrep
import WSC.Shaped.GlobalShapedP1SOwnPrep
import WSC.Shaped.GlobalShapedRPrep
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (CurrencySymbol validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **MANDATORY VACUITY PROBE, SHAPE T1R** (empty mint). Expected `Falsified`. -/
def D9_T1R_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer),
    validRewardingContext
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT1R.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [D9_T1R_vacuity]

/-- **MANDATORY VACUITY PROBE, SHAPE T8R** (empty mint, SCRIPT-owned mini-ledger
input — PR #112's new indexed owner-witness path). Expected `Falsified`. -/
def D9_T8R_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol) (cs tn plc sOwn : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 w2 : ByteString) (a0 a1 a2 rBase rTls rOwn fee : Integer),
    validRewardingContext
      (p1SOwnCtx cs tn plc sOwn inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 w2 a0 a1 a2 rBase rTls rOwn fee) →
    ¬ isSuccessful
      (appliedGlobalShapedT8R.prop ppCS cs tn plc sOwn inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 w2 a0 a1 a2 rBase rTls rOwn fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [D9_T8R_vacuity]

/-- **THE D9 POSITIVE CONTROL, SHAPE G1R** (NONZERO mint — P5's own shape). If
the hypothesis in this module's header is right, THIS one raises the SMT
"Overflow encountered when expanding vector" error while the two above return
verdicts. -/
def D9_G1R_vacuity : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer) (fee : Integer),
    validRewardingContext
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) →
    ¬ isSuccessful
      (appliedGlobalShapedG1R.prop ppCS cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 a0 rMint fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [D9_G1R_vacuity]

end WSC
