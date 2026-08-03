/-
WSC/Shaped/Probe/GPrepT2400B.lean — PARTIAL-SKELETON `#prep_uplc`, lattice
point 2 (2026-08-02). Read GPrepT2400.lean's header first.

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT. Build ONLY under `ulimit -v`:

    lake build WSC.Shaped.Probe.GPrepT2400B

Lattice point 1 (GPrepT2400.lean — redeemer spine + empty mint + purpose
pinned, ALL list spines symbolic) died on the same memory cliff as the
unshaped preps (34.7 GB @ 18 min, budget 2400). Two suspects remain for the
fork explosion: the transaction's LIST SPINES (inputs/outputs/refInputs/wdrl,
symbolic length ⟹ the aggregation loops fork per element) and the VALUE MAPS
inside each output (symbolic `Data` maps ⟹ the CIP-153 union/lookup recursion
forks per slot).

THIS MODULE separates them: everything point 1 pinned, PLUS

  * `txInfoInputs := [i1, i2]`            — spine closed, `TxInInfo`s symbolic
  * `txInfoOutputs := [o1, o2]`           — spine closed, `TxOut`s symbolic
  * `txInfoReferenceInputs := [pIn, nIn]` — spine closed, entries symbolic
  * `txInfoWdrl := [w1, w2]`              — spine closed, entries symbolic

i.e. a 2-in/2-out/2-ref/2-wdrl pure transfer whose values, datums, credentials
and redeemer fields are ALL still symbolic. This is the T1R TOPOLOGY with none
of T1R's closed `Data` skeletons — if it preps, a containment stanza over it
covers every value/datum/credential assignment at that topology, which is
strictly and massively more general than SHAPE T1R's ~40 scalar leaves.

If it OOMs: the driver is the value-map recursion itself, every remaining
lattice point converges to the closed shape, and the middle regime is dead —
P1-unshaped is then gated entirely on upstream unroller memory
(Lean-blaster#138), measured three ways.

Budget 2400 > K_T1R = 2343: the T1R witness class inhabits this topology
(2 inputs, 2 outputs, params+node reference inputs, 2 withdrawal entries), so
non-vacuity is inherited if the prep lands.

MEASURED (2026-08-02, `ulimit -v` 42 GiB): **`INTERNAL PANIC: out of memory`
— 6809 s ≈ 113 min, MaxRSS 32.5 GB.** Closing every transaction list SPINE
bought a 6× longer runway than lattice point 1 (18 min) at the same budget,
but the same cliff wins. VERDICT OF THE BISECTION: the explosion driver is the
recursion over the symbolic VALUE MAPS / datum `Data` inside the (now
spine-pinned) entries — the last symbolic dimension standing — and every
further lattice point converges to SHAPE T1R itself. The middle prep regime
is DEAD on 61 GB hardware, measured three ways (unshaped @2200/@2300, pins
@2400 ×2). P1-unshaped is gated entirely on upstream unroller memory work
(Lean-blaster#138); see WSC/PREP-MEMORY-CLIFF.md for the consolidated hand-off.
-/
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (ScriptContext ScriptInfo TxInfo TxInInfo Credential
                          CurrencySymbol rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)

/-- Lattice point 2: point 1's pins + all four transaction list SPINES closed
at the T1R topology (2/2/2/2), every structure inside them symbolic. -/
def globalInputsT2400B (protocolParamsCS : CurrencySymbol)
    (f1 f2 f3 f4 : Data)
    (i1 i2 : TxInInfo) (o1 o2 : TxOut) (pIn nIn : TxInInfo)
    (w1 w2 : Credential × Integer)
    (tin : TxInfo) (cred : Credential) : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      ⟨{ tin with
           txInfoInputs := [i1, i2]
         , txInfoReferenceInputs := [pIn, nIn]
         , txInfoOutputs := [o1, o2]
         , txInfoMint := []
         , txInfoWdrl := [w1, w2] },
       Data.Constr 0 [f1, f2, f3, f4, Data.I 0],
       .RewardingScript cred⟩

#prep_uplc appliedGlobalT2400B programmableLogicGlobal1600 globalInputsT2400B 2400

end WSC
