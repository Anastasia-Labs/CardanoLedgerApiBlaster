/-
WSC/Shaped/Probe/GPrepT2400.lean — PARTIAL-SKELETON `#prep_uplc` EXPERIMENT
(2026-08-02): the untested middle between "unshaped" and "shaped".

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT. Build deliberately, and ONLY under a
hard memory cap (`ulimit -v` ≥ 40 GiB advised; see CostG2300.lean's header for
what an uncapped run of this validator's prep did to the box):

    lake build WSC.Shaped.Probe.GPrepT2400

THE HYPOTHESIS UNDER TEST. The two measured regimes of `#prep_uplc` on this
validator are the extremes:

  * fully symbolic ctx: completes at 1600 (≤4.35 GB), memory-cliff OOM at
    2200/2300 (21.6/27.4 GB capped; 46 GB uncapped) — CostG2200/2300.lean;
  * fully closed skeleton (SHAPE T1R, ~40 scalar leaves): **1.51 s at 4400**.

Nothing in between has ever been measured. This module preps over a PARTIAL
skeleton chosen to remove exactly the forking the pure-transfer accept path
does not need, while leaving every list spine of the transaction symbolic:

  * redeemer = `Constr 0 [f1, f2, f3, f4, I 0]` — the raw 5-field TransferAct
    spine, fields SYMBOLIC, `paramsRefIdx = 0` LITERAL (a symbolic index makes
    the params `pdropList` fork per index value, and SHAPING-RESULTS §2.4/G3
    already showed free indices are load-bearing for this validator);
  * `txInfoMint := []` — kills the mint walk (`mintedEntries` is empty, so the
    per-proof directory-node forking never starts). K_T1R = 2343 shows real
    accepting pure transfers live in this class — mint-carrying transfers are
    OUT of scope for this prep, exactly as they are for SHAPE T1R;
  * purpose = `RewardingScript cred`, `cred` symbolic — removes the
    inputs-function's purpose fork;
  * EVERYTHING ELSE SYMBOLIC: the whole `TxInfo` via `{ tin with … }` (inputs,
    reference inputs, outputs, withdrawals, redeemer map, signatories, … — no
    list length, no `Data` skeleton below the two pins above).

BUDGET 2400 > K_T1R = 2343 (`WSC.P1RShapedWitness.K_T1R_is_2343`), so the
class contains a real accepting pure transfer and any `accept → POST` theorem
stated against this prep is non-vacuous — the first prerequisite for an
unshaped-spine P1 containment stanza (conclusion vocabulary:
WSC/Benchmark/P1LkVocab.lean, which exists for exactly that statement).

OUTCOME SEMANTICS: if this completes at ANY cost, the partial-skeleton route
is alive and the next step is the containment stanza against
`appliedGlobalT2400.prop`. If it hits the same memory cliff as the unshaped
preps, the middle regime is dead too and P1-unshaped is gated ENTIRELY on
upstream unroller memory work (Lean-blaster#138).

MEASURED (2026-08-02, `ulimit -v` 42 GiB): **`INTERNAL PANIC: out of memory`
— 1093 s ≈ 18 min, MaxRSS 34.7 GB.** The pins bought a later death than
unshaped@2300 (13 min / 27.4 GB) at a HIGHER budget, but the cliff still wins.
Interpretation: with the dispatch and mint-walk forking removed, the driver
must live in what remained symbolic — the input/output LIST SPINES and the
VALUE MAPS inside them (CIP-153 aggregation loops). The next lattice point,
GPrepT2400B.lean, pins the spines (2 in / 2 out) and keeps the values
symbolic, to separate those two suspects.
-/
import WSC.Prep.GlobalImport
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext ScriptInfo TxInfo Credential CurrencySymbol
                          rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)

/-- Partial-skeleton inputs: TransferAct redeemer spine with `paramsRefIdx = 0`
literal and fields symbolic, empty mint, Rewarding purpose with symbolic
credential, all else the fully symbolic `tin`. -/
def globalInputsT2400 (protocolParamsCS : CurrencySymbol)
    (f1 f2 f3 f4 : Data) (tin : TxInfo) (cred : Credential) : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      ⟨{ tin with txInfoMint := [] },
       Data.Constr 0 [f1, f2, f3, f4, Data.I 0],
       .RewardingScript cred⟩

#prep_uplc appliedGlobalT2400 programmableLogicGlobal1600 globalInputsT2400 2400

end WSC
