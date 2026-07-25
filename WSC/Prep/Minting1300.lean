/-
WSC/Prep/Minting1300.lean — import + prep of the programmableTokenMinting
(issuance) policy at CEK step budget **1300**.

WHY 1300. It is the cheapest budget that covers the `DelegateTransfer` custody
arm: `programmableTokenMinting.mint-delegate-transfer-topup` halts in **1,257**
CEK steps (WSC/goldens/K-MEASUREMENTS.md §3). A P4 proved at 1300 therefore
ranges over accepting runs of BOTH the pure-burn shape (784) and the
delegate-transfer shape — i.e. two of the four arms are exercised rather than
one. (`mint-local-registered-by-ref` needs 1,681, so the `Local` arm still is
not; see the ARM SCOPE stanza in WSC/Props/P4_Minting.lean.)

────────────────────────────────────────────────────────────────────────────
MEASURED PREP COST — AND A CORRECTION TO K-MEASUREMENTS.md §5.1
────────────────────────────────────────────────────────────────────────────
K-MEASUREMENTS §5.1 reports the symbolic `#prep_uplc` cost of this validator as
11.1 s @600, 27.6 s @900, 131.6 s @1200 and "never completed, killed at
48.6 min" @1700, and concludes that budgets ≥ ~1700 are unreachable. Those
numbers were taken with `lake env lean <file>` (K-MEASUREMENTS §6
"Reproduction"), which loads no precompiled dynlib, so **Blaster runs in the
Lean interpreter**. `Blaster`'s lakefile sets `precompileModules := true`
(.lake/packages/Blaster/lakefile.lean:5,10), so under `lake build` the same prep
runs against `libBlaster.so` — and it is an order of magnitude cheaper.

Measured this session on the same 32-core box, warm `.lake`, `maxHeartbeats 0`:

| budget | `lake build` (native) | `lake env lean` (interpreted) |
|---|---|---|
| 600  | (cached)  | 11.1 s (K-MEASUREMENTS) |
| 900  | **1.5 s** | **23.9 s** (reproduces K-MEASUREMENTS' 27.6 s) |
| 1300 | **7.4 s** | — |
| 1700 | **92.7 s** | >48.6 min, never completed (K-MEASUREMENTS) |
| 2000 | **never completed — killed by `timeout 1800`** | — |

So the prep wall is real but sits ~300 budget steps higher than published, and
the affordable ceiling for this validator is **1700 (92.7 s), with 2000 dead**.
Every prep budget the WSC library needs for minting is therefore affordable;
what is NOT affordable is the SMT solve at those budgets (see
WSC/Props/P4_Minting.lean's SOLVER COST stanza). Correcting §5.1's methodology
note is left to the owner of that document; this module records the
measurements.

This module is prep-only and carries no probe, so its cost is exactly the prep.
Provenance of the flat: WSC/flats/PROVENANCE.md.
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol ScriptHash mintingInputs)
open PlutusCore.UPLC.Term (Term)

set_option maxHeartbeats 0

#import_uplc programmableTokenMinting1300 PlutusV3 double_cbor_hex "WSC/flats/programmableTokenMinting.flat"

/-- Parameter evidence: identical to `WSC/Prep/Minting900.lean`'s
`mintingPolicyInputs900` — see that module's doc comment for the
`Issuance.hs:132-133` signature, the offchain application order
(`Scripts.hs:135-140`) and the `PMintingScript` purpose (`Issuance.hs:139`). -/
def mintingPolicyInputs1300 (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash :: mintingInputs ctx

#prep_uplc appliedMinting1300 programmableTokenMinting1300 mintingPolicyInputs1300 1300

end WSC
