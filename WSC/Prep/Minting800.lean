/-
WSC/Prep/Minting800.lean — import + prep of the programmableTokenMinting
(issuance) policy at CEK step budget **800**.

WHY 800 EXISTS ALONGSIDE 900. It is the SMALLEST round budget above this
validator's measured non-vacuity floor: the cheapest accepting golden,
`programmableTokenMinting.mint-burnonly`, halts in 784 CEK steps
(WSC/goldens/K-MEASUREMENTS.md §3). Two jobs:

1. It brackets the positive witnesses in WSC/Props/P4_Minting.lean from below.
   Both the hand-built `P4Witness.ctx` and the real golden `P4Golden.ctx` are
   REJECTED by the bytecode at 600 and ACCEPTED at 800, pinning their true step
   count in (600, 800] — consistent with the golden's measured 784.
2. It is the control for the solver-cost question: if the SMT wall documented in
   WSC/Props/P4_Minting.lean were simply "one budget too far", the same goal
   would close 100 steps lower. It does not — P4a is Undetermined at 800 with a
   3,300 s Z3 cap exactly as at 900 — which is what identifies the wall as the
   vacuity boundary rather than a budget-size effect.

Measured prep cost: 3.1 s under `lake build` (see WSC/Prep/Minting1300.lean for
the full native-vs-interpreted table and the correction it implies for
K-MEASUREMENTS §5.1). Prep-only module; parameter evidence is identical to
WSC/Prep/Minting900.lean's `mintingPolicyInputs900` — see that module for the
`Issuance.hs:132-133` signature, the offchain application order
(`Scripts.hs:135-140`) and the `PMintingScript` purpose (`Issuance.hs:139`).
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
#import_uplc programmableTokenMinting800 PlutusV3 double_cbor_hex "WSC/flats/programmableTokenMinting.flat"
def mintingPolicyInputs800 (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash :: mintingInputs ctx
#prep_uplc appliedMinting800 programmableTokenMinting800 mintingPolicyInputs800 800
end WSC
