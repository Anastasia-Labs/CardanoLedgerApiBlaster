/-
WSC/Prep/GlobalImport.lean — the DECODE-ONLY module for the production
`programmableLogicGlobal` (transfer) validator, at wsc-poc main @ 2306678
(PR #112).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS (task N4, 2026-07-28) — it unblocks defect D8
════════════════════════════════════════════════════════════════════════════
Before this split, `WSC/Prep/Global1600.lean` did TWO things in one module:

1. `#import_uplc programmableLogicGlobal1600` — decode the flat; and
2. `#prep_uplc appliedGlobal1600 … 1600` — the FULLY-SYMBOLIC (unshaped) prep.

Every `WSC/Shaped/Global*Prep.lean` imported that module, but every one of them
needs only (1): they run their OWN `#prep_uplc` over their OWN shaped inputs
function and never mention `appliedGlobal1600`.

Against the PR #112 bytecode step (2) FAILS — defect **D8**, reported by unit N1
(WSC/IMPACT-PR112.md §6.2): after ~8 minutes the Blaster optimizer emits a
kernel-ill-typed `Blaster.dite'` whose branch polarities disagree
(`Bool.true = eqDataMap …` supplied where `¬ Bool.true = eqDataMap … → State`
is expected). Because (1) and (2) shared a module, that failure took the entire
shaped global chain — and therefore P1, P5 and P6 — down with it, even though
none of those results depends on the unshaped prep.

Splitting the `#import_uplc` out confines D8 to `WSC/Prep/Global1600.lean`.
**This is an isolation of the defect, not a fix for it**, and it is not a
soundness shortcut: the shaped preps were never consumers of `appliedGlobal1600`,
so nothing that previously depended on the unshaped prep now silently depends on
less. The unshaped prep and the theorems stated against it remain BLOCKED and are
reported as such.

DECODE GATE (re-run at 2306678, task N4). The `#import_uplc` below reports
`Successfully decoded double CBOR hex`. The PR #112 global flat is a DIFFERENT
program from the one the pre-#112 results were proved against — sha256 of the
exported cborHex moved `ddd6f7df4278…` → `eed62d595f56…`, 6880 → 5624 bytes
(WSC/flats/PROVENANCE.md). Anything proved against the old bytes is not a
statement about this program.

CIP-153 SUBSTRATE PIN (ADDENDUM E11). This validator uses the CIP-153 Value
builtins, so it decodes ONLY against the CIP-153-capable PlutusCoreBlaster
(branch `cip153-value-builtins` @ 9f9ca8c, pinned by lakefile.lean as a LOCAL
path). Against PCB `main` @ 4ef4860 the same flat fails with "Could not decode
program!". Note that the global flat decodes fine; it is the SEIZE flat that
additionally needs `ScaleValue` (flat tag 100), which PCB does not yet have —
defect D7/N2 §4, out of scope for this unit.

Provenance of the flat: WSC/flats/PROVENANCE.md.
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs)
open PlutusCore.UPLC.Term (Term)

#import_uplc programmableLogicGlobal1600 PlutusV3 double_cbor_hex "WSC/flats/programmableLogicGlobal.flat"

/-- Parameter evidence for `programmableLogicGlobal` — 1 parameter, then ctx
**Line citations re-read at wsc-poc main @ 2306678 (task N4)** — they moved with
PR #112 and the pre-#112 numbers no longer resolve.

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.

* Plutarch signature: `mkProgrammableLogicGlobal :: Term s (PAsData
  PCurrencySymbol :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1180
  (lambda order `\protocolParamsCS ctx` at :1181). The parameter list is
  UNCHANGED by PR #112; only the redeemer type gained a field.
* Offchain application: `mkProgrammableLogicGlobal # pdata (pconstant $
  transPolicyId paramsPolId)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:119-122.
* Golden corroboration: all four `programmableLogicGlobal.*` vectors in
  WSC/goldens/ carry exactly ONE `paramsHex` entry (MANIFEST.md param table).
* Purpose: REWARDING (withdraw-zero) validator — `pisRewardingScript` is a
  validated condition of the `PTransferAct` arm (ProgrammableLogicBase.hs:1276).
  Note PR #112 moved seize OUT of this validator: the `PSeizeAct` arm is now a
  hard error (:1290-1291), so this program handles transfers only. -/
def globalInputs1600 (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

end WSC
