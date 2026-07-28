-- ✅ RE-PROVED AT PR #112 (task N5, wsc-poc main 2306678). Current. See WSC/IMPACT-PR112.md §N5.
/-
WSC/Prep/Seize.lean — import + prep of the programmableSeize validator.
Split into its own module so the `#prep_uplc` elaboration is cached
per-validator. Provenance: WSC/flats/PROVENANCE.md.

BUDGET NOTE (E2 spike, 2026-07-24): fully-symbolic `#prep_uplc` on this
bytecode is empirically intractable at accept-capable budgets (>=2000 never
completed in >75 min wall on 32 cores; 600 takes ~11 s). This module preps at
600 ONLY to validate the import/apply pipeline end-to-end. The E2 vacuity
probe proved there is NO accepting context within 600 steps, so no P-theorem
may be stated against `appliedSeize` from this module — P2 uses SHAPED
contexts (fixed input/output spines, concrete SeizeAct redeemer skeleton,
symbolic scalars) with per-shape measured budgets; see WSC/props/P2_Seize.lean
and ARCHITECTURE.md ADDENDUM E1/E2.
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs)
open PlutusCore.UPLC.Term (Term)

#import_uplc programmableSeize PlutusV3 double_cbor_hex "WSC/flats/programmableSeize.flat"

/-- Parameter evidence for `programmableSeize` — 1 parameter, then ctx:

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.

* Plutarch signature: `mkProgrammableSeize :: Term s (PAsData PCurrencySymbol
  :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1290
  (lambda order `\protocolParamsCS ctx` at :1291).
* Offchain application: `mkProgrammableSeize # pdata (pconstant $ transPolicyId
  paramsPolId)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:114-117.
* Purpose: REWARDING (withdraw-zero) validator — first validated condition is
  `pisRewardingScript` (ProgrammableLogicBase.hs:1321). -/
def seizeInputs (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

#prep_uplc appliedSeize programmableSeize seizeInputs 600

end WSC
