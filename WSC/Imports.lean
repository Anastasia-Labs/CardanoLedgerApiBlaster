/-
WSC/Imports.lean — aggregation of the imported + prepped production
validators (arch §0.1 idiom, §3 budgets; flats provenance in
WSC/flats/PROVENANCE.md).

The actual `#import_uplc` / `#prep_uplc` commands live in one module per
validator under WSC/Prep/ so each expensive prep elaboration is cached
independently:

* WSC/Prep/Base.lean    — `appliedBase`    (spending,  budget 600)
* WSC/Prep/Minting.lean — `appliedMinting` (minting,   budget 2000)
* WSC/Prep/Seize.lean   — `appliedSeize`   (rewarding, budget 9000)

The .flat files are the raw TextEnvelope `cborHex` strings of the UNAPPLIED
production scripts, so `double_cbor_hex` is the correct decoder (TextEnvelope
cborHex = CBOR bytestring wrapping the CBOR-wrapped flat program). Parameter
count/order/type evidence (Plutarch `mk*` signature + offchain application
site, file:line) is documented above each inputs function in those modules.
-/
import WSC.Prep.Base
import WSC.Prep.Minting
import WSC.Prep.Seize

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs)
open PlutusCore.UPLC.Term (Term)

-- ==== programmableLogicGlobal (REWARDING validator; blocked on CIP-153, U5) ====

-- The GLOBAL (transfer) validator uses the CIP-153 Value builtins
-- (insertCoin/unValueData/valueData/unionValue/valueContains); the current
-- PlutusCoreBlaster flat decoder has builtin tags 94–99 commented out in
-- FlatEncoding/Basic.lean, so this import FAILS TO DECODE ("Could not decode
-- program!", verified 2026-07-24) until the CIP-153 builtins land in
-- PlutusCoreBlaster (task U5). Uncomment then:
-- #import_uplc programmableLogicGlobal PlutusV3 double_cbor_hex "WSC/flats/programmableLogicGlobal.flat"

/-- Parameter evidence for `programmableLogicGlobal` — 1 parameter, then ctx:

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.

* Plutarch signature: `mkProgrammableLogicGlobal :: Term s (PAsData
  PCurrencySymbol :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1176
  (lambda order `\protocolParamsCS ctx` at :1177).
* Offchain application: `mkProgrammableLogicGlobal # pdata (pconstant $
  transPolicyId paramsPolId)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:119-122.
* Purpose: REWARDING (withdraw-zero) validator — `pisRewardingScript` is the
  first validated condition (ProgrammableLogicBase.hs:1254).

Kept ready for U5; the matching prep will be
`#prep_uplc appliedGlobal programmableLogicGlobal globalInputs <budget>` once
the CIP-153 builtins decode. -/
def globalInputs (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

end WSC
