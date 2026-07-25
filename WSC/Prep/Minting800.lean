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
