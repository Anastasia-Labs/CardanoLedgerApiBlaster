/-
WSC/Prep/Base.lean — import + prep of the programmableLogicBase validator.
Split into its own module so the (expensive) `#prep_uplc` elaboration is
cached per-validator. Provenance: WSC/flats/PROVENANCE.md.
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext Credential spendingInputs)
open PlutusCore.UPLC.Term (Term)

#import_uplc programmableLogicBase PlutusV3 double_cbor_hex "WSC/flats/programmableLogicBase.flat"

/-- Parameter evidence for `programmableLogicBase` — 2 parameters, then ctx:

1. `globalCred : PAsData PCredential` — global (transfer) rewarding credential.
2. `seizeCred  : PAsData PCredential` — standalone seize rewarding credential.

* Plutarch signature: `mkProgrammableLogicBase :: Term s (PAsData PCredential
  :--> PAsData PCredential :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:722
  (lambda order `\globalCred seizeCred ctx` at :723).
* Offchain application order: `mkProgrammableLogicBase # pdata (pconstant $
  transStakeCredential globalCred) # pdata (pconstant seizeCred)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:100-109.
* Purpose: base SPENDING script of programmable-token UTxOs (forwards to the
  global/seize withdrawal) — ProgrammableLogicBase.hs:701-735.

`PAsData PCredential` arguments are Data-encoded credentials, so the Lean-side
type is `Credential` (IsData: Constr 0/1 [B bytes] —
CardanoLedgerApi/V1/Credential.lean:105-113, matching PlutusLedgerApi). -/
def baseInputs (globalCred seizeCred : Credential) (ctx : ScriptContext) : List Term :=
  toTerm globalCred :: toTerm seizeCred :: spendingInputs ctx

#prep_uplc appliedBase programmableLogicBase baseInputs 600

end WSC
