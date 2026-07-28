/-
WSC/Prep/Base.lean — import + prep of the programmableLogicBase validator.
Split into its own module so the (expensive) `#prep_uplc` elaboration is
cached per-validator. Provenance: WSC/flats/PROVENANCE.md.

RE-BASED ON wsc-poc `main` @ 2306678 (PR #112) by task N3.  The flat is the
POST-#112 one (`sha256 a9e7364b519a…`, 192 hex chars); the pre-#112 flat
(`1881821b7a2c…`, 260 hex chars) is gone from `main`.  What changed on the
validator side, and what it means for this prep, is in the parameter-evidence
docstring below and in `WSC/Props/P3_Base.lean`.
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
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:711
  (lambda order `\globalCred seizeCred ctx` at :712).  **Line numbers are at
  wsc-poc `main` @ 2306678**; pre-#112 they were :722 / :723.
* Offchain application order: `mkProgrammableLogicBase # pdata (pconstant $
  transStakeCredential globalCred) # pdata (pconstant seizeCred)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:100-109.
  **Unchanged by #112** — the parameter list and its order are exactly as
  before, which is why this inputs function needed no edit.
* Purpose: base SPENDING script of programmable-token UTxOs (forwards to the
  global/seize withdrawal) — ProgrammableLogicBase.hs:711-733.

**WHAT #112 CHANGED, and it is not cosmetic.**  The pre-#112 body ignored its
redeemer entirely and SCANNED `txInfoWdrl` for either parameter.  The post-#112
body READS ITS REDEEMER: it reaches field 1 of the `ScriptContext` constructor
(`scriptContextRedeemer`) with `pasConstr`, uses the constructor TAG to select
`globalCred` (tag 0 = `SpendViaGlobal`) or `seizeCred` (any other tag —
`ProgrammableLogicBase.hs:729` is a `pif` on `tag #== 0`, not an exhaustive
match), and uses the tag's single `Integer` field as an INDEX into the
credential-sorted withdrawal map (`pdropList` on the map, reached in turn by
`pdropList 6` on the `TxInfo` fields) — :712-733.  The redeemer type is new:
`data BaseSpendRedeemer = SpendViaGlobal Integer | SpendViaSeize Integer`
(:704-707), `makeIsDataIndexed [('SpendViaGlobal,0),('SpendViaSeize,1)]`
(:709); mirrored in Lean as `WSC.BaseSpendRedeemer` (`WSC/Redeemer.lean:99-111`).

CONSEQUENCE FOR THIS PREP: `spendingInputs ctx` already serialises the WHOLE
`ScriptContext`, including `scriptContextRedeemer`, so the inputs function is
unchanged and correct for the new body — but a context whose
`scriptContextRedeemer` is not a `Constr` now makes the validator ERROR where
before it was ignored.  Any pre-#112 context literal carrying `Data.I …` as its
redeemer is therefore a REJECTING context now, not an accepting one.  (Measured:
`WSC.P3Witness.ctx` had `Data.I 0` and had to be re-cut — see
`WSC/Props/P3_Base.lean`.)

`PAsData PCredential` arguments are Data-encoded credentials, so the Lean-side
type is `Credential` (IsData: Constr 0/1 [B bytes] —
CardanoLedgerApi/V1/Credential.lean:105-113, matching PlutusLedgerApi). -/
def baseInputs (globalCred seizeCred : Credential) (ctx : ScriptContext) : List Term :=
  toTerm globalCred :: toTerm seizeCred :: spendingInputs ctx

/-! Prep budget 600 — unchanged from pre-#112, and re-justified against the new
bytecode: the post-#112 base validator's accepting run costs **K = 194** CEK
steps on the regenerated golden `base-spend-transfer-tx`
(`WSC/goldens/K-MEASUREMENTS.md` §3, task N2; it was 208 pre-#112) and **194**
on each of the two in-library bootstrap witnesses of `WSC/Props/P3_Base.lean`.
600 is 3.1× that. -/
#prep_uplc appliedBase programmableLogicBase baseInputs 600

end WSC
