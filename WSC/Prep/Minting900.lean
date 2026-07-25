/-
WSC/Prep/Minting900.lean — import + prep of the programmableTokenMinting
(issuance) policy at CEK step budget **900**, the budget P4/P4a are proved at
(WSC/Props/P4_Minting.lean).

WHY A SECOND MODULE (900) ALONGSIDE WSC/Prep/Minting.lean (600). 600 is
provably VACUOUS for this validator: the cheapest accepting golden,
`programmableTokenMinting.mint-burnonly`, halts in **784** CEK steps
(WSC/goldens/K-MEASUREMENTS.md §3), so no accepting context exists within 600
steps and every `accept → POST` theorem there is empty. 900 > 784 clears that
floor with margin while staying affordable: measured symbolic prep cost is
11.1 s @600, **27.6 s @900**, 131.6 s @1200, and >48.6 min (never completed)
@1700 (K-MEASUREMENTS §5.1). The 600 module is kept, unchanged, because
`WSC/Imports.lean` and the pipeline-validation story depend on it.

SCOPE CONSEQUENCE (binding, ADDENDUM E1 — and read this before quoting any
theorem proved against `appliedMinting900`): 900 steps admits the burn-only
accepting shape (784) and NOT the custody-arm shapes — `mint-delegate-transfer-topup`
needs 1,257 steps and `mint-local-registered-by-ref` needs 1,681
(K-MEASUREMENTS §3). So the P4 disjunction proved here is non-vacuous, but the
only accepting shape it actually ranges over is the pure burn. The Local /
DelegateTransfer / DelegateSeize arms are NOT exercised at this budget. See the
"ARM SCOPE" stanza in WSC/Props/P4_Minting.lean.

Provenance of the flat: WSC/flats/PROVENANCE.md.
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol ScriptHash mintingInputs)
open PlutusCore.UPLC.Term (Term)

-- Symbolic prep at 900 exceeds the default 200k-heartbeat cap (SPIKE-FINDINGS:
-- `#prep_uplc` is Lean-side work and is NOT covered by `(timeout: n)`, which
-- caps Z3 only).
set_option maxHeartbeats 0

#import_uplc programmableTokenMinting900 PlutusV3 double_cbor_hex "WSC/flats/programmableTokenMinting.flat"

/-- Parameter evidence for `programmableTokenMinting` — 2 parameters, then ctx.
Identical to `WSC/Prep/Minting.lean`'s `mintingPolicyInputs` (re-declared here
only to keep the two preps in independent modules); citations updated to the
line numbers actually read in the source this session:

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.
2. `mintingLogicHash : PAsData PScriptHash` — token-specific minting-logic
   script hash (MUST be the LAST applied parameter; the offchain
   issuance-cbor-hex derivation splits the compiled CBOR around it —
   Issuance.hs:11-17).

* Plutarch signature: `mkProgrammableLogicMinting :: Term s (PAsData
  PCurrencySymbol :--> PAsData PScriptHash :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/Issuance.hs:132
  (lambda order `\protocolParamsCS mintingLogicHash' ctx` at :133).
* Offchain application order: `mkProgrammableLogicMinting # pdata (pconstant
  protocolParamsCS)` then `applyArguments … [toData $ extractScriptHash $
  transStakeCredential mintingCred]`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:135-140.
* Purpose: MINTING policy — `PMintingScript ownCS' <- pmatch
  pscriptContext'scriptInfo` at Issuance.hs:139.

Both parameters are Data-encoded bytestrings (`CurrencySymbol`/`ScriptHash` are
`ByteString` abbrevs with `toData := Data.B` — CardanoLedgerApi/V1/Value.lean:10,
CardanoLedgerApi/V1/Scripts.lean:16). -/
def mintingPolicyInputs900 (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash :: mintingInputs ctx

#prep_uplc appliedMinting900 programmableTokenMinting900 mintingPolicyInputs900 900

end WSC
