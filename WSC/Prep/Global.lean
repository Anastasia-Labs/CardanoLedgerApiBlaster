-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Prep/Global.lean — import + prep of the programmableLogicGlobal
(transfer) validator. Split into its own module so the `#prep_uplc`
elaboration is cached per-validator. Provenance: WSC/flats/PROVENANCE.md.

CIP-153 NOTE (X4, 2026-07-25): this validator uses the CIP-153 Value builtins
(insertCoin/lookupCoin/unionValue/valueContains/valueData/unValueData —
flat builtin tags 94-99). It therefore decodes/preps ONLY against the
CIP-153-capable PlutusCoreBlaster (branch `cip153-value-builtins` @ 9f9ca8c;
see ADDENDUM E11 "Substrate pins" in WSC/ARCHITECTURE.md). Against PCB `main`
@ 4ef4860 the same flat fails with "Decoding error … Could not decode
program!" (negative control re-verified 2026-07-25 against that checkout's
own build).

DECODE GATE (X4 step 2, 2026-07-25): the `#import_uplc` below reports
`Successfully decoded double CBOR hex 'WSC/flats/programmableLogicGlobal.flat'`.
The decoded program is 3444 term nodes with 282 builtin occurrences, of which
46 are CIP-153 (InsertCoin 4, LookupCoin 0, UnionValue 14, ValueContains 2,
ValueData 4, UnValueData 22) — the new tags are genuinely consumed, so the
real production transfer validator now runs in the Lean CEK. Cost:
`lake env lean WSC/Prep/Global.lean` = 17.2 s wall / 1.25 GB peak RSS
(decode + prep@600 + probe, 32-core box); as a lake module, 1.9 s.

BUDGET NOTE (mirrors Prep/Seize.lean): fully-symbolic `#prep_uplc` on
accept-capable budgets is empirically intractable for the heavy validators
(E2 spike). This module preps at 600 ONLY to validate the CIP-153
import/apply/CEK pipeline end-to-end; the vacuity probe below CHARACTERIZES
the budget as vacuous (no accepting context within 600 steps — the cheapest
golden accept, transfer-nonmember-covering-node, costs 29,160,036 CPU units,
so 600 raw CEK steps cannot reach accept). No P-theorem may be stated against
`appliedGlobal` from this module — P1 uses SHAPED contexts with per-shape
measured budgets (ARCHITECTURE.md ADDENDUM, Stage-3b).
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs
                          validRewardingContext)
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.Utils (isSuccessful)

#import_uplc programmableLogicGlobal PlutusV3 double_cbor_hex "WSC/flats/programmableLogicGlobal.flat"

/-- Parameter evidence for `programmableLogicGlobal` — 1 parameter, then ctx:

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.

* Plutarch signature: `mkProgrammableLogicGlobal :: Term s (PAsData
  PCurrencySymbol :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1176
  (lambda order `\protocolParamsCS ctx` at :1177).
* Offchain application: `mkProgrammableLogicGlobal # pdata (pconstant $
  transPolicyId paramsPolId)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:119-122.
* Golden corroboration: all four `programmableLogicGlobal.*` vectors in
  WSC/goldens/ carry exactly ONE `paramsHex` entry (MANIFEST.md param table,
  `ProgrammableLogicBase.hs:1176` row).
* Purpose: REWARDING (withdraw-zero) validator — `pisRewardingScript` is the
  first validated condition (ProgrammableLogicBase.hs:1254). -/
def globalInputs (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

#prep_uplc appliedGlobal programmableLogicGlobal globalInputs 600

/-- Vacuity characterization @600 (X4 step 3). RESULT (2026-07-25): `✅ Valid`
⟹ the budget is **VACUOUS** — there is NO accepting context within 600 CEK
steps. Expected: the cheapest accepting golden for this validator,
`programmableLogicGlobal.transfer-nonmember-covering-node`, costs 29,160,036
CPU units (WSC/goldens/MANIFEST.md), so 600 raw steps cannot reach accept.
`solve-result: 0` therefore encodes "expected Valid = expected vacuous" — this
stanza is a CHARACTERIZATION, not a property. The deliverable of this module is
that the CEK evaluates the CIP-153 builtins symbolically without hard errors
(decode + apply + prep + solve all clean), not that 600 is accept-capable. -/
def global_vacuity_probe_600 : Prop :=
  ∀ (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx →
    ¬ isSuccessful (appliedGlobal.prop protocolParamsCS ctx)

#blaster (gen-cex: 0) (solve-result: 0) [global_vacuity_probe_600]

end WSC
