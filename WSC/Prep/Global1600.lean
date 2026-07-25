/-
WSC/Prep/Global1600.lean — SECOND prep of the SAME imported
`programmableLogicGlobal` (transfer) validator, at CEK step budget **1600**.

WHY A SECOND MODULE (task Y1). `WSC/Prep/Global.lean` preps the same flat at
budget 600, which its own committed probe CHARACTERIZES AS VACUOUS (no
accepting context exists within 600 CEK steps). Budget 600 is therefore
unusable for any `accept → POST` theorem. This module exists so that P5 (the
escape-critical NonMember/covering-node property, ADDENDUM E3) can be stated
against a NON-VACUOUS prep. The 600 module is left intact: it is cited by the
CIP-153 decode gate and by the vacuity characterization in
WSC/goldens/K-MEASUREMENTS.md §4.

WHY EXACTLY 1600 (WSC/goldens/K-MEASUREMENTS.md, task X1 measurements):
* The CHEAPEST accepting golden of this validator is
  `programmableLogicGlobal.transfer-nonmember-covering-node` at **K = 1554**
  CEK steps (K-MEASUREMENTS §3) — and that golden is precisely P5's subject
  shape (a transfer in which a policy is classified `NonMember` and a covering
  directory node is referenced). So 1600 ≥ 1554 is the smallest round budget
  that admits an accepting run of exactly the scenario P5 talks about.
* Symbolic `#prep_uplc` cost is exponential in the BUDGET with a measured
  marginal doubling every ~100-113 steps, then a cliff: global @600 = 11.8 s,
  @900 = 24.3 s, **@1600 = 2143 s = 35.7 min (completed, 1.55 GB peak RSS)**,
  while minting @1700 never completed in 48.6 min and seize @2000 never
  completed in 77 min (K-MEASUREMENTS §5.1). 1600 is thus the ONLY measured
  accept-capable budget for this validator that is known to terminate; do NOT
  raise it (1700+ risks the cliff), and in particular the containment-carrying
  transfer accepts (K = 3262 / 3726, i.e. P1's shapes) are 7-182 years of prep
  on the measured slope and are out of reach — see K-MEASUREMENTS §5.2.

SCOPE CONSEQUENCE (ADDENDUM E1, binding). Every theorem stated against
`appliedGlobal1600.prop` is BOUNDED-TRANSACTION model checking of the real
bytecode: it constrains exactly those invocations whose validator run halts
within 1600 CEK steps. Non-vacuity is certified by the mandatory probe in
WSC/Props/P5_NonMember.lean (Falsified = an accepting context exists inside
1600 steps), and the golden above is the concrete witness of the shape that
budget covers.

CIP-153 NOTE (X4/E11): this validator uses the CIP-153 Value builtins (flat
builtin tags 94-99), so it decodes ONLY against the CIP-153-capable
PlutusCoreBlaster (branch `cip153-value-builtins` @ 9f9ca8c, pinned by
lakefile.lean as a LOCAL path — see ADDENDUM E11 "Substrate pins", including
its binding reproducibility caveat: that branch is unpushed). Against PCB
`main` @ 4ef4860 the same flat fails with "Could not decode program!".

Provenance of the flat: WSC/flats/PROVENANCE.md (same bytes as
WSC/Prep/Global.lean imports; this module re-imports rather than re-using the
600 module's `programmableLogicGlobal` so that the two preps stay in
independently-cached modules).
-/
import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

-- The 1600-step symbolic unrolling is a ~36-minute elaboration; the default
-- 200k-heartbeat cap kills it in seconds (SPIKE-FINDINGS: `#prep_uplc` dies on
-- `maxHeartbeats` before it dies on wall clock).
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs)
open PlutusCore.UPLC.Term (Term)

#import_uplc programmableLogicGlobal1600 PlutusV3 double_cbor_hex "WSC/flats/programmableLogicGlobal.flat"

/-- Parameter evidence for `programmableLogicGlobal` — 1 parameter, then ctx
(identical to WSC/Prep/Global.lean; repeated here so this module is
self-contained):

1. `protocolParamsCS : PAsData PCurrencySymbol` — protocol-params NFT policy id.

* Plutarch signature: `mkProgrammableLogicGlobal :: Term s (PAsData
  PCurrencySymbol :--> PScriptContext :--> PUnit)`
  — src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:1176
  (lambda order `\protocolParamsCS ctx` at :1177).
* Offchain application: `mkProgrammableLogicGlobal # pdata (pconstant $
  transPolicyId paramsPolId)`
  — src/programmable-tokens-offchain/lib/ProgrammableTokens/OffChain/Scripts.hs:119-122.
* Golden corroboration: all four `programmableLogicGlobal.*` vectors in
  WSC/goldens/ carry exactly ONE `paramsHex` entry (MANIFEST.md param table).
* Purpose: REWARDING (withdraw-zero) validator — `pisRewardingScript` is the
  first validated condition (ProgrammableLogicBase.hs:1254). -/
def globalInputs1600 (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

#prep_uplc appliedGlobal1600 programmableLogicGlobal1600 globalInputs1600 1600

end WSC
