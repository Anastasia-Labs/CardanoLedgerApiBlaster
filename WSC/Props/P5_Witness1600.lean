/-
WSC/Props/P5_Witness1600.lean — CONCRETE non-vacuity witness for CEK step
budget 1600 on the production `programmableLogicGlobal` (transfer) validator,
i.e. the budget WSC/Prep/Global1600.lean preps at and the budget P5 is stated
against (WSC/Props/P5_NonMember.lean).

WHAT THIS CERTIFIES. The REAL compiled transfer validator, with the REAL
off-chain-produced golden `ScriptContext` of the NonMember/covering-node
scenario applied to it, HALTS (accepts) inside 1600 CEK steps, and does NOT
halt at 1553 steps. So budget 1600 is genuinely accept-capable for exactly the
transaction shape P5 talks about: any `isSuccessful (appliedGlobal1600.prop …)
→ POST` theorem is about a non-empty set of transactions.

WHAT IT DOES NOT CERTIFY. This runs the FULLY APPLIED golden program
(`WSC/goldens/applied/…`: production script + params + ctx baked in as `Data`
constants, produced by Plutarch `applyArguments` — provenance and byte-exact
argument verification in WSC/goldens/MANIFEST.md and K-MEASUREMENTS.md §2.1),
NOT `appliedGlobal1600.prop protocolParamsCS ctx` with symbolic arguments.
The two coincide in shape — CLAB's `rewardingInputs ctx` yields exactly
`[toTerm ctx]` and `toTerm x = Term.Const (Const.Data (toData x))`
(CardanoLedgerApi/V3/Contexts.lean:676-691, IsData/Class.lean:56), i.e. one
`Const` node per argument, exactly as in the applied flat
(K-MEASUREMENTS.md §2.3) — so the accepting path costs the same K inside a
symbolic prep. But it is evidence about the BYTECODE, not a solver certificate
about the optimized `prop` term. The symbolic vacuity probe that would certify
`prop` itself did NOT return in 87 minutes (see WSC/Props/P5_NonMember.lean's
"OBLIGATION STATUS" section).

K = 1554 for this golden was measured in task X1 by iterating the real
`PlutusCore.UPLC.CekMachine.step` (WSC/goldens/K-MEASUREMENTS.md §3, and the
run's ledger `ExBudget` of 29,160,036 CPU / 86,035 mem is reproduced to the
unit by PCB's own cost model — §2.2). The two `#eval`s below reproduce the
essential fact (`Halt` at 1600, `Error` at 1553) from inside this library, at a
cost of milliseconds.
-/
import PlutusCore.UPLC

namespace WSC.Witness1600

open PlutusCore.UPLC.CekMachine (State cekExecuteProgram)

#import_uplc goldenNonMemberApplied PlutusV3 double_cbor_hex "WSC/goldens/applied/programmableLogicGlobal.transfer-nonmember-covering-node.flat"

/-- Terminal-state tag, so the `#eval`s below are readable one-liners. -/
def outcome : State → String
  | .Halt _ => "HALT (accept)"
  | .Error => "ERROR (reject or budget-exhausted)"
  | _ => "NON-TERMINAL"

/- Budget 1600 >= K = 1554: the real bytecode ACCEPTS. Expected: HALT. -/
#eval outcome (cekExecuteProgram goldenNonMemberApplied.script [] 1600)

/- Budget 1553 = K - 1: budget exhaustion. Expected: ERROR -- the control that
shows the HALT above is a genuine accept reached at ~1554 steps, not an
artifact. -/
#eval outcome (cekExecuteProgram goldenNonMemberApplied.script [] 1553)

end WSC.Witness1600
