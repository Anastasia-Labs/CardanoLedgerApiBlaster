/-
WSC/Props/P5_Witness1600.lean

╔══════════════════════════════════════════════════════════════════════════════╗
║  **READ THIS FIRST — WHAT IS AND IS NOT A THEOREM IN THIS FILE.**            ║
║                                                                              ║
║  Historically this module contained TWO `#eval` COMMANDS AND NOTHING ELSE.    ║
║  `#eval` prints a string into the build log.  It is evidence a human can      ║
║  read; it is **not** a kernel-checked proposition, `#print axioms` cannot be  ║
║  run on it, and it must **never** be cited as a theorem.  Task U2 cited       ║
║  "`WSC.Witness1600`" as if it were one; the independent audit recorded that   ║
║  as finding **F11 (INFORMATIONAL)** and this banner is task A1's response.    ║
║                                                                              ║
║  * `WSC.Witness1600.golden_halts_at_1600` — **THEOREM** (`native_decide`).    ║
║  * `WSC.Witness1600.golden_errors_at_1553` — **THEOREM** (`native_decide`).   ║
║    Both added by task A1 so the facts this file is cited for are now          ║
║    theorem-grade IN THIS FILE.  Cite these names, not "`WSC.Witness1600`".    ║
║  * the two `#eval`s at the bottom — **NOT THEOREMS.**  Retained only because  ║
║    a human-readable `HALT`/`ERROR` line in the build log is useful when       ║
║    debugging the accept path.  They prove nothing.                            ║
║                                                                              ║
║  Even the two theorems are about the **fully applied golden flat**, not about ║
║  `appliedGlobal1600.prop`.  For a claim about the term P5 quantifies over,    ║
║  cite `WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped` (theorem, real      ║
║  bytecode, `native_decide`) or, for the `prop` term itself,                   ║
║  `WSC.ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600` (`blaster`,          ║
║  therefore `sorryAx`).  The non-vacuity obligation of `WSC/Honest.lean` is    ║
║  discharged by `WSC.NonVacuity.globalNonVacuous_at_1600`, which is about      ║
║  `Runs.globalRun 1600` — not about anything in this file.                     ║
╚══════════════════════════════════════════════════════════════════════════════╝

CONCRETE non-vacuity witness for CEK step budget 1600 on the production
`programmableLogicGlobal` (transfer) validator, i.e. the budget
WSC/Prep/Global1600.lean preps at and the budget P5 is stated against
(WSC/Props/P5_NonMember.lean).

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
unit by PCB's own cost model — §2.2).
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

/-- Bool reflection of "reached `Halt`", so the facts below can be THEOREMS
rather than `#eval`s. -/
def isHaltB : State → Bool
  | .Halt _ => true
  | _ => false

/-! ## THEOREMS (task A1) — the two facts this module is cited for

`native_decide`, i.e. the real CEK machine on the real applied golden flat,
compiled. Axioms: `Lean.ofReduceBool`, `Lean.trustCompiler` (plus whatever the
`Bool` equality needs) and **no `sorryAx`**. -/

/-- Budget 1600 ≥ K = 1554: the real bytecode ACCEPTS the golden. -/
theorem golden_halts_at_1600 :
    isHaltB (cekExecuteProgram goldenNonMemberApplied.script [] 1600) = true := by
  native_decide

/-- Budget 1553 = K − 1: budget exhaustion. The control that shows the `Halt`
above is a genuine accept reached at ~1554 steps, not an artifact. -/
theorem golden_errors_at_1553 :
    isHaltB (cekExecuteProgram goldenNonMemberApplied.script [] 1553) = false := by
  native_decide

/-! ## NOT THEOREMS — human-readable log lines only

These two `#eval`s are the module's original content. They are kept because a
`HALT`/`ERROR` string in the build log is convenient, and for no other reason.
**Nothing may cite them.** The theorems above state the same two facts. -/

/- NOT A THEOREM. Budget 1600 >= K = 1554. Expected log line: HALT. -/
#eval outcome (cekExecuteProgram goldenNonMemberApplied.script [] 1600)

/- NOT A THEOREM. Budget 1553 = K - 1. Expected log line: ERROR. -/
#eval outcome (cekExecuteProgram goldenNonMemberApplied.script [] 1553)

/-! ## AXIOM AUDIT — runnable on the theorems, impossible on the `#eval`s -/

#print axioms WSC.Witness1600.golden_halts_at_1600
#print axioms WSC.Witness1600.golden_errors_at_1553

end WSC.Witness1600
