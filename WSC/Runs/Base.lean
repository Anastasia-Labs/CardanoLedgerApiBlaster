/-
WSC/Runs/Base.lean — `Runs.baseRun`, SPLIT OUT AS ITS OWN LEAF (task N3).

WHY THE SPLIT. `WSC/Runs.lean` holds all four `XRun` definitions and therefore
imports all four preps — `Prep.Base`, `Prep.Minting900`, `Prep.Global1600`,
`Prep.Seize`. After wsc-poc PR #112 two of those four are BROKEN at the
substrate level (`WSC/IMPACT-PR112.md` §6: the new seize flat does not decode
without a `ScaleValue` tag in PCB; the new global flat does not prep at 1600),
so `WSC/Runs.lean` — and with it `WSC/Honest.lean` and every run-form
theorem — could not be built at all. That is an ACCIDENTAL dependency: the base
validator's run form has nothing whatever to do with the seize or global
bytecode.

Splitting `baseRun` into this leaf makes the base keystone provable
independently of the other three validators' substrate state, which is the
property it should have had all along. `WSC/Runs.lean` imports this module and
re-exports nothing — `WSC.Runs.baseRun` is the SAME constant with the SAME
definition, so every existing consumer (`WSC/Honest.lean`'s `LR_BUDGET_base`,
`WSC/Composition.lean`'s `p3_lifted`, `WSC/ShapeBridge.lean`'s `exec_*`)
resolves it exactly as before. Nothing else moved: in particular `WSC.K_base`
stays in `WSC/Honest.lean`, and `K_base = 600` by `rfl`, so a theorem stated
here at the literal `600` is the same statement.

WHAT THIS MODULE IS. One definition: *the imported production base validator
running on a `ScriptContext` under a `K`-step CEK meter*. No `#prep_uplc`, no
`Blaster.Optimize`, no solver, no `Classical` embedding. See `WSC/Runs.lean`'s
header for the full rationale of the `XRun` family (task A1) — it applies
verbatim.
-/
import WSC.Prep.Base

namespace WSC
namespace Runs

open CardanoLedgerApi.V3 (Credential ScriptContext)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

/-- `programmableLogicBase` at budget `K` on a ledger-supplied context.

Flat: `WSC/flats/programmableLogicBase.flat` (`WSC/Prep/Base.lean`), the
POST-#112 bytecode (`sha256 a9e7364b519a…`).
Inputs fn: `WSC.baseInputs` (parameter-evidence audit in the same file's
docstring — 2 `PAsData PCredential` params, then the ctx). -/
def baseRun (K : Nat) (globalCred seizeCred : Credential) (ctx : ScriptContext) :=
  cekExecuteProgram programmableLogicBase.script (baseInputs globalCred seizeCred ctx) K

end Runs
end WSC
