-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/Calib/P3Unshaped.lean — CALIBRATION BASELINE (task Z2, rung 1).

Re-states P3 and its vacuity probe against the UNSHAPED prep
(`WSC/Prep/Base.lean`, fully symbolic `ScriptContext`, budget 600) in a module
of its own, so that `lake build WSC.Shaped.Calib.P3Unshaped` times the SMT solve
from scratch (`WSC/Props/P3_Base.lean` replays from cache and therefore cannot
be timed).

This is the control against which `WSC/Shaped/Calib/P3Shaped.lean` is compared.
-/
import WSC.Prep.Base
import Blaster

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC.Z2Calib

open CardanoLedgerApi.V3 (Credential ScriptContext validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- The unshaped P3 obligation (identical to `P3_base_requires_global_or_seize`). -/
theorem P3_unshaped :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    isSuccessful (appliedBase.prop globalCred seizeCred ctx) →
      credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl := by blaster

/-- The unshaped vacuity probe (expected Falsified). -/
def P3_unshaped_vacuity : Prop :=
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    ¬ isSuccessful (appliedBase.prop globalCred seizeCred ctx)

#blaster (gen-cex: 0) (solve-result: 1) [P3_unshaped_vacuity]

end WSC.Z2Calib
