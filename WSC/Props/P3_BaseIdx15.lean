/-
WSC/Props/P3_BaseIdx15.lean — **THE TOP RUNG OF THE REDEEMER-INDEX LADDER**.

Split out of `WSC/Props/P3_BaseIdx.lean` for one reason: it is the only rung
that is EXPENSIVE (measured **223 s**, against 1.6–2.5 s for every rung ≤ 10),
and lake builds modules in parallel, so isolating it keeps it off the critical
path of the cheap ones.

It is landed rather than merely recorded because it is the LAST rung that
closes: `redIsG 20`, `redIsG 25` and `redIsG 100` are all `⚠️ Undetermined` at a
600 s cap (task X2).  So the boundary of the family is machine-checked from
both sides — this module is the last `✅ Valid`, and the header table of
`P3_BaseIdx.lean` records the first three failures.
-/
import WSC.Props.P3_BaseIdx
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC.P3Idx

open CardanoLedgerApi.V3 (Credential ScriptContext credentialInWithdrawals)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **RUNG 15 — the top of the ladder.**  Same statement as every other rung. -/
theorem P3_idx_g15 :
  ∀ (g s : Credential) (ctx : ScriptContext),
    redIsG 15 ctx = true →
    isSuccessful (appliedBase.prop g s ctx) →
      credentialInWithdrawals g ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals s ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 600)

end WSC.P3Idx
