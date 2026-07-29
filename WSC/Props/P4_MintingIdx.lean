/-
WSC/Props/P4_MintingIdx.lean — **P4a, PROVED, OVER THE UNSHAPED PREP, AT A
LITERAL REDEEMER INDEX** (task X2 / consolidation task).

════════════════════════════════════════════════════════════════════════════
READ THIS FIRST: THIS MODULE RETIRES A HEADLINE `⚠️ Undetermined`
════════════════════════════════════════════════════════════════════════════
`WSC/Props/P4_Minting.lean`'s `P4a_mint_runs_minting_logic` is the obligation
whose `⚠️ Undetermined` at **296 s, 1,748 s and 3,208 s of Z3 — all identical**
is the MOTIVATING EXAMPLE for prep-shaping in this project's method write-up
(`WSC/SHAPING-RESULTS.md` §2, and `docs/METHOD.md` §2 in the published mirror).

**That obligation now has a proof, over the SAME UNSHAPED PREP, in 1.9 s** —
`P4a_idx_burn0` below.  Nothing about the prep changed: it is
`WSC.appliedMinting900`, the unshaped prep of the production issuance policy at
budget 900, the identical term.  The only change is ONE HYPOTHESIS pinning the
redeemer's index to a LITERAL.

**This does NOT mean shaping was unnecessary.**  It means the specific example
chosen to sell shaping has a better proof.  Shaping is still necessary for the
heavy validators, and that is measured, not assumed: task X3 swept
`smt.random-seed` 0–31 and eleven Z3 configurations against this same unshaped
P4a goal at caps up to 900 s and got **0 hits, 11/11 timeout**, and the same
against the unshaped P3 goal.  No solver knob touches an unshaped goal.  The
SMT-level reason is in `WSC/SHAPING-RESULTS.md`: the unshaped queries carry
**14** quantified `isList`/`isData` well-formedness axioms (one per symbolic
recursive `TxInfo` structure) against **3–4** for the shaped ones.  What this
module shows is that pinning ONE `Data` field can drop a goal out of the
14-axiom class without freezing a single list — for the base and issuance
validators only.

════════════════════════════════════════════════════════════════════════════
WHAT IS AND IS NOT COVERED
════════════════════════════════════════════════════════════════════════════
The class each theorem ranges over leaves SYMBOLIC: the mint value, every
output, every reference input, the redeemer map, the signatories, the validity
range, the certificates, the datum witnesses, the withdrawal map INCLUDING ITS
LENGTH, and both script parameters.  The residual is exactly one dimension —
the burn redeemer's index — and it is expressible in ledger vocabulary.

Measured ladder against `WSC.appliedMinting900` @ 900 (task X2):

| rung | verdict | wall | landed here? |
|---|---|---|---|
| `BurnOnly 0` | ✅ Valid | 1.9 s | yes |
| `BurnOnly 1` | ✅ Valid | 1.0 s | yes |
| `BurnOnly 10` | ✅ Valid | 2.3 s | yes |
| `BurnOnly 25` | ⚠️ Undetermined | 902 s (cap 900) | **NO** — the wall |
| `Constr 3 [I _]` — skeleton only, index SYMBOLIC | ⚠️ Undetermined | 903 s | no |

The symbolic-index row is the same negative as on the base validator
(`WSC/Props/P3_BaseIdx.lean` §header): the win is `Optimize.main` folding a
literal, not the class being small.

════════════════════════════════════════════════════════════════════════════
THIS IS STRICTLY STRONGER THAN `P4a_mint_runs_minting_logic` IN ONE MORE WAY
════════════════════════════════════════════════════════════════════════════
`P4_Minting.lean`'s statement assumes `validMintingContext ctx`.  The theorems
below deliberately DO NOT — the ledger predicate is dropped, so the class is
larger and the theorem stronger.  (Task X2 §6 measured that predicate to be a
first-order solver cost independent of the property.)

`WSC/Props/P4_Minting.lean`'s ARM-SCOPE note still applies and is not weakened
here: at budget 900 only the pure-burn arm is reachable at all
(`WSC/goldens/K-MEASUREMENTS.md`: `mint.burnonly` K = 784, the next accepting
golden is 1,257), which is exactly why the reachable rungs are `BurnOnly i`.
-/
import WSC.Prep.Minting900
import WSC.Props.P4_Minting
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC.P4Idx

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          credentialInWithdrawals)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §0 THE HYPOTHESIS

One `Bool`-valued equation on one `Data` field.  Not a shape: it is used
against the UNSHAPED `WSC.appliedMinting900`. -/

/-- The mint redeemer is `BurnOnly i` on the wire (`Issuance.hs:83-85` / `:88-90`
give the constructor index 3).  Used with a **literal** `i`. -/
def redIsBurnOnly (i : Integer) (ctx : ScriptContext) : Bool :=
  ctx.scriptContextRedeemer == Data.Constr 3 [Data.I i]

/-! ## §1 P4a AT A LITERAL BURN INDEX -/

/-- **P4a AT `BurnOnly 0` — THE HEADLINE RESULT OF THIS MODULE.**
*Any accepted run of the issuance minting policy whose redeemer is `BurnOnly 0`
runs the token's minting-logic script: its script credential appears in the
transaction's withdrawal map.*

Same prep, same budget, same solver, same postcondition as
`WSC.P4a_mint_runs_minting_logic` (`WSC/Props/P4_Minting.lean`), which is
`⚠️ Undetermined` after 3,208 s.  This closes in ≈ 2 s. -/
theorem P4a_idx_burn0 :
  ∀ (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext),
    redIsBurnOnly 0 ctx = true →
    isSuccessful (appliedMinting900.prop protocolParamsCS mintingLogicHash ctx) →
      credentialInWithdrawals (Credential.ScriptCredential mintingLogicHash)
        ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 900)

/-- **P4a AT `BurnOnly 1`.** -/
theorem P4a_idx_burn1 :
  ∀ (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext),
    redIsBurnOnly 1 ctx = true →
    isSuccessful (appliedMinting900.prop protocolParamsCS mintingLogicHash ctx) →
      credentialInWithdrawals (Credential.ScriptCredential mintingLogicHash)
        ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 900)

/-- **P4a AT `BurnOnly 10` — the top measured rung.**  `BurnOnly 25` is
`⚠️ Undetermined` at a 900 s cap. -/
theorem P4a_idx_burn10 :
  ∀ (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext),
    redIsBurnOnly 10 ctx = true →
    isSuccessful (appliedMinting900.prop protocolParamsCS mintingLogicHash ctx) →
      credentialInWithdrawals (Credential.ScriptCredential mintingLogicHash)
        ctx.scriptContextTxInfo.txInfoWdrl := by
  blaster (timeout: 900)

/-! ## §2 THE MANDATORY VACUITY PROBES

Expected: Falsified — accepting contexts of the class exist inside budget 900. -/

/-- Vacuity at `BurnOnly 0`.  Expected: Falsified. -/
def vac_burn0 : Prop :=
  ∀ (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext),
    redIsBurnOnly 0 ctx = true →
    ¬ isSuccessful (appliedMinting900.prop protocolParamsCS mintingLogicHash ctx)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [vac_burn0]

/-- Vacuity at `BurnOnly 1` — a rung the certified golden does NOT inhabit, so
non-vacuity is established away from the witness too.  Expected: Falsified. -/
def vac_burn1 : Prop :=
  ∀ (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ctx : ScriptContext),
    redIsBurnOnly 1 ctx = true →
    ¬ isSuccessful (appliedMinting900.prop protocolParamsCS mintingLogicHash ctx)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [vac_burn1]

/-! ## §3 WITNESS MEMBERSHIP — the four-point bar, inherited

Kernel-level, no solver.  `WSC.P4Witness.ctx` is the library's certified
accepting minting context: it is the decoded `mint.burnonly` golden, accepted by
the real CEK machine at K = 784 (`WSC/goldens/K-MEASUREMENTS.md` §3, pinned
two-sided in `WSC/Props/P4_Minting.lean`), ledger-valid and redeemer-covered.
Showing it is INSIDE rung 0's class is what makes `P4a_idx_burn0`'s class
node-realizable rather than merely non-empty in the solver's model. -/

/-- The certified `mint.burnonly` witness is in rung 0's class. -/
theorem mctx_in_burn0 : redIsBurnOnly 0 P4Witness.ctx = true := by native_decide

end WSC.P4Idx
