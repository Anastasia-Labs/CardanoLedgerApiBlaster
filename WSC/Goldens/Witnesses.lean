/-
WSC/Goldens/Witnesses.lean — REAL-SUITE positive witnesses (task Y4 RESULT B;
ADDENDUM E9 "boundary witnesses", upgrade of P3's bootstrap witness).

`WSC/Props/P3_Base.lean` proves its non-vacuity with a HAND-CONSTRUCTED
accepting context (`P3Witness`, now relabelled BOOTSTRAP there).  This module
replaces that role with the real thing: the off-chain-produced golden

    programmableLogicBase.base-spend-transfer-tx

decoded straight out of its `serialiseData` CBOR (`WSC/Goldens/Vectors.lean` ←
`WSC/goldens/programmableLogicBase.base-spend-transfer-tx.json`).  That golden
was verified accepting by running the actual production-exported script at PV11
through `PlutusLedgerApi.V3.evaluateScriptCounting`
(`WSC/goldens/MANIFEST.md`), and its run costs K = 208 CEK steps
(`WSC/goldens/K-MEASUREMENTS.md` §3) — comfortably inside the 600-step
`#prep_uplc` budget of `WSC/Prep/Base.lean`, which is why THIS validator is the
one that can carry a real-suite witness today.  (The other three validators'
cheapest accepting goldens need 784 / 1,554 / 2,570 steps against preps of 600;
see the follow-up note at the bottom.)

WHY THIS IS STRICTLY STRONGER THAN THE BOOTSTRAP WITNESS: the bootstrap context
was written by hand in Lean, so it certifies only that SOME context is accepted
within the budget.  This one is a transaction the off-chain suite actually
builds and the Haskell ledger evaluator actually accepts, entering Lean through
PCB's CBOR decoder and CLAB's `IsData` instance with a byte-identical
round-trip receipt (`ctx_pins_the_golden` below).  Nothing about it is
transcribed by a human.
-/
import WSC.Goldens.Decode
import WSC.Goldens.TermsCheck
import WSC.Prep.Base
import WSC.Props.P3_Base
import Blaster

namespace WSC.Goldens.Witness

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential ScriptContext validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful)

-- Blaster closes Valid goals via `admit` (WSC/SPIKE-FINDINGS.md): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false

/-! ## The golden, decoded

The three arguments come from the golden's `Data` literals in
`WSC/Goldens/Terms.lean` (generated from the JSON hexes and PROVEN equal to
PlutusCoreBlaster's own CBOR decode of them in `WSC/Goldens/TermsCheck.lean`),
pushed through CLAB's `IsData` instances.

WHY THE LITERALS AND NOT `ctxOfHex` DIRECTLY: `by blaster` cannot see through a
`partial def`, and BOTH of PCB's decoders on the hex path are partial
(`hexStringToString`, `decodeDataLoop`) — a goal mentioning `ctxOfHex …` dies
with `normConst: partial function not supported`.  The literal route keeps the
whole term structurally recursive.  Fidelity is not weakened: the
`*_pins_the_golden` theorems below re-derive the same values through the hex
path with `native_decide`, so the literal and the golden CBOR are the same
transaction.

`Option.getD` needs a fallback; the fallbacks are the BOOTSTRAP witness's own
values (`WSC.P3Witness`), and the pinning theorems prove the fallback is never
taken. -/

/-- The golden vector (generated from
`WSC/goldens/programmableLogicBase.base-spend-transfer-tx.json`). -/
def golden : Vector := programmableLogicBase_base_spend_transfer_tx

private abbrev goldenParams : List PlutusCore.Data.Data :=
  Terms.programmableLogicBase_base_spend_transfer_tx_params

/-- Parameter 1: the global (transfer) rewarding credential,
`paramsHex[0] = d87a9f581c1313…13ff` = `Constr 1 [B 1313…13]` =
`ScriptCredential 1313…13`. -/
def globalCred : Credential :=
  (IsData.fromData (goldenParams.getD 0 (.I 0))).getD WSC.P3Witness.globalCred

/-- Parameter 2: the standalone seize rewarding credential,
`paramsHex[1] = d87a9f581c4040…40ff`. -/
def seizeCred : Credential :=
  (IsData.fromData (goldenParams.getD 1 (.I 0))).getD WSC.P3Witness.seizeCred

/-- The golden `ScriptContext`. -/
def ctx : ScriptContext :=
  (IsData.fromData Terms.programmableLogicBase_base_spend_transfer_tx_ctx).getD
    WSC.P3Witness.ctx

/-! ## Pinning: these ARE the golden's values, and nothing was lost -/

/-- **Pinning (params).** Decoding the golden's `paramsHex` fields through PCB's
CBOR decoder yields exactly `globalCred` / `seizeCred` — so the literal route and
the hex route agree, and the `Option.getD` fallbacks above are not taken. -/
theorem params_pin_the_golden :
    (golden.paramsHex.getD 0 "" |> credentialOfHex) = some globalCred ∧
    (golden.paramsHex.getD 1 "" |> credentialOfHex) = some seizeCred ∧
    golden.paramsHex.length = 2 := by
  native_decide

/-- **Pinning (context).** `ctx` is exactly what PCB's CBOR decoder + CLAB's
`IsData ScriptContext` produce from the golden's `scriptContextHex`, AND
re-encoding `ctx` reproduces that hex **byte for byte**.  This is the fidelity
receipt: CLAB's reading of the golden is lossless, so `ctx` is the off-chain
context and not an approximation of it. -/
theorem ctx_pins_the_golden :
    ctxOfHex golden.scriptContextHex = some ctx ∧
    ctxTypeRoundTrips golden = some true := by
  native_decide

/-- The separately-exposed `redeemerHex` is the context's own redeemer field
(ADDENDUM E8 consistency gate).  For this validator the redeemer is `()`
(`Constr 0 []`) — the base validator ignores its redeemer. -/
theorem redeemer_matches_context : redeemerMatchesContext golden = some true := by
  native_decide

/-! ## RESULT B — the real-suite positive witness

Both forms of the prepped program are exhibited, exactly as
`WSC/Props/P3_Base.lean` does for the bootstrap:

* `exec_accepts` — the raw metered CEK run (`cekExecuteProgram … 600`), closed
  by `native_decide`;
* `prop_accepts` — the OPTIMIZED term the P-theorems quantify over.  Kernel
  `decide` cannot work on `.prop` because `Optimize` embeds
  `Classical.propDecidable`, so this is closed by `blaster` on the fully
  concrete goal (the idiom `P3_Base.lean:197-198` documents). -/

/-- Bool reflection of `isSuccessful` (a `Prop`) for `native_decide`; same
helper as `WSC.P3Witness.isHaltB`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- **REAL-SUITE POSITIVE WITNESS (executable CEK).** The production
`programmableLogicBase` bytecode ACCEPTS the golden
`base-spend-transfer-tx` context at the module's 600-step budget. -/
theorem exec_accepts : isSuccessful (appliedBase.exec globalCred seizeCred ctx) :=
  isHaltB_sound _ (by native_decide)

/-- **REAL-SUITE POSITIVE WITNESS (prepped form) — RESULT B.**
`isSuccessful (appliedBase.prop <golden params> <golden ctx>)`: the same golden
context is accepted by the optimized term that `P3_base_requires_global_or_seize`
quantifies over.  Hence P3 is non-vacuous *on a transaction the off-chain suite
really builds*, not merely on a hand-made one. -/
theorem prop_accepts : isSuccessful (appliedBase.prop globalCred seizeCred ctx) := by
  blaster

/-! ## What the witness satisfies on the postcondition side

P3's conclusion is discharged through its FIRST disjunct: the golden's
withdrawal map contains the `globalCred` parameter (the transfer tx withdraws
zero from the global stake credential). -/

theorem ctx_post :
    credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl = true := by
  native_decide

/-! ## SCOPE: the caveat is now DISCHARGED

This module used to carry an honest caveat here: the golden context failed
`validSpendingContext` on its `txInfoFee > 0` conjunct, because the wsc-poc
benchmark harness that built it charged no fee.  That was a harness artifact, not
a fact about the chain, and it has been **fixed upstream** — the harness now
charges a positive fee and balances against it, emits `txInfoWdrl` in the
ledger's own `Credential` order, and attaches min-UTxO ada to every output.

So the golden now satisfies `validSpendingContext` **outright, with every
conjunct checked verbatim** (no relaxation).  P3's non-vacuity therefore no
longer rests only on the bytecode accept fact: this context can be substituted
into `P3_base_requires_global_or_seize` to re-derive `ctx_post`, which is what
LR-CTX (ADDENDUM E5) was supposed to buy and previously could not. -/
theorem ctx_satisfies_validSpendingContext :
    validSpendingContext ctx = true ∧
    relaxedVerdict golden = some true ∧
    0 < ctx.scriptContextTxInfo.txInfoFee := by
  native_decide

/-! ## FOLLOW-UP (parallel agents Y1/Y2)

This module deliberately depends on `WSC/Prep/Base.lean` (budget 600) ONLY.
Y1/Y2 are adding `WSC/Prep/Minting900` and `WSC/Prep/Global1600`; this copy of
the repo predates them, so no witness is attempted for the other validators.
When those preps land, the same six-theorem pattern applies verbatim to

* `programmableTokenMinting.mint-burnonly` (K = 784) against Minting900, and
* `programmableLogicGlobal.transfer-nonmember-covering-node` (K = 1,554)
  against Global1600,

using `byteStringOfHex` (`WSC/Goldens/Decode.lean`) for their `CurrencySymbol` /
`ScriptHash` parameters instead of `credentialOfHex`.  `programmableSeize`'s
cheapest accepting golden needs 2,570 steps and has no affordable prep
(`K-MEASUREMENTS.md` §5.2). -/

end WSC.Goldens.Witness
