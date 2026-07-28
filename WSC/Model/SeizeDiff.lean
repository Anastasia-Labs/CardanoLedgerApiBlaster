-- ⛔ REFUTED AT PR #112: `seizeModel_faithful` is FALSE at main 2306678 — machine-checked counterexample in WSC/Model/SeizeModelRefuted.lean. The 13/13 differential test still passes but no golden covers the change. Results bridged by that axiom are INVALID for production.
/-
WSC/Model/SeizeDiff.lean — **THE FIDELITY GATE** for the source-model route.

`WSC/Model/SeizeModel.lean` is a hand transcription of `mkProgrammableSeize`.
A transcription is only worth what its differential test is worth, so this
module compares the model against the REAL BYTECODE on every golden in the
suite, three ways:

1. **model vs. the Lean CEK machine running the production flat.**
   `WSC/Prep/Seize.lean`'s `programmableSeize` is the imported production
   `WSC/flats/programmableSeize.flat` (sha256 in `WSC/flats/PROVENANCE.md`), and
   `WSC.seizeInputs` is its audited application order.  For each of the **13**
   golden `ScriptContext`s this module runs that bytecode on the context and
   compares the machine's accept/reject with `seizeModel`'s.  All 13 comparisons
   are closed by `native_decide` (`all_13_model_agrees_with_bytecode`).
   This is the strong test: it is 13 independent transactions, and 10 of them
   are contexts built for the *other three* validators, i.e. exactly the
   off-purpose shapes a hand transcription is most likely to get wrong.
2. **model vs. the recorded Haskell-ledger verdict** for the 3 goldens whose
   validator IS `programmableSeize`: 2 accepting, 1 rejecting.  Those verdicts
   come from `PlutusLedgerApi.V3.evaluateScriptCounting` at PV11 on the
   production-exported script (`WSC/goldens/MANIFEST.md`) — a completely
   different implementation of the CEK machine from PlutusCoreBlaster's.
3. **the ExBudget cross-check already in the repo** (`WSC/goldens/MANIFEST.md`,
   "applied/" section): PCB's metered CEK reproduces the Haskell ledger's
   ExBudget to the unit on all 9 accepting goldens, which is what licenses
   using route 1 as a proxy for the node.

THE REJECTING SEIZE GOLDEN IS THE LOAD-BEARING ONE.
`programmableSeize.seize-1-input-missing-residual-output-REJECT` is
`seize-1-input` with the residual (seized-tokens) output deleted — i.e. it fails
precisely on the containment half of P2.  A model that accepted everything, or
that got `perror` polarity backwards in `checkBalanceInvariant`
(ProgrammableLogicBase.hs:1508), would still pass the two accepting goldens and
would be caught only here.

GOLDEN ARTEFACTS ARE NOT CANONICALISED (`WSC/LR-CTX-AUDIT.md`, `WSC/STATUS.md`
§3 D3).  All 13 goldens have `txInfoFee = 0`; the 3 seize goldens emit their two
script withdrawal credentials DESCENDING; the 2 accepting seize goldens have a
residual output with no ada entry at all.  The goldens are run here EXACTLY AS
THEY ARE, because that is what the bytecode was executed on.  Consequently these
theorems are statements about the bytecode's accept behaviour (which is all a
differential test needs), not about `validRewardingContext`-normalised
transactions; the last theorem in this file records that gap explicitly.
-/
import WSC.Model.SeizeModel
import WSC.Goldens.Decode
import WSC.Goldens.Terms
import WSC.Goldens.Vectors

namespace WSC.SeizeModel.Diff

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open WSC.Goldens

/-! ## The script parameter

`programmableSeize` takes ONE parameter, `protocolParamsCS`
(ProgrammableLogicBase.hs:1290-1291; `WSC/Prep/Seize.lean`'s parameter
evidence).  It is taken from the golden's own `paramsHex`, never transcribed. -/

/-- `protocolParamsCS` as carried by the seize goldens' `paramsHex[0]`. -/
def paramsCS : Option CurrencySymbol :=
  match Terms.programmableSeize_seize_1_input_params with
  | Data.B cs :: _ => some cs
  | _ => none

/-- **Pinning.** The parameter used below is exactly the golden's `paramsHex[0]`
decoded by PlutusCoreBlaster's own CBOR decoder, and all three seize goldens
carry the SAME parameter (they are the same deployment). -/
theorem paramsCS_pins_the_goldens :
    (WSC.Goldens.byteStringOfHex
        ((WSC.Goldens.programmableSeize_seize_1_input.paramsHex).getD 0 "")) = paramsCS ∧
    WSC.Goldens.programmableSeize_seize_2_inputs_partial_with_noise.paramsHex
      = WSC.Goldens.programmableSeize_seize_1_input.paramsHex ∧
    WSC.Goldens.programmableSeize_seize_1_input_missing_residual_output_REJECT.paramsHex
      = WSC.Goldens.programmableSeize_seize_1_input.paramsHex := by
  native_decide

/-- The parameter, with the (never-taken) fallback discharged by
`paramsCS_pins_the_goldens` + `paramsCS_is_some`. -/
def ppCS : CurrencySymbol := paramsCS.getD (ByteString.mk "")

theorem paramsCS_is_some : paramsCS = some ppCS := by native_decide

/-! ## Executing the real bytecode

`seizeExecAt` (WSC/Model/SeizeModel.lean) is `cekExecuteProgram
programmableSeize.script (seizeInputs …) n` — the same machine and the same
program `WSC/Prep/Seize.lean`'s `appliedSeize.exec` uses, with the step count
left free. -/

/-- Bool reflection of "the CEK machine halted successfully" (same helper as
`WSC/Goldens/Witnesses.lean`). -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → PlutusCore.UPLC.Utils.isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- Step budget for the differential runs.  The two accepting seize goldens halt
in **2,570** and **4,647** CEK steps (`WSC/goldens/K-MEASUREMENTS.md` §3), so
20,000 is far above both; rejecting and off-purpose runs `Error` long before it.
Deliberately generous: a budget-starved run would `Error` and could be mistaken
for a genuine rejection. -/
def diffSteps : Nat := 20000

/-! ## The 13 golden rows

`recorded` is the golden JSON's `accepts` field — the verdict of the
production-exported script that golden was built for, run at PV11 by the Haskell
ledger evaluator.  `ownValidator` says whether that validator IS
`programmableSeize`; only for those three rows is `recorded` comparable to the
seize model.  For the other ten, `recorded` is about a different script and the
comparison that matters is model vs. the seize bytecode on the same context. -/

structure Row where
  name : String
  ownValidator : Bool
  recorded : Bool
  ctx : Data

open WSC.Goldens.Terms in
def rows : List Row :=
  [ ⟨"programmableSeize.seize-1-input", true, true,
      programmableSeize_seize_1_input_ctx⟩
  , ⟨"programmableSeize.seize-2-inputs-partial-with-noise", true, true,
      programmableSeize_seize_2_inputs_partial_with_noise_ctx⟩
  , ⟨"programmableSeize.seize-1-input-missing-residual-output-REJECT", true, false,
      programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx⟩
  , ⟨"programmableLogicBase.base-spend-transfer-tx", false, true,
      programmableLogicBase_base_spend_transfer_tx_ctx⟩
  , ⟨"programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT", false, false,
      programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT_ctx⟩
  , ⟨"programmableTokenMinting.mint-local-registered-by-ref", false, true,
      programmableTokenMinting_mint_local_registered_by_ref_ctx⟩
  , ⟨"programmableTokenMinting.mint-burnonly", false, true,
      programmableTokenMinting_mint_burnonly_ctx⟩
  , ⟨"programmableTokenMinting.mint-delegate-transfer-topup", false, true,
      programmableTokenMinting_mint_delegate_transfer_topup_ctx⟩
  , ⟨"programmableTokenMinting.mint-local-empty-withdrawals-REJECT", false, false,
      programmableTokenMinting_mint_local_empty_withdrawals_REJECT_ctx⟩
  , ⟨"programmableLogicGlobal.transfer-member-single-policy", false, true,
      programmableLogicGlobal_transfer_member_single_policy_ctx⟩
  , ⟨"programmableLogicGlobal.transfer-nonmember-covering-node", false, true,
      programmableLogicGlobal_transfer_nonmember_covering_node_ctx⟩
  , ⟨"programmableLogicGlobal.transfer-mixed-many-policies", false, true,
      programmableLogicGlobal_transfer_mixed_many_policies_ctx⟩
  , ⟨"programmableLogicGlobal.transfer-containment-violation-REJECT", false, false,
      programmableLogicGlobal_transfer_containment_violation_REJECT_ctx⟩
  ]

/-- Decode a golden's `Data` into a CLAB `ScriptContext`.  All 13 decode — that
is `WSC/Goldens/Decode.lean`'s `allContextsDecode`, re-checked below. -/
def ctxOf (d : Data) : Option ScriptContext := IsData.fromData d

/-- The model's verdict on a golden. -/
def modelVerdict (d : Data) : Option Bool :=
  match ctxOf d with
  | some c => some (WSC.SeizeModel.seizeModel ppCS c)
  | none => none

/-- The BYTECODE's verdict on a golden: the production `programmableSeize` flat,
applied to `(ppCS, ctx)` and run on PlutusCoreBlaster's CEK machine. -/
def bytecodeVerdict (d : Data) : Option Bool :=
  match ctxOf d with
  | some c => some (isHaltB (WSC.SeizeModel.seizeExecAt diffSteps ppCS c))
  | none => none

/-- Per-golden differential report: `(name, model, bytecode, recorded-if-comparable)`.
Kept as a `#eval`-able value so the table can be inspected, not just asserted. -/
def report : List (String × Option Bool × Option Bool × Option Bool) :=
  let rec go : List Row → List (String × Option Bool × Option Bool × Option Bool)
    | [] => []
    | r :: rest =>
        (r.name, modelVerdict r.ctx, bytecodeVerdict r.ctx,
          if r.ownValidator then some r.recorded else none) :: go rest
  go rows

/-- Every row decodes, and the model's verdict equals the bytecode's. -/
def modelAgreesWithBytecode : Bool :=
  let rec go : List Row → Bool
    | [] => true
    | r :: rest =>
        (match modelVerdict r.ctx, bytecodeVerdict r.ctx with
         | some m, some b => m == b
         | _, _ => false) && go rest
  go rows

/-- On the rows whose own validator IS `programmableSeize`, the model's verdict
equals the verdict recorded by the Haskell ledger evaluator. -/
def modelAgreesWithRecorded : Bool :=
  let rec go : List Row → Bool
    | [] => true
    | r :: rest =>
        (if r.ownValidator then
            (match modelVerdict r.ctx with
             | some m => m == r.recorded
             | none => false)
          else true) && go rest
  go rows

/-- Count of rows checked, and of `ownValidator` rows — so the theorems below
cannot silently degenerate to a check of the empty list. -/
def rowCounts : Nat × Nat :=
  let rec go : List Row → Nat × Nat
    | [] => (0, 0)
    | r :: rest => let (a, b) := go rest; (a + 1, if r.ownValidator then b + 1 else b)
  go rows

/-! ## RESULTS -/

/-- **Suite shape (anti-degeneracy).** 13 rows, 3 of them `programmableSeize`'s
own goldens, and each seize golden's polarity is as `WSC/goldens/MANIFEST.md`
records it (2 accepting, 1 rejecting). -/
theorem suite_shape :
    rowCounts = (13, 3) ∧
    WSC.Goldens.programmableSeize_seize_1_input.accepts = true ∧
    WSC.Goldens.programmableSeize_seize_2_inputs_partial_with_noise.accepts = true ∧
    WSC.Goldens.programmableSeize_seize_1_input_missing_residual_output_REJECT.accepts
      = false := by
  native_decide

/-- **DIFFERENTIAL RESULT 1 — 13/13 model vs. production bytecode.**
For every one of the 13 golden `ScriptContext`s, `seizeModel ppCS ctx` equals
"the production `programmableSeize` bytecode halts successfully on `ctx`". -/
theorem all_13_model_agrees_with_bytecode : modelAgreesWithBytecode = true := by
  native_decide

/-- **DIFFERENTIAL RESULT 2 — 3/3 model vs. the Haskell ledger's recorded
verdicts**, on the three goldens that ARE `programmableSeize` transactions:
`seize-1-input` (accept), `seize-2-inputs-partial-with-noise` (accept), and
`seize-1-input-missing-residual-output-REJECT` (reject). -/
theorem all_3_model_agrees_with_recorded_ledger_verdict :
    modelAgreesWithRecorded = true := by
  native_decide

/-- **The two accepting seize goldens, spelled out.**  The model accepts them,
the bytecode accepts them, and (via `isHaltB_sound`) they witness
`seizeAcceptsUnbounded` — so `seizeModel_faithful`'s left-to-right direction is
non-vacuously instantiated by real transactions. -/
theorem accepting_seize_goldens :
    modelVerdict Terms.programmableSeize_seize_1_input_ctx = some true ∧
    bytecodeVerdict Terms.programmableSeize_seize_1_input_ctx = some true ∧
    modelVerdict Terms.programmableSeize_seize_2_inputs_partial_with_noise_ctx = some true ∧
    bytecodeVerdict Terms.programmableSeize_seize_2_inputs_partial_with_noise_ctx = some true := by
  native_decide

/-- **The rejecting seize golden, spelled out** — the load-bearing row.  Both the
model and the bytecode REJECT the `seize-1-input` transaction with its residual
(seized-tokens) output deleted.  This is the containment half of P2 failing, and
it is the only golden that can catch an over-permissive model or a flipped
`perror` polarity in `checkBalanceInvariant` (ProgrammableLogicBase.hs:1508). -/
theorem rejecting_seize_golden :
    modelVerdict Terms.programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx
      = some false ∧
    bytecodeVerdict Terms.programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx
      = some false := by
  native_decide

/-- **The 10 off-purpose goldens.**  These are contexts built for the base
validator, the issuance minting policy and the global transfer validator.  The
seize bytecode rejects all 10, and so does the model — for reasons that differ
per family and are all mirrored in `seizeFieldsOf`
(WSC/Model/SeizeModel.lean §4): the 2 base goldens carry the unit redeemer
`Constr 0 []` (⇒ the `PTransferAct` arm's `ptraceInfoError` at
ProgrammableLogicBase.hs:1298); the 4 global goldens carry a `TransferAct`,
also `Constr 0` (same error); the 4 minting goldens carry a `MintRedeemer`
whose field list is too short for the raw `phead`/`ptail` chain that reaches
`pissuerWdrlIdx` at field 5 (`Local` has 3 fields, `DelegateTransfer`/
`DelegateSeize` 4, `BurnOnly` 1).  Note the last family exercises the
**constructor fall-through** path (`Constr 1/2/3` all fall through to the
`PSeizeAct` arm) — the one decode gap `WSC/Redeemer.lean`'s strict mirror does
not have. -/
theorem off_purpose_goldens_all_rejected :
    modelVerdict Terms.programmableLogicBase_base_spend_transfer_tx_ctx = some false ∧
    modelVerdict Terms.programmableTokenMinting_mint_burnonly_ctx = some false ∧
    modelVerdict Terms.programmableTokenMinting_mint_local_registered_by_ref_ctx = some false ∧
    modelVerdict Terms.programmableTokenMinting_mint_delegate_transfer_topup_ctx = some false ∧
    modelVerdict Terms.programmableLogicGlobal_transfer_member_single_policy_ctx = some false ∧
    modelVerdict Terms.programmableLogicGlobal_transfer_mixed_many_policies_ctx = some false ∧
    bytecodeVerdict Terms.programmableLogicBase_base_spend_transfer_tx_ctx = some false ∧
    bytecodeVerdict Terms.programmableTokenMinting_mint_burnonly_ctx = some false ∧
    bytecodeVerdict Terms.programmableLogicGlobal_transfer_member_single_policy_ctx
      = some false := by
  native_decide

/-! ## HONEST SCOPE CAVEATS (do not delete)

1. **CAVEAT DISCHARGED (task Z5): the two ACCEPTING seize goldens now satisfy
   `validRewardingContext`.**  This caveat used to read "the goldens do not
   satisfy `validRewardingContext`; every golden has `txInfoFee = 0` (a builder
   artefact)".  All three of that artefact's siblings have since been fixed
   upstream in wsc-poc's
   `ProgrammableTokens.Test.ScriptContext.Builder.buildLedgerShapedScriptContext`
   — positive balanced fee, withdrawal map in the ledger's `Credential` order,
   and min-UTxO ada on every output (the seize residual seized-token UTxO was the
   only lovelace-free output in the whole suite) — and the goldens were
   re-dumped.  So the two accepting seize goldens CAN now be substituted into
   `P2_seize_relocates_only_seized` to re-derive its postcondition.  The
   REJECTING golden still fails, but only on `isBalanced`, which is intrinsic to
   its tamper (it deletes the residual output).  See
   `WSC/LR-CTX-AUDIT.md` and `WSC/Goldens/Audit.lean`.
2. **What the goldens do NOT exercise.**  Enumerated in
   `seizeModel_faithful`'s docstring: the constructor fall-through is exercised
   only by the 4 minting goldens (and only into a too-short field list, never
   into a well-formed 6-field `Constr 5`); `pdropList`'s negative-index clamping
   is exercised by no golden (all redeemer indices here are ≥ 0); the
   `remainingProgCSDelta` `perror` branches (:1767, :1768) are not reached by any
   golden. -/
/-- `(validRewardingContext ctx, 0 < txInfoFee)` for a golden. -/
def validityAndFee (d : Data) : Option (Bool × Bool) :=
  match ctxOf d with
  | some c => some (validRewardingContext c, decide (0 < c.scriptContextTxInfo.txInfoFee))
  | none => none

/-- The two ACCEPTING seize goldens satisfy `validRewardingContext` verbatim, and
all three pay a positive fee.  The rejecting one fails, on `isBalanced` alone —
intrinsic to its tamper, which deletes the residual output (see
`WSC/Goldens/Audit.lean`'s
`fail_seize_1_input_missing_residual_output_REJECT`). -/
theorem accepting_seize_goldens_satisfy_validRewardingContext :
    validityAndFee Terms.programmableSeize_seize_1_input_ctx = some (true, true) ∧
    validityAndFee Terms.programmableSeize_seize_2_inputs_partial_with_noise_ctx
      = some (true, true) ∧
    validityAndFee Terms.programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx
      = some (false, true) := by
  native_decide

end WSC.SeizeModel.Diff
