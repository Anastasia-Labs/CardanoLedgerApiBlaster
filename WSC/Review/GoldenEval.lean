/-
WSC/Review/GoldenEval.lean — **NON-VACUITY OF THE PROPOSED `P1UnshapedFormD` /
`P1UnshapedFormH` AT A REAL, OFF-CHAIN-PRODUCED TRANSACTION.**

Every non-vacuity certificate the P1 benchmark currently carries is a HAND-BUILT
context (`WSC.P1RShapedWitness.ctxOk`, `BaseAbsentProbe.ctxA`). That leaves open
the question an adversarial reviewer must ask of any hypothesis-form statement:
*does the hypothesis set hold of anything the real off-chain code actually
produces?* — in particular `validRewardingContext`, whose `validTxInfo` conjunct
includes `isBalanced` (`CardanoLedgerApi/V3/Contexts.lean:1778`), a global
value-conservation equation that no hand-built witness is obliged to respect
by accident.

Measured here at `WSC/goldens/programmableLogicGlobal.transfer-member-single-policy.json`
(the accepting golden the model suite already uses, decoded through
`WSC/Goldens/Decode.lean`, K pinned two-sided at 2782 by
`WSC.GlobalModelRefuted.golden_shows_budget_gap`).
-/
import WSC.Review.AdversarialProbe
import WSC.Model.GlobalModelRefuted

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Review
namespace GoldenEval

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext TokenName TxInInfo
                          validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open P1ShapedWitness (isHaltB)

def gv : WSC.Goldens.Vector :=
  WSC.Goldens.programmableLogicGlobal_transfer_member_single_policy

/-- The `(cs, tn)` of the first non-ada slot of the first mini-ledger input.
Extracted rather than hard-coded so the row below cannot drift from the golden. -/
def csTnOfBaseInput (base : Credential) : List TxInInfo → Option (CurrencySymbol × TokenName)
  | [] => none
  | i :: rest =>
      if WSC.payCred i.txInInfoResolved == base then
        match i.txInInfoResolved.txOutValue with
        | _ :: (Data.B cs, Data.Map ((Data.B tn, _) :: _)) :: _ => some (cs, tn)
        | _ => csTnOfBaseInput base rest
      else csTnOfBaseInput base rest

/-- `(validRewardingContext, isProgrammable, params-clause, outSum, inSum,
mintSigned, halts@4400)` at the decoded golden, with `dirCS` and `base` taken
from the transaction's OWN params reference input and `(cs, tn)` from its own
mini-ledger input. -/
def goldenRow : Option (Bool × Bool × Bool × Integer × Integer × Integer × Bool) :=
  match Model.Goldens.ppCSOf gv, Model.Goldens.ctxOf gv with
  | some p, some c =>
      match Benchmark.paramsPublishedBy c with
      | some (dcs, plcD) =>
          match (IsData.fromData plcD : Option Credential) with
          | some base =>
              match csTnOfBaseInput base c.scriptContextTxInfo.txInfoInputs with
              | some (cs, tn) =>
                  let ti := c.scriptContextTxInfo
                  some ( validRewardingContext c
                       , AdversarialProbe.isProgrammable dcs cs ti.txInfoReferenceInputs
                       , Benchmark.paramsPublishedBy c == some (dcs, IsData.toData base)
                       , Model.outSum base cs tn ti.txInfoOutputs
                       , Model.inSum base cs tn ti.txInfoInputs
                       , Model.mintSigned cs tn ti.txInfoMint
                       , isHaltB (WSC.GlobalModelRefuted.globalExecAt 4400 p c) )
              | none => none
          | none => none
      | none => none
  | _, _ => none

/-- **THE PROPOSED HYPOTHESIS SET IS INHABITED BY A REAL TRANSACTION, AND THE
CONCLUSION HOLDS THERE.**

`(true, true, true, 5, 5, 0, true)` — the off-chain-produced golden is
ledger-valid in CLAB's full sense (including `isBalanced`), publishes its own
`(directoryNodeCS, progLogicCred)` at the redeemer's index, carries NO covering
node for its policy (its directory reference input is the MEMBER node, keyed
exactly `cs`, so `exemptible = false`), is ACCEPTED by the real compiled
`programmableLogicGlobal` inside the benchmark's own 4400-step meter, and
satisfies `outSum 5 ≥ inSum 5 + mint 0`.

This is the certificate `WSC/Benchmark/P1UnshapedStatement.lean` §4 does not
have: a non-vacuity witness that was produced by the off-chain builder rather
than by the formalization. -/
theorem golden_inhabits_the_proposed_hypotheses :
    (goldenRow == some (true, true, true, 5, 5, 0, true)) = true := by native_decide

/-- The same golden read through the OLD (3-field) covering test: it agrees with
`exemptible` here, so the repair does not move this witness. -/
def goldenCoveringPair : Option (Bool × Bool) :=
  match Model.Goldens.ctxOf gv with
  | some c =>
      match Benchmark.paramsPublishedBy c with
      | some (dcs, plcD) =>
          match (IsData.fromData plcD : Option Credential) with
          | some base =>
              match csTnOfBaseInput base c.scriptContextTxInfo.txInfoInputs with
              | some (cs, _) =>
                  some ( Model.coveringNodeExists dcs cs
                           c.scriptContextTxInfo.txInfoReferenceInputs
                       , AdversarialProbe.exemptible dcs cs
                           c.scriptContextTxInfo.txInfoReferenceInputs )
              | none => none
          | none => none
      | none => none
  | none => none

theorem golden_old_and_new_covering_agree :
    (goldenCoveringPair == some (false, false)) = true := by native_decide

end GoldenEval
end Review
end WSC
