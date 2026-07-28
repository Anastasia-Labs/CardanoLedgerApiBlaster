-- ⚠️ PRE-#112 / **PROVABLY DEAD**: SHAPE B1's redeemer is `Data.I red`, and the post-#112 base validator opens its redeemer with `pasConstr`, which errors on a `Data.I`. Its ACCEPT CLASS IS EMPTY — machine-checked as `WSC.Z2Calib.B1_accept_class_is_empty` (`WSC/Shaped/Calib/P3Shaped.lean`, ✅ Valid). Every `accept → …` statement over `appliedBaseShaped` is therefore VACUOUSLY true. The live replacement is SHAPES B1RG/B1RS in `WSC/Shaped/BaseShapedR.lean`. See WSC/IMPACT-PR112.md APPENDIX N3.
/-
WSC/Shaped/BaseShaped.lean — SHAPED prep of `programmableLogicBase`
(task Z2 rung 1: the calibration rung, run on the ONE already-proven property).

Mechanism (i) of the two the task lists: the shape is baked into the
`#prep_uplc` inputs function, so the CEK symbolic execution never sees a
symbolic `Data` skeleton and the residual the SOLVER gets is smaller. (Mechanism
(ii) — keep the unshaped prep and add shape hypotheses — leaves the residual as
large as before and is not used.)

Same flat, same budget (600) as WSC/Prep/Base.lean, so the comparison
WSC/Shaped/Calib/P3Unshaped.lean vs WSC/Shaped/Calib/P3Shaped.lean isolates
exactly one variable: the shape.
-/
import WSC.Prep.Base
import WSC.Shaped.Shape
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TxInInfo TxOutRef TxInfo spendingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- **SHAPE B1 — "one base spend, two script withdrawals".**

FIXED (this is the published scope): exactly 1 input and it is the script's own
input; 0 reference inputs; 0 outputs; empty mint, certificate, signatory, datum,
vote and proposal lists; a withdrawal map of exactly 2 entries, both carrying
SCRIPT credentials; exactly 1 redeemer entry, for the `Spending` purpose of the
own input; the spent output carries an ada-only canonical value, no datum and no
reference script; a finite closed validity interval; treasury/donation present.

SYMBOLIC (every scalar leaf): the own input's transaction id and index, the base
script hash the input sits at, its lovelace amount, BOTH withdrawal credentials'
script hashes and BOTH withdrawal amounts, the fee, the redeemer integer, the
validity bounds and the transaction id.

Note what is deliberately symbolic: the two withdrawal credentials. P3's
conclusion is a statement about exactly those, so shaping them concretely would
have smuggled the postcondition into the shape. -/
def baseShapedCtx
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString)
    : ScriptContext :=
  let outRef : TxOutRef := ⟨txid, idx⟩
  let resolved : TxOut :=
    { txOutAddress := ⟨.ScriptCredential baseHash, none⟩
    , txOutValue := adaOnly lovelace
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨outRef, resolved⟩]
      , txInfoReferenceInputs := []
      , txInfoOutputs := []
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]
      , txInfoValidRange := range lo hi
      , txInfoSignatories := []
      , txInfoRedeemers := [(.Spending outRef, Data.I red)]
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := Data.I red
  , scriptContextScriptInfo := .SpendingScript outRef none }

/-- The shape's withdrawal map, named separately so the theorem statements stay
readable. `baseShapedCtx_wdrl` below proves this IS the shaped context's
withdrawal map, so nothing is lost by quoting it. -/
def baseShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer)
    : CardanoLedgerApi.V3.Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- AUDIT LINK: `baseShapedWdrl` is exactly `txInfoWdrl` of the shaped context. -/
theorem baseShapedCtx_wdrl
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid).scriptContextTxInfo.txInfoWdrl
      = baseShapedWdrl w0 w1 a0 a1 := rfl

/-- Shaped inputs function. The two script parameters are also shaped: they are
`ScriptCredential`s over symbolic hashes (`gh`, `sh`), which is what the honest
deployment uses — both the global transfer validator and the seize validator are
scripts (ProgrammableLogicBase.hs:722-729, offchain Scripts.hs:100-109). -/
def baseShapedInputs
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString)
    : List Term :=
  toTerm (Credential.ScriptCredential gh) :: toTerm (Credential.ScriptCredential sh)
    :: spendingInputs
        (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid)

#prep_uplc appliedBaseShaped programmableLogicBase baseShapedInputs 600

end WSC
