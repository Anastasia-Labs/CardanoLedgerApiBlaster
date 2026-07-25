/-
WSC/Goldens/RedeemerGate.lean — the ADDENDUM E8 golden-CBOR gate on every
`IsData` mirror instance in `WSC/Redeemer.lean` (task Y4 RESULT C).

WHAT THIS CATCHES.  Every redeemer-conditioned theorem in the WSC library
(`isTransferAct`, `isSeizeAct`, `isDelegateSeize`, `classifiedMember`, the
`MintRedeemer` arm split of P4, the seized-policy projection of P2, …) reads the
attacker-supplied redeemer through the hand-written `IsData` mirrors in
`WSC/Redeemer.lean`.  If one mirror had the wrong `makeIsDataIndexed` tag or the
wrong field order, those theorems would silently be about a DIFFERENT redeemer
than the one the chain carries: they would still typecheck, still prove, and
still be worthless.  This module is the gate that rules that out, using CBOR
produced by the off-chain Haskell suite.

WHY A ROUND-TRIP ALONE IS NOT ENOUGH (important).  `toData ∘ fromData = id` is
insensitive to a CONSISTENTLY wrong encoding: a mirror that used tag 5 where
Haskell uses tag 0 would round-trip perfectly.  So each golden is checked
**twice**:

1. `mirrorRoundTrip` — the mirror DECODES the golden CBOR and re-encodes it
   byte-identically (catches field-count/shape drift), and
2. `encodesTo <expected value> <golden hex>` — the mirror's `toData` of the
   value the Haskell driver says it built (`WSC/goldens/MANIFEST.md`, "Goldens"
   table, and the `sourceTest` field of each JSON) reproduces the golden bytes
   exactly (catches a wrong tag or a permuted field order, because it pins the
   VALUE, not just the shape).

Together: the decoded value's `toData` equals the expected value's `toData`,
which for these mirrors (all injective) means the mirror reads the golden as the
constructor the Haskell side actually wrote.

Datum mirrors are gated the same way from the goldens' inline reference-input
datums (`GlobalParams`, `DirectorySetNode` — the two raw-`Data.List` encodings,
historically the most error-prone, including the fifth `globalStateCS` field).

All checks are `native_decide` (the CBOR decoder is `partial`, so kernel
`decide` is not available).
-/
import WSC.Goldens.Decode
import WSC.Redeemer

namespace WSC.Goldens.RedeemerGate

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential ScriptContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

/-! ## The two gate primitives -/

/-- Decode `h` (golden `serialiseData` hex) through the CBOR decoder and then
through `α`'s mirror `IsData` instance, re-encode, and compare bytes.
`some true` = decoded AND byte-identical; `some false` = decoded but the
re-encoding differs (BLOCKER); `none` = the mirror REFUSED the golden (BLOCKER). -/
def mirrorRoundTrip (α : Type) [IsData α] (h : String) : Option Bool :=
  match dataOfHex h with
  | none => none
  | some d =>
      match (IsData.fromData d : Option α) with
      | none => none
      | some x => (fun h' => h' == h) <$> hexOfData (IsData.toData x)

/-- Does the mirror encode the given value to exactly the golden's bytes?
This is the clause that pins tags and field order. -/
def encodesTo {α : Type} [IsData α] (x : α) (h : String) : Bool :=
  hexOfData (IsData.toData x) == some h

/-- Value-level agreement: the mirror's reading of the golden has the same
`Data` image as the expected value.  (Stated via `toData` so that no
`DecidableEq` instance has to be added to `WSC/Redeemer.lean`; `Data` has one.) -/
def decodesToValue (α : Type) [IsData α] (h : String) (expected : Data) : Bool :=
  match dataOfHex h with
  | none => false
  | some d =>
      match (IsData.fromData d : Option α) with
      | none => false
      | some x => IsData.toData x == expected

/-! ## programmableLogicBase — the redeemer is `()`

`mkProgrammableLogicBase` never reads its redeemer
(`ProgrammableLogicBase.hs:717-729`); the off-chain suite supplies `()`, whose
PlutusTx encoding is `Constr 0 []`.  There is deliberately NO mirror type for
it in `WSC/Redeemer.lean`, so only the `Data`-level fact is asserted. -/

theorem base_redeemers_are_unit :
    dataOfHex programmableLogicBase_base_spend_transfer_tx.redeemerHex
      = some (Data.Constr 0 []) ∧
    dataOfHex programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT.redeemerHex
      = some (Data.Constr 0 []) := by
  native_decide

/-! ## programmableTokenMinting — `MintRedeemer` (+ `RegWitness`)

Tags frozen by `makeIsDataIndexed` at `Issuance.hs:88-90`
(`Local = 0`, `DelegateTransfer = 1`, `DelegateSeize = 2`, `BurnOnly = 3`) and
`Issuance.hs:57-59` (`RegisteredByReferenceInput = 0`, `RegisteredByOutput = 1`).
Expected values from `WSC/goldens/MANIFEST.md`. -/

/-- `mint-local-registered-by-ref`: MANIFEST says
`Local 0 0 (RegisteredByReferenceInput 1)`.  Exercises the `Local` tag (0), all
three of its fields in order, AND the nested `RegWitness` tag (0). -/
theorem mint_local_registered_by_ref :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex = some true ∧
    encodesTo (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex = true ∧
    decodesToValue MintRedeemer
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex
      (IsData.toData (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))) = true := by
  native_decide

/-- `mint-local-empty-withdrawals-REJECT`: same redeemer as above (the tamper is
in the context, `txInfoWdrl := []`, not the redeemer). -/
theorem mint_local_empty_withdrawals_REJECT :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_local_empty_withdrawals_REJECT.redeemerHex = some true ∧
    encodesTo (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))
      programmableTokenMinting_mint_local_empty_withdrawals_REJECT.redeemerHex = true := by
  native_decide

/-- `mint-burnonly`: MANIFEST says `BurnOnly 2`.  Exercises the HIGHEST mint tag
(3), i.e. the compact CBOR tag 124 — the case a tag-offset bug would break. -/
theorem mint_burnonly :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_burnonly.redeemerHex = some true ∧
    encodesTo (MintRedeemer.BurnOnly 2)
      programmableTokenMinting_mint_burnonly.redeemerHex = true ∧
    decodesToValue MintRedeemer programmableTokenMinting_mint_burnonly.redeemerHex
      (IsData.toData (MintRedeemer.BurnOnly 2)) = true := by
  native_decide

/-- `mint-delegate-transfer-topup`: MANIFEST says `DelegateTransfer 2 0 1 0`.
Exercises tag 1 and all four fields in order — a permutation of
`(mintingLogicWdrlIdx, paramsRefIdx, nodeRefIdx, globalWdrlIdx)` would be caught
here because the four values are not all equal. -/
theorem mint_delegate_transfer_topup :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = some true ∧
    encodesTo (MintRedeemer.DelegateTransfer 2 0 1 0)
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = true ∧
    decodesToValue MintRedeemer
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex
      (IsData.toData (MintRedeemer.DelegateTransfer 2 0 1 0)) = true := by
  native_decide

/-! ## programmableLogicGlobal / programmableSeize — `PLGRedeemer` (+ `MintProof`)

Tags frozen by `makeIsDataIndexed` at `ProgrammableLogicBase.hs:1066-1068`
(`TransferAct = 0`, `SeizeAct = 1`). -/

/-- `transfer-member-single-policy`: MANIFEST says `TransferAct [1] [1] [] 0`. -/
theorem transfer_member_single_policy :
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] 0)
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex = true ∧
    decodesToValue PLGRedeemer
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex
      (IsData.toData (PLGRedeemer.TransferAct [1] [1] [] 0)) = true := by
  native_decide

/-- `transfer-nonmember-covering-node` and
`transfer-containment-violation-REJECT` carry the same `TransferAct [1] [1] [] 0`. -/
theorem transfer_nonmember_and_violation :
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] 0)
      programmableLogicGlobal_transfer_nonmember_covering_node.redeemerHex = true ∧
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_nonmember_covering_node.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] 0)
      programmableLogicGlobal_transfer_containment_violation_REJECT.redeemerHex = true ∧
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_containment_violation_REJECT.redeemerHex = some true := by
  native_decide

/-- `transfer-mixed-many-policies`: MANIFEST says proofs `[1,2,3,4,1]`.  The
strongest field-order test in the suite: the two `[Integer]` fields have
DIFFERENT contents (`[1,2,3,4,1]` vs `[1,1,1,1,1]`), so swapping
`plgrTransferProofs` with `plgrTransferWdrlIdxs` would be caught. -/
theorem transfer_mixed_many_policies :
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1, 2, 3, 4, 1] [1, 1, 1, 1, 1] [] 0)
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = true ∧
    decodesToValue PLGRedeemer
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex
      (IsData.toData (PLGRedeemer.TransferAct [1, 2, 3, 4, 1] [1, 1, 1, 1, 1] [] 0)) = true := by
  native_decide

/-- `seize-1-input`: MANIFEST records the Haskell helper call
`mkSeizeActRedeemerFromAbsoluteInputIdxs 1 [0] 0 0 0`, i.e.
`SeizeAct dirNodeIdx=1 inputIdxs=[0] outputsStartIdx=0 lengthInputIdxs=1
seizeParamsRefIdx=0 issuerWdrlIdx=0` (issuerWdrlIdx is 0, not 1, since the
harness now emits `txInfoWdrl` in the ledger's own Credential order, which puts
the issuer credential `0x14..` before the seize credential `0x40..`) (the helper computes `lengthInputIdxs`
from the list, which is why the wire form has six fields for five arguments).
Exercises tag 1 and all six fields. -/
theorem seize_1_input :
    mirrorRoundTrip PLGRedeemer
      programmableSeize_seize_1_input.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)
      programmableSeize_seize_1_input.redeemerHex = true ∧
    decodesToValue PLGRedeemer programmableSeize_seize_1_input.redeemerHex
      (IsData.toData (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)) = true := by
  native_decide

/-- `seize-1-input-missing-residual-output-REJECT`: same redeemer (the tamper
deletes an output). -/
theorem seize_1_input_missing_residual_REJECT :
    mirrorRoundTrip PLGRedeemer
      programmableSeize_seize_1_input_missing_residual_output_REJECT.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)
      programmableSeize_seize_1_input_missing_residual_output_REJECT.redeemerHex = true := by
  native_decide

/-- `seize-2-inputs-partial-with-noise`: two seized inputs, so
`lengthInputIdxs = 2`.  Note `inputIdxs = [0,0]` — legitimate, because the
current seize validator no longer READS `pinputIdxs`/`plengthInputIdxs`
(`ProgrammableLogicBase.hs:1299-1304`), while the fields remain in the frozen
encoding (documented at `WSC/Redeemer.lean:104-107`). -/
theorem seize_2_inputs_partial_with_noise :
    mirrorRoundTrip PLGRedeemer
      programmableSeize_seize_2_inputs_partial_with_noise.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.SeizeAct 1 [0, 0] 0 2 0 0)
      programmableSeize_seize_2_inputs_partial_with_noise.redeemerHex = true ∧
    decodesToValue PLGRedeemer
      programmableSeize_seize_2_inputs_partial_with_noise.redeemerHex
      (IsData.toData (PLGRedeemer.SeizeAct 1 [0, 0] 0 2 0 0)) = true := by
  native_decide

/-! ## COVERAGE GAP, stated honestly

The 13 goldens exercise: `MintRedeemer.Local` / `.DelegateTransfer` /
`.BurnOnly`, `RegWitness.RegisteredByReferenceInput`,
`PLGRedeemer.TransferAct` / `.SeizeAct`.  They do NOT contain any of

* `MintRedeemer.DelegateSeize` (tag 2),
* `RegWitness.RegisteredByOutput` (tag 1) — note `Issuance.hs:207` makes
  registration reg-by-REF only, so this arm may be unreachable by design (L4.3),
* a non-empty `mintProofs` list, hence neither `MintProof.Member` (tag 0) nor
  `MintProof.NonMember` (tag 1).

Those four constructors' tags/field orders remain SOURCE-CITED ONLY
(`WSC/Redeemer.lean`), not golden-gated.  `MintProof` is the one that matters
most: ADDENDUM E8 makes `classifiedMember/NonMember` positional in the mint
list, so a `MintProof` tag error would mis-read P5/P6's classification.
FOLLOW-UP: extend the golden driver with (a) a `DelegateSeize` mint and (b) a
transfer whose `plgrMintProofs` is non-empty with both a `Member` and a
`NonMember` entry. -/

/-! ## Datum mirrors: `GlobalParams` and `DirectorySetNode`

Both are raw `Data.List` encodings (NOT `Constr`), hand-written `ToData` in the
source — `ProtocolParams.hs:84-96` and `PTokenDirectory.hs:167-174` — which
makes them the likeliest place for a field-order or arity mistake.  They are
gated here from the goldens' inline reference-input datums, extracted with
`inlineDatums` below.

Field values as they appear in every golden (verified below):
`GlobalParams` = ⟨directoryNodeCS 11…11, progLogicCred Script 12…12,
globalLogicCred Script 13…13, seizeLogicCred Script 40…40⟩ — note the last two
are exactly the two `programmableLogicBase` script parameters, so the goldens
are internally config-consistent. -/

private def b28 (c : Char) : ByteString := ByteString.mk (String.mk (List.replicate 28 c))

/-- All inline datums (`OutputDatum`) attached to a context's reference inputs,
inputs and outputs, in that order. -/
def inlineDatums (ctx : ScriptContext) : List Data :=
  (ctx.scriptContextTxInfo.txInfoReferenceInputs.map
      (fun i => i.txInInfoResolved.txOutDatum)
   ++ ctx.scriptContextTxInfo.txInfoInputs.map (fun i => i.txInInfoResolved.txOutDatum)
   ++ ctx.scriptContextTxInfo.txInfoOutputs.map (fun o => o.txOutDatum)).filterMap
      (fun d => match d with
        | .OutputDatum dat => some dat
        | _ => none)

/-- The protocol-params datum the goldens carry, per the `GlobalParams` mirror.
`globalLogicCred`/`seizeLogicCred` coincide with the base validator's two script
parameters (`WSC/goldens/MANIFEST.md`, "Validator signatures"). -/
def expectedParamsDatum : GlobalParams :=
  { directoryNodeCS := b28 '\x11'
  , progLogicCred := .ScriptCredential (b28 '\x12')
  , globalLogicCred := .ScriptCredential (b28 '\x13')
  , seizeLogicCred := .ScriptCredential (b28 '\x40') }

/-- **Datum gate.** In EVERY golden context, the first inline datum is the
protocol-params datum, and the `GlobalParams` mirror reproduces it byte for byte
— including the raw-`Data.List`-of-4 shape and the normative field order
(`ProtocolParams.hs:44-68`). -/
theorem globalParams_datum_gate :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          match (inlineDatums ctx).head? with
          | none => false
          | some d =>
              (IsData.fromData d : Option GlobalParams).isSome
              && IsData.toData expectedParamsDatum == d) = true := by
  native_decide

/-- **Datum gate.** Every inline datum in every golden that is not the
protocol-params datum is a `DirectorySetNode`, and the mirror re-encodes it byte
for byte — including the FIFTH field `globalStateCS`
(`PTokenDirectory.hs:144-150`), whose omission would shift nothing detectably in
a 4-field reading but is caught by the byte comparison. -/
theorem directoryNode_datum_gate :
    all.all (fun v =>
      match ctxOfHex v.scriptContextHex with
      | none => false
      | some ctx =>
          (inlineDatums ctx).all (fun d =>
            (IsData.toData expectedParamsDatum == d)
            || (match (IsData.fromData d : Option DirectorySetNode) with
                | none => false
                | some n => IsData.toData n == d))) = true := by
  native_decide

/-- The covering ("does-not-exist") directory node that
`transfer-nonmember-covering-node` uses is the sentinel-bounded root node
`key = "" `, `next = 0xff…ff` (28 bytes) — exactly the shape ADDENDUM E3 makes
P5's postcondition witness (`dirNodeKey i < cs < dirNodeNext i`). -/
theorem covering_node_is_sentinel_bounded :
    (match ctxOfHex programmableLogicGlobal_transfer_nonmember_covering_node.scriptContextHex with
     | none => false
     | some ctx =>
         (inlineDatums ctx).any (fun d =>
           match (IsData.fromData d : Option DirectorySetNode) with
           | none => false
           | some n => n.key == ByteString.mk "" && n.next == b28 '\xff')) = true := by
  native_decide

/-! ## Aggregate: RESULT C verdict in one Bool -/

/-- Every golden's redeemer decodes through the correct mirror type and
re-encodes byte-identically (`()` for the two base goldens, which have no mirror
type and are covered by `base_redeemers_are_unit`). -/
def allRedeemerMirrorsRoundTrip : Bool :=
  all.all fun v =>
    match v.validator with
    | "programmableLogicBase" => dataOfHex v.redeemerHex == some (Data.Constr 0 [])
    | "programmableTokenMinting" => mirrorRoundTrip MintRedeemer v.redeemerHex == some true
    | "programmableSeize" => mirrorRoundTrip PLGRedeemer v.redeemerHex == some true
    | "programmableLogicGlobal" => mirrorRoundTrip PLGRedeemer v.redeemerHex == some true
    | _ => false

theorem allRedeemerMirrorsRoundTrip_true : allRedeemerMirrorsRoundTrip = true := by
  native_decide

end WSC.Goldens.RedeemerGate
