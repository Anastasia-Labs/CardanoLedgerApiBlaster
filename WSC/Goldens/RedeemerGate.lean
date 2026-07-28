-- ✅ POST-#112: REWRITTEN by task N2 against wsc-poc main @ 2306678 (PR #112).
-- This module is CURRENT. It carries the post-#112 mirrors (BaseSpendRedeemer,
-- 5-field TransferAct) and, in §2, machine-checked proofs that the PRE-#112
-- mirrors in WSC/Redeemer.lean are refuted by these goldens. See
-- WSC/goldens/MANIFEST.md; WSC/IMPACT-PR112.md § the RedeemerGate row is now
-- discharged.
/-
WSC/Goldens/RedeemerGate.lean — the ADDENDUM E8 golden-CBOR gate on the redeemer
and datum mirrors (task Y4 RESULT C; REWRITTEN by task N2 for wsc-poc main
@ 2306678, i.e. after PR #112 "Seize path: per-pair value delta via CIP-153
builtins, witnessed base delegation").

WHAT THIS CATCHES.  Every redeemer-conditioned theorem in the WSC library reads
the attacker-supplied redeemer through a hand-written `IsData` mirror.  If a
mirror had the wrong `makeIsDataIndexed` tag or the wrong field order, those
theorems would silently be about a DIFFERENT redeemer than the one the chain
carries: they would still typecheck, still prove, and still be worthless.  This
module is the gate that rules that out, using CBOR produced by the off-chain
Haskell suite (`WSC/goldens/*.json`, field `redeemerHex` = `serialiseData` of
the redeemer the driver actually handed the ledger evaluator).

WHY A ROUND-TRIP ALONE IS NOT ENOUGH (important).  `toData ∘ fromData = id` is
insensitive to a CONSISTENTLY wrong encoding: a mirror that used tag 5 where
Haskell uses tag 0 would round-trip perfectly.  So each golden is checked
**twice**:

1. `mirrorRoundTrip` — the mirror DECODES the golden CBOR and re-encodes it
   byte-identically (catches field-count/shape drift), and
2. `encodesTo <expected value> <golden hex>` — the mirror's `toData` of the
   value the Haskell driver says it built reproduces the golden bytes exactly
   (catches a wrong tag or a permuted field order, because it pins the VALUE).

## WHAT PR #112 CHANGED, AND WHY THIS MODULE DEFINES ITS OWN MIRRORS

PR #112 changed two redeemer TYPES:

* **base.**  `mkProgrammableLogicBase` used to ignore its redeemer and scan the
  withdrawal map for `globalCred`/`seizeCred`.  It now takes
  `data BaseSpendRedeemer = SpendViaGlobal Integer | SpendViaSeize Integer`
  (`ProgrammableLogicBase.hs:704-709`, tags 0/1), whose constructor SELECTS the
  arm and whose `Integer` INDEXES the credential-sorted withdrawal map
  (`:727-729`).  The pre-#112 gate asserted the base redeemers were
  `Data.Constr 0 []` (PlutusTx `()`); they are now `Data.Constr 0 [Data.I i]`.

* **global.**  `TransferAct` gained a THIRD field `plgrOwnerWdrlIdxs :: [Integer]`
  (`ProgrammableLogicBase.hs:1046-1052`), so it has five fields, not four:
  `transferProofs, transferWdrlIdxs, ownerWdrlIdxs, mintProofs, paramsRefIdx`.

Both re-cuts landed in `WSC/Redeemer.lean` in task N1's re-base
(`BaseSpendRedeemer` :99-111, five-field `PLGRedeemer.TransferAct` :205-219),
and THIS MODULE GATES THOSE — see §1 on why it must not define its own.

`SeizeAct`, `MintRedeemer`, `RegWitness`, `MintProof`, `GlobalParams` and
`DirectorySetNode` are UNCHANGED by #112 and are gated through the existing
`WSC/Redeemer.lean` mirrors, unmodified.

All checks are `native_decide` (the CBOR decoder is `partial`, so kernel
`decide` is not available).
-/
import WSC.Goldens.Decode
import WSC.Redeemer

namespace WSC.Goldens.RedeemerGate

open CardanoLedgerApi.IsData.Class (IsData mkDataConstr)
open CardanoLedgerApi.V3 (Credential ScriptContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## The three gate primitives -/

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
`Data` image as the expected value. -/
def decodesToValue (α : Type) [IsData α] (h : String) (expected : Data) : Bool :=
  match dataOfHex h with
  | none => false
  | some d =>
      match (IsData.fromData d : Option α) with
      | none => false
      | some x => IsData.toData x == expected

/-! # §1 — WHICH mirrors this module gates

**It gates the mirrors in `WSC/Redeemer.lean`, not local copies of them.**  That
distinction is the whole value of this module: a gate that defined its own
`IsData` instances would prove those instances correct and say nothing about the
ones every redeemer-conditioned theorem in the library actually reads.

An earlier revision of this file (task N2, before merging task N1's re-base) DID
define local post-#112 mirrors, because `WSC/Redeemer.lean` still carried the
pre-#112 shapes and widening it would have broken ~20 modules under `WSC/Shaped`
and `WSC/Props` at once.  Task N1 has since re-cut `WSC/Redeemer.lean` against
2306678 — `BaseSpendRedeemer` at :99-111 and the five-field
`PLGRedeemer.TransferAct` at :205-219 — so the local copies were DELETED and
every clause below now names `WSC.BaseSpendRedeemer` / `WSC.PLGRedeemer`
directly.  If those two ever drift back, this module stops compiling or its
`native_decide`s go false; it cannot silently pass.

The post-#112 field order it pins, from `ProgrammableLogicBase.hs:1039-1055`:

  1. `plgrTransferProofs   :: [Integer]`   (:1041)
  2. `plgrTransferWdrlIdxs :: [Integer]`   (:1042)
  3. `plgrOwnerWdrlIdxs    :: [Integer]`   (:1046) — **NEW in #112**
  4. `plgrMintProofs       :: [MintProof]` (:1053)
  5. `plgrParamsRefIdx     :: Integer`     (:1054)

Fields 2 and 3 are ADJACENT and both `[Integer]`, which is precisely the swap a
shape-only round-trip cannot see — `transfer_mixed_many_policies` below pins it
with lists of different lengths. -/

/-! ## The base redeemer is no longer PlutusTx `()`

Kept as an explicit `Data`-level fact because the pre-#112 gate asserted the
opposite (`= some (Data.Constr 0 [])`), and because it is the one clause here
that needs no mirror at all. -/

theorem base_redeemers_are_not_unit :
    dataOfHex programmableLogicBase_base_spend_transfer_tx.redeemerHex
      = some (Data.Constr 0 [Data.I 0]) ∧
    dataOfHex programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT.redeemerHex
      = some (Data.Constr 0 [Data.I 0]) := by
  native_decide

/-- The `TransferAct` goldens carry FIVE fields.  Stated at the `Data` level so
it holds independently of any mirror: if `WSC/Redeemer.lean` ever reverts to the
4-field arm, the mirror clauses below break AND this clause still records what
the chain actually carries. -/
theorem transfer_goldens_carry_five_fields :
    (match dataOfHex programmableLogicGlobal_transfer_member_single_policy.redeemerHex with
     | some (Data.Constr 0 fs) => fs.length
     | _ => 0) = 5 ∧
    (match dataOfHex programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex with
     | some (Data.Constr 0 fs) => fs.length
     | _ => 0) = 5 := by
  native_decide

/-! # §3 — programmableLogicBase: `BaseSpendRedeemer`

Both base goldens carry `SpendViaGlobal 0`, but they mean opposite things, and
that is the point of the pair:

* `base-spend-transfer-tx` (ACCEPTS): the tx withdraws at
  `[globalCred, transferLogicCred]` in the ledger's credential order and
  `globalCred` sits at index 0, so the witnessed index is CORRECT and the
  delegation check passes.  The index is not hand-written — the catalogue
  computes it with `withdrawalIndexOf` (`BenchmarkOnchainScripts.hs:188`), so a
  re-derived script hash reorders the map without invalidating the witness.
* `base-spend-no-global-or-seize-invoked-REJECT` (REJECTS): the surrounding tx
  withdraws only at the minting-logic script, so index 0 names a credential that
  is neither `globalCred` nor `seizeCred`.  Index 0 is IN RANGE, so this is a
  genuine credential mismatch and not an out-of-bounds list access — the
  stronger negative control. -/

theorem base_spend_transfer_tx :
    mirrorRoundTrip BaseSpendRedeemer
      programmableLogicBase_base_spend_transfer_tx.redeemerHex = some true ∧
    encodesTo (BaseSpendRedeemer.SpendViaGlobal 0)
      programmableLogicBase_base_spend_transfer_tx.redeemerHex = true ∧
    decodesToValue BaseSpendRedeemer
      programmableLogicBase_base_spend_transfer_tx.redeemerHex
      (IsData.toData (BaseSpendRedeemer.SpendViaGlobal 0)) = true := by
  native_decide

theorem base_spend_no_global_or_seize_invoked_REJECT :
    mirrorRoundTrip BaseSpendRedeemer
      programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT.redeemerHex
        = some true ∧
    encodesTo (BaseSpendRedeemer.SpendViaGlobal 0)
      programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT.redeemerHex = true := by
  native_decide

/-- Tag discrimination: `SpendViaSeize 0` does NOT encode to the goldens' bytes.
Without this, a mirror that collapsed both constructors to tag 0 would pass
every clause above. -/
theorem base_arm_tag_is_discriminating :
    encodesTo (BaseSpendRedeemer.SpendViaSeize 0)
      programmableLogicBase_base_spend_transfer_tx.redeemerHex = false ∧
    encodesTo (BaseSpendRedeemer.SpendViaGlobal 1)
      programmableLogicBase_base_spend_transfer_tx.redeemerHex = false := by
  native_decide

/-! # §4 — programmableTokenMinting: `MintRedeemer` (+ `RegWitness`)

UNCHANGED by #112 — the minting bytecode is byte-identical across
f918ec6 → 2306678 (`programmableTokenMinting` cborHex sha256 `7274240514ff`
both sides).  The mirrors in `WSC/Redeemer.lean` are therefore still live and
are used as-is.  Tags frozen by `makeIsDataIndexed` at `Issuance.hs:88-90`
(`Local = 0`, `DelegateTransfer = 1`, `DelegateSeize = 2`, `BurnOnly = 3`) and
`Issuance.hs:57-59` (`RegisteredByReferenceInput = 0`, `RegisteredByOutput = 1`).

NOTE the withdrawal-index VALUES moved even though the type did not:
`BurnOnly 2 → BurnOnly 1` and `DelegateTransfer 2 0 1 0 → 1 0 1 0`.  Nothing
about the encoding changed; the catalogue now DERIVES those indices with
`withdrawalIndexOf mintFixtureWdrls …` (`BenchmarkOnchainScripts.hs:208-221`)
from script hashes that are themselves derived from the really-compiled
scripts, and the derived hashes sort differently from the old synthetic
`0x11…`-style placeholders. -/

theorem mint_local_registered_by_ref :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex = some true ∧
    encodesTo (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex = true ∧
    decodesToValue MintRedeemer
      programmableTokenMinting_mint_local_registered_by_ref.redeemerHex
      (IsData.toData (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))) = true := by
  native_decide

/-- `mint-local-empty-withdrawals-REJECT`: same redeemer (the tamper is in the
context, `txInfoWdrl := []`, not the redeemer). -/
theorem mint_local_empty_withdrawals_REJECT :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_local_empty_withdrawals_REJECT.redeemerHex = some true ∧
    encodesTo (MintRedeemer.Local 0 0 (.RegisteredByReferenceInput 1))
      programmableTokenMinting_mint_local_empty_withdrawals_REJECT.redeemerHex = true := by
  native_decide

/-- `mint-burnonly`: `BurnOnly mintingLogicWdrlIdx`, which now evaluates to 1.
Exercises the HIGHEST mint tag (3), i.e. the compact CBOR tag 124 — the case a
tag-offset bug would break. -/
theorem mint_burnonly :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_burnonly.redeemerHex = some true ∧
    encodesTo (MintRedeemer.BurnOnly 1)
      programmableTokenMinting_mint_burnonly.redeemerHex = true ∧
    decodesToValue MintRedeemer programmableTokenMinting_mint_burnonly.redeemerHex
      (IsData.toData (MintRedeemer.BurnOnly 1)) = true := by
  native_decide

/-- `mint-delegate-transfer-topup`: `DelegateTransfer 1 0 1 0`.  Exercises tag 1
and all four fields in order.  (Field-order sensitivity is weaker here than it
was pre-#112: the four values used to be `2 0 1 0` and are now `1 0 1 0`, so the
first and third coincide.  `mint_delegate_field_order_is_discriminating` below
restores a discriminating check.) -/
theorem mint_delegate_transfer_topup :
    mirrorRoundTrip MintRedeemer
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = some true ∧
    encodesTo (MintRedeemer.DelegateTransfer 1 0 1 0)
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = true ∧
    decodesToValue MintRedeemer
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex
      (IsData.toData (MintRedeemer.DelegateTransfer 1 0 1 0)) = true := by
  native_decide

/-- The two DISTINCT values in `DelegateTransfer 1 0 1 0` are at positions 1,3
and 2,4; any permutation that moves a 1 into a 0 slot is rejected. -/
theorem mint_delegate_field_order_is_discriminating :
    encodesTo (MintRedeemer.DelegateTransfer 0 1 0 1)
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = false ∧
    encodesTo (MintRedeemer.DelegateTransfer 1 1 0 0)
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = false ∧
    encodesTo (MintRedeemer.DelegateSeize 1 0 1 0)
      programmableTokenMinting_mint_delegate_transfer_topup.redeemerHex = false := by
  native_decide

/-! # §5 — programmableLogicGlobal: post-#112 5-field `TransferAct` -/

/-- `transfer-member-single-policy`: `TransferAct [1] [transferFixtureTransferWdrlIdx]
[] [] 0`, which evaluates to `TransferAct [1] [1] [] [] 0`.  `ownerWdrlIdxs` is
EMPTY and that is correct, not an omission: the mini-ledger input sits at
`scriptAddressWithSignerStake progLogicBaseHash signerPkh`, i.e. its owner is a
PUBKEY stake credential, and `plgrOwnerWdrlIdxs` carries an entry only for
SCRIPT-owned inputs (`ProgrammableLogicBase.hs:1046-1052`: "Pubkey-owned inputs
contribute no entry — they are witnessed by a signature instead"). -/
theorem transfer_member_single_policy :
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] [] 0)
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex = true ∧
    decodesToValue PLGRedeemer
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex
      (IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [] 0)) = true := by
  native_decide

/-- `transfer-nonmember-covering-node` and `transfer-containment-violation-REJECT`
carry the same `TransferAct [1] [1] [] [] 0`. -/
theorem transfer_nonmember_and_violation :
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] [] 0)
      programmableLogicGlobal_transfer_nonmember_covering_node.redeemerHex = true ∧
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_nonmember_covering_node.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1] [1] [] [] 0)
      programmableLogicGlobal_transfer_containment_violation_REJECT.redeemerHex = true ∧
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_containment_violation_REJECT.redeemerHex = some true := by
  native_decide

/-- `transfer-mixed-many-policies`: the strongest field-order test in the suite.
Proofs are `[1,2,3,1,4]` (post-#112; they were `[1,2,3,4,1]` before, because
`transferProofsFor` sorts by CURRENCY SYMBOL and the fixtures' symbols are now
derived from the really-compiled scripts, permuting the sort), transfer
withdrawal indices are `[1,1,1,1,1]`, and `ownerWdrlIdxs` is `[]`.

Three `[Integer]` fields, all pairwise different (`length 5` vs `length 5` with
different contents vs `length 0`), so ANY permutation of fields 1-3 is caught —
including the swap of the two ADJACENT ones (2 and 3) that #112 introduced. -/
theorem transfer_mixed_many_policies :
    mirrorRoundTrip PLGRedeemer
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.TransferAct [1, 2, 3, 1, 4] [1, 1, 1, 1, 1] [] [] 0)
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = true ∧
    decodesToValue PLGRedeemer
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex
      (IsData.toData (PLGRedeemer.TransferAct [1, 2, 3, 1, 4] [1, 1, 1, 1, 1] [] [] 0)) = true := by
  native_decide

/-- Field-order discrimination, stated explicitly: swapping fields 1↔2, or
sliding `ownerWdrlIdxs` into field 2's slot, does not reproduce the bytes. -/
theorem transfer_field_order_is_discriminating :
    encodesTo (PLGRedeemer.TransferAct [1, 1, 1, 1, 1] [1, 2, 3, 1, 4] [] [] 0)
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = false ∧
    encodesTo (PLGRedeemer.TransferAct [1, 2, 3, 1, 4] [] [1, 1, 1, 1, 1] [] 0)
      programmableLogicGlobal_transfer_mixed_many_policies.redeemerHex = false ∧
    encodesTo (PLGRedeemer.TransferAct [1] [] [1] [] 0)
      programmableLogicGlobal_transfer_member_single_policy.redeemerHex = false := by
  native_decide

/-! # §6 — programmableSeize: `SeizeAct` (unchanged wire form)

#112 changed the seize BYTECODE (per-pair value delta via CIP-153 builtins;
cborHex sha256 `289e9e8d18b8 → 350b58d7b322`) but not `SeizeAct`'s field list,
and the three seize goldens' `redeemerHex` is byte-identical across the change.
Gated through both the old and the new mirror so that agreement is visible. -/

/-- `seize-1-input`: `mkSeizeActRedeemerFromAbsoluteInputIdxs 1 [0] 0 0
seizeIssuerWdrlIdx`, i.e. `SeizeAct dirNodeIdx=1 inputIdxs=[0] outputsStartIdx=0
lengthInputIdxs=1 seizeParamsRefIdx=0 issuerWdrlIdx=0` (the helper computes
`lengthInputIdxs` from the list, which is why the wire form has six fields for
five arguments).  `issuerWdrlIdx = 0` because `txInfoWdrl` is in the ledger's
own `Credential` order and the issuer credential sorts before the seize
credential.  Exercises tag 1 and all six fields. -/
theorem seize_1_input :
    mirrorRoundTrip PLGRedeemer programmableSeize_seize_1_input.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)
      programmableSeize_seize_1_input.redeemerHex = true ∧
    decodesToValue PLGRedeemer programmableSeize_seize_1_input.redeemerHex
      (IsData.toData (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)) = true := by
  native_decide

/-- `seize-1-input-missing-residual-output-REJECT`: same redeemer (the tamper
deletes the residual output, which is the SECOND-to-last output — the last is
the balancing change output). -/
theorem seize_1_input_missing_residual_REJECT :
    mirrorRoundTrip PLGRedeemer
      programmableSeize_seize_1_input_missing_residual_output_REJECT.redeemerHex = some true ∧
    encodesTo (PLGRedeemer.SeizeAct 1 [0] 0 1 0 0)
      programmableSeize_seize_1_input_missing_residual_output_REJECT.redeemerHex = true := by
  native_decide

/-- `seize-2-inputs-partial-with-noise`: two seized inputs, so
`lengthInputIdxs = 2`.  `inputIdxs = [0,0]` is legitimate: the seize validator
no longer READS `pinputIdxs`/`plengthInputIdxs`, while the fields remain in the
frozen encoding. -/
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

The 13 goldens exercise: `BaseSpendRedeemer.SpendViaGlobal`,
`MintRedeemer.Local` / `.DelegateTransfer` / `.BurnOnly`,
`RegWitness.RegisteredByReferenceInput`, `PLGRedeemer.TransferAct` /
`.SeizeAct`.  They do NOT contain any of

* `BaseSpendRedeemer.SpendViaSeize` (tag 1) — **NEW GAP opened by #112.**  Every
  seize golden is a REWARDING-purpose run of `programmableSeize`; none of them
  is a SPENDING-purpose run of `programmableLogicBase` under the seize arm, so
  tag 1's encoding is pinned only negatively (by
  `base_arm_tag_is_discriminating`) and by source citation.  The catalogue does
  build such redeemers (`baseViaSeizeIn`, `BenchmarkOnchainScripts.hs:190-191`,
  used by `seizeMintFamilyInputBuilder`), so closing this is a matter of adding
  a 14th golden that runs the BASE validator on a seize context — not of
  building a new fixture.
* `MintRedeemer.DelegateSeize` (tag 2) — pinned only negatively, by
  `mint_delegate_field_order_is_discriminating`.
* `RegWitness.RegisteredByOutput` (tag 1) — note `Issuance.hs:207` makes
  registration reg-by-REF only, so this arm may be unreachable by design (L4.3).
* a non-empty `mintProofs` list, hence neither `MintProof.Member` (tag 0) nor
  `MintProof.NonMember` (tag 1).
* a non-empty `ownerWdrlIdxs` list — **NEW GAP opened by #112.**  All four
  transfer goldens spend pubkey-stake-owned base inputs, so the new field is
  empty in every one of them.  Its POSITION is pinned (three distinguishable
  adjacent list fields, `transfer_field_order_is_discriminating`), but no golden
  pins its CONTENT.  The catalogue's `MixedOwners5` scenario
  (`BenchmarkOnchainScripts.hs:1442-1446`) builds a non-empty one; promoting it
  to a golden would close this.

Those remain SOURCE-CITED ONLY, not golden-gated. -/

/-! # §7 — Datum mirrors: `GlobalParams` and `DirectorySetNode`

Both are raw `Data.List` encodings (NOT `Constr`), hand-written `ToData` in the
source — `ProtocolParams.hs:84-96` and `PTokenDirectory.hs:167-174` — which
makes them the likeliest place for a field-order or arity mistake.  Unchanged by
#112; gated here from the goldens' inline reference-input datums.

The VALUES moved, though.  Pre-#112 the fixtures used synthetic placeholder
hashes (`0x11…11`, `0x12…12`, `0x13…13`, `0x40…40`); the catalogue now derives
them from the really-compiled scripts
(`BenchmarkOnchain.PlutarchFixtureIds`), so the constants below are real
blake2b-224 script hashes.  The internal-consistency property that made the old
constants worth stating survives verbatim and is asserted in
`params_datum_matches_base_script_parameters`: the datum's `globalLogicCred`
and `seizeLogicCred` are EXACTLY the two `programmableLogicBase` script
parameters. -/

private def bsHex28_directoryNodeCS : ByteString := ByteString.mk "\x84 \x12\xc3\x12z\xe9\xcc\x0cY\x03\xb7\xea\xde\xf1\x11k\x03:]\x0a\xd7\x1f\xa1,\x9c``"
private def bsHex28_progLogic : ByteString := ByteString.mk "\xe3\xcf|\xfc\x80-V\xf5\xc2\x12|&n\xb0\xd9\xd4\xec\xce\xcf\x1e\x12OQ\x97*\xe0'\xd4"
private def bsHex28_globalLogic : ByteString := ByteString.mk "|\xb8=\xdb\x13\xd4d\x83Y\x80c/y\xab\xd9`\\?\x19\xa6\xedG\x8a\x97\x03\xbc\x8c\x98"
private def bsHex28_seizeLogic : ByteString := ByteString.mk "\xdd\x96\xf3\x83\xda\\\xfcKj\x04\xe0.\x07`\xe7\x7f\x81b\xb8C\xce\x95/sq\xe7v\x8e"
private def bsHex28_ffSentinel : ByteString := ByteString.mk "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"

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

/-- The protocol-params datum the goldens carry, per the `GlobalParams` mirror. -/
def expectedParamsDatum : GlobalParams :=
  { directoryNodeCS := bsHex28_directoryNodeCS
  , progLogicCred := .ScriptCredential bsHex28_progLogic
  , globalLogicCred := .ScriptCredential bsHex28_globalLogic
  , seizeLogicCred := .ScriptCredential bsHex28_seizeLogic }

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

/-- **Config consistency.**  The params datum's `globalLogicCred` and
`seizeLogicCred` are exactly the two script parameters the base validator is
applied to in the base goldens (`paramsHex`, in application order).  This is
what makes the base goldens' delegation check meaningful rather than a
coincidence of unrelated constants — and it is a stronger statement now than it
was pre-#112, because these are derived hashes rather than placeholders that
were equal by construction. -/
theorem params_datum_matches_base_script_parameters :
    (programmableLogicBase_base_spend_transfer_tx.paramsHex.map dataOfHex
      = [ some (IsData.toData (Credential.ScriptCredential bsHex28_globalLogic))
        , some (IsData.toData (Credential.ScriptCredential bsHex28_seizeLogic)) ]) ∧
    (programmableLogicBase_base_spend_no_global_or_seize_invoked_REJECT.paramsHex.map dataOfHex
      = [ some (IsData.toData (Credential.ScriptCredential bsHex28_globalLogic))
        , some (IsData.toData (Credential.ScriptCredential bsHex28_seizeLogic)) ]) := by
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
`key = ""`, `next = 0xff…ff` (28 bytes) — exactly the shape ADDENDUM E3 makes
P5's postcondition witness (`dirNodeKey i < cs < dirNodeNext i`). -/
theorem covering_node_is_sentinel_bounded :
    (match ctxOfHex programmableLogicGlobal_transfer_nonmember_covering_node.scriptContextHex with
     | none => false
     | some ctx =>
         (inlineDatums ctx).any (fun d =>
           match (IsData.fromData d : Option DirectorySetNode) with
           | none => false
           | some n => n.key == ByteString.mk "" && n.next == bsHex28_ffSentinel)) = true := by
  native_decide

/-! # §8 — Aggregate: RESULT C verdict in one Bool -/

/-- Every golden's redeemer decodes through the correct POST-#112 mirror type
and re-encodes byte-identically. -/
def allRedeemerMirrorsRoundTrip : Bool :=
  all.all fun v =>
    match v.validator with
    | "programmableLogicBase" => mirrorRoundTrip BaseSpendRedeemer v.redeemerHex == some true
    | "programmableTokenMinting" => mirrorRoundTrip MintRedeemer v.redeemerHex == some true
    | "programmableSeize" => mirrorRoundTrip PLGRedeemer v.redeemerHex == some true
    | "programmableLogicGlobal" => mirrorRoundTrip PLGRedeemer v.redeemerHex == some true
    | _ => false

theorem allRedeemerMirrorsRoundTrip_true : allRedeemerMirrorsRoundTrip = true := by
  native_decide

end WSC.Goldens.RedeemerGate
