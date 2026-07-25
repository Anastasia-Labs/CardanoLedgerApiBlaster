/-
WSC/Spec.lean — the ground-truth vocabulary (arch §3) used in every theorem
postcondition, plus pure redeemer projections (ADDENDUM E8: POSITIONAL mint
classification) and the §3-P2 `seizeStructurePreserved` skeleton.

RULE: every definition here references ONLY ledger ground truth — the
`ScriptContext` fields and the Data-level redeemer/datum encodings mirrored in
WSC/Redeemer.lean — never validator internals. Validator-shaped commentary is
given in doc comments with source citations, but the definitions themselves
are what the ledger sees.
-/
import CardanoLedgerApi.V3
import WSC.Redeemer

namespace WSC

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol TokenName Value
                          MintValue ScriptContext TxInInfo TxOut valueOf)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-! ## §3 ground-truth vocabulary -/

/-- Payment credential of an output (ledger ground truth: the address's
payment credential; staking credential deliberately ignored — mini-ledger
ownership is carried by the staking credential while the payment credential is
the shared programmable-logic base script). -/
def payCred (o : TxOut) : Credential :=
  o.txOutAddress.addressCredential

/-- `o` is an output sitting at the mini-ledger base payment credential. -/
def outAtBase (base : Credential) (o : TxOut) : Bool :=
  payCred o == base

/-- `i` is a transaction input spent from the mini-ledger base payment
credential. -/
def inAtBase (base : Credential) (i : TxInInfo) : Bool :=
  outAtBase base i.txInInfoResolved

/-- Signed minted quantity of asset `(cs, tn)` in the transaction mint field
(0 when absent). Ground truth only: `txInfoMint` lookup. -/
def mintOf (cs : CurrencySymbol) (tn : TokenName) (mint : MintValue) : Integer :=
  valueOf cs tn mint

/-- Some token name under `cs` has a strictly positive quantity in the token
map `tns` (Data-level walk over `(tn, qty)` pairs). -/
def anyPosTokens : List (Data × Data) → Bool
  | [] => false
  | (_, Data.I n) :: rest => n > 0 || anyPosTokens rest
  | _ :: rest => anyPosTokens rest

/-- The transaction mints a strictly positive quantity of SOME token under
policy `cs` (ground truth over `txInfoMint`; a pure burn of `cs` — all
quantities negative — yields `false`). -/
def mintPos (cs : CurrencySymbol) : MintValue → Bool
  | [] => false
  | (Data.B cs', Data.Map tns) :: rest =>
      if cs' == cs then anyPosTokens tns else mintPos cs rest
  | _ :: rest => mintPos cs rest

/-! ## Pure redeemer projections (Data-level, per WSC/Redeemer.lean mirrors) -/

/-- The redeemer Data decodes to `TransferAct` (tag 0 —
ProgrammableLogicBase.hs:1066-1068). -/
def isTransferAct (r : Data) : Bool :=
  match (IsData.fromData r : Option PLGRedeemer) with
  | some (.TransferAct ..) => true
  | _ => false

/-- The redeemer Data decodes to `SeizeAct` (tag 1 —
ProgrammableLogicBase.hs:1066-1068). -/
def isSeizeAct (r : Data) : Bool :=
  match (IsData.fromData r : Option PLGRedeemer) with
  | some (.SeizeAct ..) => true
  | _ => false

/-- The issuance redeemer Data decodes to `DelegateSeize` (tag 2 —
Issuance.hs:88-90). -/
def isDelegateSeize (r : Data) : Bool :=
  match (IsData.fromData r : Option MintRedeemer) with
  | some (.DelegateSeize ..) => true
  | _ => false

/-- The mint-proof list of a `TransferAct` redeemer, if the Data decodes as
one. -/
def transferMintProofs (r : Data) : Option (List MintProof) :=
  match (IsData.fromData r : Option PLGRedeemer) with
  | some (.TransferAct _ _ ms _) => some ms
  | _ => none

/-- POSITIONAL mint classification (ADDENDUM E8).

The global validator's mint walk consumes ONE proof per non-Ada mint entry, in
the sorted order of `txInfoMint` (no-omission: missing proof errors at
ProgrammableLogicBase.hs:1018, extra proof errors at :1024). Consequently the
classification of a policy `cs` is the proof at the POSITION of `cs` in the
sorted mint entries, walked in lockstep with the proof list — NOT "some proof
somewhere says Member". This function returns that positional proof; `none`
when `cs` is not minted or the lists misalign before reaching `cs`. -/
def mintProofFor (cs : CurrencySymbol) : List MintProof → MintValue → Option MintProof
  | p :: ps, (Data.B cs', _) :: ms =>
      if cs' == cs then some p else mintProofFor cs ps ms
  | _, _ => none

/-- `cs`'s positional mint proof is `Member` (tag 0). -/
def classifiedMember (proofs : List MintProof) (mint : MintValue) (cs : CurrencySymbol) : Bool :=
  match mintProofFor cs proofs mint with
  | some .Member => true
  | _ => false

/-- `cs`'s positional mint proof is `NonMember` (tag 1, any node index). -/
def classifiedNonMember (proofs : List MintProof) (mint : MintValue) (cs : CurrencySymbol) : Bool :=
  match mintProofFor cs proofs mint with
  | some (.NonMember _) => true
  | _ => false

/-! ## §3-P2: seize structure preservation (skeleton) -/

/-- Drop the (single, sorted-in-at-most-one-position) entry for policy `cs`
from a Data-level value. Ground truth helper for "all policies other than the
seized one are unchanged". -/
def dropCS (cs : CurrencySymbol) : Value → Value
  | [] => []
  | (Data.B cs', m) :: rest =>
      if cs' == cs then dropCS cs rest else (Data.B cs', m) :: dropCS cs rest
  | e :: rest => e :: dropCS cs rest

/-- One paired seize input/output preserves address, datum and reference
script exactly, and every policy other than the seized `seizedCS` (including
Ada) byte-for-byte.

Validator-side counterpart (NOT referenced — commentary only): address +
datum/refScript equality at ProgrammableLogicBase.hs:1459-1465, non-target
policy equality inside `pvalueEqualsDeltaCurrencySymbol`
(ProgrammableLogicBase.hs:1677-1830). -/
def pairPreserved (seizedCS : CurrencySymbol) (inp out : TxOut) : Bool :=
  inp.txOutAddress == out.txOutAddress &&
  inp.txOutDatum == out.txOutDatum &&
  inp.txOutReferenceScript == out.txOutReferenceScript &&
  dropCS seizedCS inp.txOutValue == dropCS seizedCS out.txOutValue

/-- §3-P2 SKELETON: structural preservation of the seize transformation,
expressed over ledger ground truth.

Walk EVERY transaction input in order. Each input at the base payment
credential is paired with the next output of the paired-output cursor
(`pairedOutputs` = `txInfoOutputs` from the redeemer's `outputsStartIdx`
onward), and the pair must be preserved outside the seized policy
(`pairPreserved`); non-base inputs are skipped without consuming an output.

Validator-side counterpart (commentary): the every-input walk at
ProgrammableLogicBase.hs:1523-1545 and per-pair check at :1429-1475.

NOTE (skeleton): this captures the STRUCTURE only. The quantity side of P2 —
the accumulated seized-policy delta plus its mint/burn remains contained in
the remaining base outputs (ProgrammableLogicBase.hs:1499-1521) — is layered
on top of this predicate in the P2 proof task. -/
def seizeStructurePreserved (base : Credential) (seizedCS : CurrencySymbol) :
    List TxInInfo → List TxOut → Bool
  | [], _ => true
  | i :: rest, pairedOutputs =>
      if inAtBase base i then
        match pairedOutputs with
        | [] => false
        | o :: os =>
            pairPreserved seizedCS i.txInInfoResolved o &&
            seizeStructurePreserved base seizedCS rest os
      else
        seizeStructurePreserved base seizedCS rest pairedOutputs

end WSC
