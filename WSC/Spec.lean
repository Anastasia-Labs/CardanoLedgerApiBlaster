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
                          MintValue ScriptContext ScriptHash ScriptPurpose
                          RedeemerMap TxInInfo TxOut valueOf hasCurrencySymbol
                          credentialInWithdrawals)
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
  -- FOUR wildcards, not three: PR #112 gave `TransferAct` a THIRD field of
  -- five, `ownerWdrlIdxs` (`ProgrammableLogicBase.hs:1046`,
  -- `WSC/Redeemer.lean`), so `mintProofs` is now the FOURTH positional field.
  -- Applied by task N3 (identified and left unapplied by N1 to avoid three
  -- parallel units colliding on one line); N5 reached the same line
  -- independently and made the identical code change, so the two agree.
  | some (.TransferAct _ _ _ ms _) => some ms
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

/-! ## §3-P4: the four custody predicates of the issuance minting policy

Every definition below is GROUND TRUTH ONLY: `ScriptContext` fields, the
`Value`/`MintValue` Data encodings, and the `IsData` mirrors of
WSC/Redeemer.lean. None of them refers to a validator-computed value, an
index taken from the redeemer is only ever used to *look up* a ledger field,
and the redeemer's constructor is never consulted (see the note on
constructor fall-through in WSC/Props/P4_Minting.lean).

Source: src/programmable-tokens-onchain/lib/SmartTokens/Contracts/Issuance.hs
at wsc-poc worktree `new-session-3c417d` (line numbers read 2026-07-25). -/

/-- **C1 — the minting-logic script ran.** The token's minting-logic script
credential appears in the transaction's withdrawal map.

Validator counterpart (commentary): `mintingLogicCred = pdata $ pcon $
PScriptCredential mintingLogicHash'` (Issuance.hs:136) and
`mintingLogicInvokedAt` (Issuance.hs:150-151), which compares the credential of
the withdrawal entry at the redeemer-supplied index `wdrlIdx` against it. This
predicate is the index-free consequence: whatever index the redeemer names, the
credential is *somewhere* in `txInfoWdrl`. C1 is a conjunct of ALL FOUR arms
(Issuance.hs:195, 216, 242, 253). -/
def mintingLogicInvoked (mintingLogicHash : ScriptHash) (ctx : ScriptContext) : Bool :=
  credentialInWithdrawals (Credential.ScriptCredential mintingLogicHash)
    ctx.scriptContextTxInfo.txInfoWdrl

/-- **Registration NFT presence.** Value `v` holds exactly one directory NFT
under policy `dirCS` whose token name is the *bytes of `cs`*.

Validator counterpart: `hasNodeNFT` (Issuance.hs:156-157) —
`pvalueOf # value # directoryNodeCS # ownAsTokenName #== 1` with
`ownAsTokenName = pcon $ PTokenName (pto ownCS)` (Issuance.hs:141). Since
`CurrencySymbol` and `TokenName` are both `ByteString` abbrevs
(CardanoLedgerApi/V1/Value.lean:11-12), `cs` is used directly as the token
name — that IS `pto ownCS`. -/
def hasNodeNFT (dirCS : CurrencySymbol) (cs : CurrencySymbol) (v : Value) : Bool :=
  valueOf dirCS cs v == 1

/-- Some reference input's resolved value carries `cs`'s directory node NFT.
Index-free consequence of `PRegisteredByReferenceInput` (Issuance.hs:172-173)
and of the reg-by-REF-only delegate arms (Issuance.hs:208-209, 226-227). -/
def anyRefInputHasNodeNFT (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      hasNodeNFT dirCS cs i.txInInfoResolved.txOutValue || anyRefInputHasNodeNFT dirCS cs rest

/-- Some output carries `cs`'s directory node NFT. Index-free consequence of
`PRegisteredByOutput` (Issuance.hs:174-176) — the arm that exists ONLY in
`Local`, and only because `Local` does its own custody scan
(Issuance.hs:166-168). -/
def anyOutputHasNodeNFT (dirCS cs : CurrencySymbol) : List TxOut → Bool
  | [] => false
  | o :: rest =>
      hasNodeNFT dirCS cs o.txOutValue || anyOutputHasNodeNFT dirCS cs rest

/-- **The no-escape scan (Local custody).** Every output whose payment
credential is not the mini-ledger base credential holds zero of `cs`.

Validator counterpart: `noEscape` (Issuance.hs:183-193) — a `pall` over
`ptxInfo'outputs` using RAW field access (`pasConstr` + `phead`/`ptail`, so
datum and reference script are never forced), comparing the output's payment
credential *Data* against `pforgetData pprogLogicCred` (:182, :190) and
otherwise requiring `pnot # (phasCS # value # ownCS)` (:192). Here the
comparison is on decoded `Credential`s rather than their `Data` encodings —
equivalent by injectivity of the `Credential` `IsData` encoding — and
`hasCurrencySymbol` (CardanoLedgerApi/V1/Value.lean:170-173) is the ground-truth
counterpart of `phasCS`. -/
def noEscape (progLogicCred : Credential) (cs : CurrencySymbol) : List TxOut → Bool
  | [] => true
  | o :: rest =>
      (payCred o == progLogicCred || !hasCurrencySymbol cs o.txOutValue)
      && noEscape progLogicCred cs rest

/-- Field-wise equality of two `GlobalParams` (avoids adding a `BEq` derivation
to the frozen mirror in WSC/Redeemer.lean). -/
def paramsBEq (p q : GlobalParams) : Bool :=
  p.directoryNodeCS == q.directoryNodeCS && p.progLogicCred == q.progLogicCred &&
  p.globalLogicCred == q.globalLogicCred && p.seizeLogicCred == q.seizeLogicCred

/-- **The protocol-params view of a transaction.** EVERY reference input that
carries the protocol-params NFT policy `ppCS` has an inline datum decoding to
exactly `p`.

This is the ground-truth hypothesis under which the params-dependent custody
arms can even be *named* (the validator reads `directoryNodeCS`,
`progLogicCred`, `globalLogicCred`, `seizeLogicCred` out of that datum). It is
stated as a ∀-scan, so it RESTRICTS the transaction and cannot smuggle a
postcondition: it says nothing about withdrawals, outputs or the mint map.
Under honest deployment the params NFT is unique, so exactly one reference
input satisfies the guard and `p` is its datum.

Validator counterpart: `pparamsAtRefIdx` (ProgrammableLogicBase.hs:824-838) —
reference input at the redeemer's `paramsRefIdx`, guarded by
`phasCSH # currencySymbol # ptxOutValue` (:832, presence of the policy, NOT an
NFT-quantity check) and decoding `POutputDatum` as
`PProgrammableLogicGlobalParams` (:833-835), erroring otherwise (:836, :838). -/
def paramsView (ppCS : CurrencySymbol) (p : GlobalParams) : List TxInInfo → Bool
  | [] => true
  | i :: rest =>
      (!hasCurrencySymbol ppCS i.txInInfoResolved.txOutValue ||
        (match i.txInInfoResolved.txOutDatum with
         | .OutputDatum d =>
             match (IsData.fromData d : Option GlobalParams) with
             | some q => paramsBEq q p
             | none => false
         | _ => false))
      && paramsView ppCS p rest

/-- Reference input at a redeemer-supplied index, rejecting a negative index.
Validator counterpart: `pcheckedDrop` + `phead` (Issuance.hs:126-130, used at
:172, :208, :226) — the explicit negative-index guard is why `none` is returned
for `idx < 0` instead of clamping to 0. -/
def refInputAt (idx : Integer) (refs : List TxInInfo) : Option TxInInfo :=
  if idx < 0 then none else refs[idx.toNat]?

/-- **The seize-scope binding (DelegateSeize).** Some redeemer entry in
`txInfoRedeemers` is a `Rewarding seizeCred` purpose whose redeemer decodes to a
`SeizeAct`, and that `SeizeAct`'s `directoryNodeIdx` points at a reference input
carrying `cs`'s directory node NFT — i.e. the seize is scoped to `cs`'s node.

Validator counterpart: `seizeEntry` / `seizeScopeOk` (Issuance.hs:231-240) —
the redeemer-map entry at `seizeRedeemerIdx`, its purpose coerced to
`PScriptPurpose` and matched against `PRewarding seizeCred` (:233-234), its
redeemer coerced to `PProgrammableLogicGlobalRedeemer` and matched against
`PSeizeAct` (:235-236), then `pdata seizeCred #== pseizeLogicCred` and
`pdirectoryNodeIdx #== nodeRefIdx` (:237-238) where `nodeRefIdx` is the very
index the `regByRefOk` NFT check used (:226). This predicate is the index-free
consequence: the seize's node index resolves to a reference input keyed `cs`. -/
def seizeScopedToNodeOf (seizeCred : Credential) (dirCS cs : CurrencySymbol)
    (refs : List TxInInfo) : RedeemerMap → Bool
  | [] => false
  | (ScriptPurpose.Rewarding c, r) :: rest =>
      (c == seizeCred &&
        (match (IsData.fromData r : Option PLGRedeemer) with
         | some (.SeizeAct dirIdx _ _ _ _ _) =>
             (match refInputAt dirIdx refs with
              | some i => hasNodeNFT dirCS cs i.txInInfoResolved.txOutValue
              | none => false)
         | _ => false))
      || seizeScopedToNodeOf seizeCred dirCS cs refs rest
  | _ :: rest => seizeScopedToNodeOf seizeCred dirCS cs refs rest

/-! ### The four arms -/

/-- **Arm 1 — `Local` (Issuance.hs:159-198).** The policy proves custody
itself: the minting-logic script ran, `cs` is registered in the directory
(reference input OR output), and no output outside the mini-ledger base
credential holds any `cs`. -/
def LocalCustodyOk (mintingLogicHash : ScriptHash) (p : GlobalParams)
    (cs : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  mintingLogicInvoked mintingLogicHash ctx &&
  (anyRefInputHasNodeNFT p.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs ||
   anyOutputHasNodeNFT p.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoOutputs) &&
  noEscape p.progLogicCred cs ctx.scriptContextTxInfo.txInfoOutputs

/-- **Arm 2 — `DelegateTransfer` (Issuance.hs:200-219).** Custody is delegated
to the global transfer validator: the minting-logic script ran, `cs` is
registered via a REFERENCE INPUT ONLY (F-1: an output-side fresh node would
leave the global's directory view pre-insert — Issuance.hs:204-206), and the
global logic credential appears in the withdrawal map, so the global transfer
validator runs on this transaction (⟹ P1). -/
def DelegateTransferOk (mintingLogicHash : ScriptHash) (p : GlobalParams)
    (cs : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  mintingLogicInvoked mintingLogicHash ctx &&
  anyRefInputHasNodeNFT p.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs &&
  credentialInWithdrawals p.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl

/-- **Arm 3 — `DelegateSeize` (Issuance.hs:221-245).** Custody is delegated to
the standalone seize validator: the minting-logic script ran, `cs` is registered
via a reference input, and a `SeizeAct` redeemer for the params seize credential
is scoped to `cs`'s directory node (⟹ P2). -/
def DelegateSeizeOk (mintingLogicHash : ScriptHash) (p : GlobalParams)
    (cs : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  mintingLogicInvoked mintingLogicHash ctx &&
  anyRefInputHasNodeNFT p.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs &&
  seizeScopedToNodeOf p.seizeLogicCred p.directoryNodeCS cs
    ctx.scriptContextTxInfo.txInfoReferenceInputs ctx.scriptContextTxInfo.txInfoRedeemers

/-- **Arm 4 — `BurnOnly` (Issuance.hs:247-255).** No custody proof is needed
because nothing is created: the minting-logic script ran, and NO token of `cs`
has a strictly positive quantity in `txInfoMint`.

Validator counterpart: `ptryLookupValue # ownCS' # mint` then
`pall # plam (\pair -> pfromData (psndBuiltin # pair) #<= 0)`
(Issuance.hs:251-254) — the WHOLE `ownCS` token map, not just its head
(Issuance.hs:249-250). `mintPos` (this file) is the ground-truth counterpart;
`ptryLookupValue` errors when `ownCS` is absent from the mint map, which
`validMintingContext` excludes anyway (`validScriptInfo` clause 3,
CardanoLedgerApi/V3/Contexts.lean:987: `MintingScript cs → hasCurrencySymbol cs
txInfoMint`). -/
def BurnOnlyOk (mintingLogicHash : ScriptHash) (cs : CurrencySymbol)
    (ctx : ScriptContext) : Bool :=
  mintingLogicInvoked mintingLogicHash ctx &&
  !mintPos cs ctx.scriptContextTxInfo.txInfoMint

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

/-! ### PR #112: the seize pair rule now permits an ADA TOP-UP

`pairPreserved`/`seizeStructurePreserved` above are the PRE-#112 rule and they
are **FALSE of the production bytecode at wsc-poc main `2306678`** — measured,
not inferred: `WSC/Props/Shaped/P2ShapedR.lean`'s `P2a_R_structure` comes back
❌ Falsified with a counterexample whose ONLY defect is `i0Ada = 23101`,
`o0Ada = 36307`, i.e. the continuing output carries MORE ada than the input it
continues.

That relaxation is deliberate, and the reason is in the source
(`ProgrammableLogicBase.hs`, `pvalueEqualsDeltaCurrencySymbol`, the
`adaToppedUp` binding):

> The one non-seized policy a pair may legitimately differ on is ada, and only
> upward. A protocol-parameter change can raise the min-UTxO requirement above
> what a UTxO already holds; demanding the continuing output carry exactly the
> input's lovelace would make every such UTxO permanently unseizable, since the
> ledger would require more ada than this validator allowed.

The check is `pasInt # … #<= pconstantInteger 0` on the ada entry of the delta,
and the delta is `input - output`, so the permitted direction is
`input - output ≤ 0`, i.e. **`output ≥ input`**: ada may be added, NEVER removed.
The asymmetry is the security-relevant half, so it is stated explicitly below
and is what `P2a_R_negative_control` now falsifies-on-violation.

Both spellings are kept: the old one because the pre-#112 results quantify over
it and the audit trail must stay readable, the new one because it is what the
shipped code does. -/

/-- Lovelace held by a `TxOut`. Ground truth only — a `valueOf` lookup at the
ada symbol/token (both the empty `ByteString`, `CardanoLedgerApi/V1/Value.lean`
`adaSymbol`/`adaToken`). -/
def lovelaceOf (o : TxOut) : Integer :=
  valueOf CardanoLedgerApi.V1.adaSymbol CardanoLedgerApi.V1.adaToken o.txOutValue

/-- PR #112 per-pair rule: address, datum and reference script exactly equal;
every policy other than the seized one AND other than ada byte-for-byte equal;
and ada only ever TOPPED UP (`in ≤ out`).

Note the ada clause is an INEQUALITY in one direction only. Replacing it with
`==` gives back `pairPreserved`, which the bytecode refutes; dropping it
entirely would let a seizure drain the continuing output's lovelace, which the
bytecode also refuses (`P2a_R_negative_control`).

The ada clause is GUARDED by `seizedCS ≠ adaSymbol`, and that guard is not
cosmetic — it was forced by a second measured counterexample (task N5). When the
seized policy IS ada, ada's movement is the seizure itself and no top-up rule
can apply. The guard mirrors the validator's own dispatch exactly
(`pvalueEqualsDeltaCurrencySymbol`): the leading entry of the delta is tested
`pfstBuiltin # entry #== progCSData` FIRST, and only if that fails is it
required to be an `adaToppedUp` entry. With `progCS = adaSymbol` the first test
succeeds on the ada entry, so `adaToppedUp` is never reached. -/
def pairPreservedAdaTopUp (seizedCS : CurrencySymbol) (inp out : TxOut) : Bool :=
  inp.txOutAddress == out.txOutAddress &&
  inp.txOutDatum == out.txOutDatum &&
  inp.txOutReferenceScript == out.txOutReferenceScript &&
  dropCS CardanoLedgerApi.V1.adaSymbol (dropCS seizedCS inp.txOutValue) ==
    dropCS CardanoLedgerApi.V1.adaSymbol (dropCS seizedCS out.txOutValue) &&
  (seizedCS == CardanoLedgerApi.V1.adaSymbol ||
    decide (lovelaceOf inp ≤ lovelaceOf out))

/-- `seizeStructurePreserved` with the PR #112 pair rule. The input walk and the
paired-output cursor are IDENTICAL to the pre-#112 version; only `pairPreserved`
is replaced by `pairPreservedAdaTopUp`. -/
def seizeStructurePreservedAdaTopUp (base : Credential) (seizedCS : CurrencySymbol) :
    List TxInInfo → List TxOut → Bool
  | [], _ => true
  | i :: rest, pairedOutputs =>
      if inAtBase base i then
        match pairedOutputs with
        | [] => false
        | o :: os =>
            pairPreservedAdaTopUp seizedCS i.txInInfoResolved o &&
            seizeStructurePreservedAdaTopUp base seizedCS rest os
      else
        seizeStructurePreservedAdaTopUp base seizedCS rest pairedOutputs


end WSC
