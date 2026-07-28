/-
WSC/Redeemer.lean (ADDENDUM E8) — Lean mirrors of the on-chain redeemer and
datum types, with `IsData` instances that reproduce the EXACT Data encodings
produced by the Haskell `makeIsDataIndexed` / hand-written `ToData` instances.

Every constructor tag, field order and encoding shape carries a source
citation (file:line into input-output-hk/wsc-poc at commit
2306678fb03b615d4e58ae207e3eccf9b3676b9b on main — the PR #112 squash-merge,
and the commit the four `WSC/flats/*.flat` are exported from; see
WSC/flats/PROVENANCE.md).

**RE-BASED ON PR #112 (task N1, 2026-07-28).** The previous revision of this
file cited f918ec6 (PR #110). PR #112 changed two of the four mirrored redeemer
encodings; both changes are transcribed here and both are load-bearing:

* **NEW `BaseSpendRedeemer`.** The base spending validator's redeemer used to be
  `()` and was not read at all; it is now a two-constructor type selecting the
  delegation arm and carrying a withdrawal index
  (ProgrammableLogicBase.hs:704-709, read at :720-731). There was deliberately
  no mirror for `()`; there is one now.
* **`PLGRedeemer.TransferAct` gained a THIRD field, `ownerWdrlIdxs`**, so the
  arm has five fields, not four (ProgrammableLogicBase.hs:1039-1055).

`PLGRedeemer.SeizeAct`, `MintProof`, `RegWitness`, `MintRedeemer`,
`DirectorySetNode` and `GlobalParams` were CHECKED, not assumed, to be
unchanged: `git diff f918ec6 2306678 -- <Issuance.hs> <PTokenDirectory.hs>
<ProtocolParams.hs>` is empty, and the two `ProgrammableLogicBase.hs`
declarations are transcribed below from the 2306678 text.

IsData instance style follows Tests/Scripts/SellNFT/Properties.lean.
-/
import CardanoLedgerApi.V3
import PlutusCore

namespace WSC

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Credential CurrencySymbol)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-! ## List helpers (Data.List of I / of mirrored elements) -/

/-- `[Integer]` under `makeIsDataIndexed` fields encodes as `Data.List` of
`Data.I` entries (standard PlutusTx list-of-Integer encoding). -/
def integersToListData (xs : List Integer) : List Data :=
  xs.map Data.I

def listDataToIntegers : List Data → Option (List Integer)
  | [] => some []
  | Data.I n :: rest =>
      match listDataToIntegers rest with
      | some xs => some (n :: xs)
      | none => none
  | _ => none

instance : IsData (List Integer) where
  toData xs := Data.List (integersToListData xs)
  fromData
  | Data.List ds => listDataToIntegers ds
  | _ => none

/-! ## BaseSpendRedeemer (base spending validator) — NEW at PR #112 -/

/-- Mirror of `BaseSpendRedeemer` — **new in PR #112**; before it, the base
spending validator's redeemer was `()` and was never read, so this file
deliberately carried no mirror for it.

Source (tags frozen by `makeIsDataIndexed`, read off the splice, not assumed):

* data decl: ProgrammableLogicBase.hs:704-707 —
  `data BaseSpendRedeemer = SpendViaGlobal Integer | SpendViaSeize Integer`.
* tags: ProgrammableLogicBase.hs:709 —
  `PlutusTx.makeIsDataIndexed ''BaseSpendRedeemer
     [('SpendViaGlobal, 0), ('SpendViaSeize, 1)]`,
  i.e. **`SpendViaGlobal = 0`, `SpendViaSeize = 1`**.
* Each constructor carries exactly ONE `Integer` field, so the wire form is
  `Constr 0 [I i]` / `Constr 1 [I i]`.

WHAT THE VALIDATOR DOES WITH IT (ProgrammableLogicBase.hs:720-731), because the
MEANING of the two fields is what every base-path theorem now rides on:

* the redeemer is reached by hand off the `ScriptContext` `Constr` fields
  (`witness <- plet $ pasConstr # (phead # (ptail # ctxFields))`, :721) rather
  than through `pmatch`;
* the CONSTRUCTOR TAG selects which parameter the withdrawal credential is
  compared against — tag `0` ⇒ `globalCred`, anything else ⇒ `seizeCred`
  (`claimed = pif (pfstBuiltin # witness #== 0) globalCred seizeCred`, :728).
  Note the `pif` is not an exhaustive match: any tag ≠ 0 takes the seize arm;
* the INTEGER FIELD is an INDEX into the (credential-sorted) withdrawal map,
  reached by `pdropList 6` on the `TxInfo` fields to get `wdrl` and then
  `pdropList <idx>` (:727, :729). The single validated condition is
  `withdrawals[idx].credential == claimed` (:730-731).

There is NO mirror-visible constraint that the index be in range: an
out-of-range index makes `phead` error, which fails the transaction. Per the
in-source rationale (:685-699) a wrong index or wrong arm can only invalidate
the attacker's own transaction. -/
inductive BaseSpendRedeemer where
  | SpendViaGlobal : Integer → BaseSpendRedeemer
  | SpendViaSeize : Integer → BaseSpendRedeemer
deriving Repr

instance : IsData BaseSpendRedeemer where
  toData
  | .SpendViaGlobal i => mkDataConstr 0 [Data.I i]
  | .SpendViaSeize i => mkDataConstr 1 [Data.I i]
  fromData
  | Data.Constr 0 [Data.I i] => some (.SpendViaGlobal i)
  | Data.Constr 1 [Data.I i] => some (.SpendViaSeize i)
  | _ => none

/-! ## MintProof -/

/-- Mirror of `MintProof` — classification of one minted currency symbol
against the directory.

Source (constructor tags frozen by `makeIsDataIndexed`; VERIFIED unchanged by
PR #112, re-read at 2306678):
* data decl: ProgrammableLogicBase.hs:1030-1033 (`Member | NonMember Integer`)
* tags: ProgrammableLogicBase.hs:1035-1037 — `Member = 0`, `NonMember = 1`.
* Plutarch mirror confirming shape: `PMintProof` ProgrammableLogicBase.hs:943-948
  (`PNonMember {pnonMemberNodeIdx :: PAsData PInteger}`). -/
inductive MintProof where
  | Member : MintProof
  | NonMember : Integer → MintProof
deriving Repr

instance : IsData MintProof where
  toData
  | .Member => mkDataConstr 0 []
  | .NonMember nodeIdx => mkDataConstr 1 [Data.I nodeIdx]
  fromData
  | Data.Constr 0 [] => some .Member
  | Data.Constr 1 [Data.I nodeIdx] => some (.NonMember nodeIdx)
  | _ => none

def mintProofsToListData (xs : List MintProof) : List Data :=
  xs.map IsData.toData

def listDataToMintProofs : List Data → Option (List MintProof)
  | [] => some []
  | d :: rest =>
      match (IsData.fromData d : Option MintProof), listDataToMintProofs rest with
      | some p, some xs => some (p :: xs)
      | _, _ => none

instance : IsData (List MintProof) where
  toData xs := Data.List (mintProofsToListData xs)
  fromData
  | Data.List ds => listDataToMintProofs ds
  | _ => none

/-! ## ProgrammableLogicGlobalRedeemer (global transfer + seize validators) -/

/-- Mirror of `ProgrammableLogicGlobalRedeemer`.

**CHANGED BY PR #112: `TransferAct` has FIVE fields, not four.**
`plgrOwnerWdrlIdxs` was inserted as the THIRD field. Field order is transcribed
below from the record declaration at 2306678, position by position.

Source (tags frozen by `makeIsDataIndexed`, ProgrammableLogicBase.hs:1067-1069:
`TransferAct = 0`, `SeizeAct = 1`):

* `TransferAct` fields, in order (ProgrammableLogicBase.hs:1039-1055):
  1. `plgrTransferProofs   :: [Integer]`   (:1041)
  2. `plgrTransferWdrlIdxs :: [Integer]`   (:1042)
  3. `plgrOwnerWdrlIdxs    :: [Integer]`   (:1046)  ← **NEW at PR #112**
  4. `plgrMintProofs       :: [MintProof]` (:1053)
  5. `plgrParamsRefIdx     :: Integer`     (:1054)
* `SeizeAct` fields, in order (ProgrammableLogicBase.hs:1056-1064) —
  VERIFIED UNCHANGED by PR #112, field for field, at 2306678:
  1. `plgrDirectoryNodeIdx :: Integer`    (:1057)
  2. `plgrInputIdxs        :: [Integer]`  (:1058)
  3. `plgrOutputsStartIdx  :: Integer`    (:1059)
  4. `plgrLengthInputIdxs  :: Integer`    (:1060)
  5. `plgrSeizeParamsRefIdx :: Integer`   (:1061)
  6. `plgrIssuerWdrlIdx    :: Integer`    (:1062)

Plutarch mirror confirming field order/types: `PProgrammableLogicGlobalRedeemer`
ProgrammableLogicBase.hs:1136-1163 (`PTransferAct` fields at :1146-1150 — note
`pownerWdrlIdxs` third, at :1148 — and `PSeizeAct` at :1154-1159).

**FIDELITY WARNING — THREE ADJACENT `[Integer]` FIELDS.** `TransferAct`'s first
three fields are now ALL `[Integer]`. A permutation of any two of them
typechecks, elaborates, and proves exactly the same theorems while being about
a different redeemer. Neither the Lean type signature nor `deriving Repr` can
see the difference. The ONLY thing in this library that can is
`WSC/Goldens/RedeemerGate.lean`'s `encodesTo`/`decodesToValue` clauses, which
pin the VALUE against golden CBOR emitted by the Haskell driver — and they only
catch it if the goldens carry three DISTINCT lists (the pre-#112 gate relied on
exactly that: `transfer_mixed_many_policies` used `[1,2,3,4,1]` vs
`[1,1,1,1,1]`). Whoever regenerates the goldens must keep that property and
extend it to the third field.

Semantics of the new field, from the source comment (:1046-1052): it is the
withdrawal index of the OWNER script of each script-owned mini-ledger input, in
input order; pubkey-owned inputs contribute NO entry (they are witnessed by a
signature instead), so this list is NOT in general the same length as
`plgrTransferProofs`.

Note (fidelity, still true at 2306678): the seize validator does not READ
`pinputIdxs`/`plengthInputIdxs` (ProgrammableLogicBase.hs:1316-1320) but the
fields remain in the frozen encoding, so they are mirrored here. -/
inductive PLGRedeemer where
  | TransferAct
      (transferProofs : List Integer)
      (transferWdrlIdxs : List Integer)
      (ownerWdrlIdxs : List Integer)
      (mintProofs : List MintProof)
      (paramsRefIdx : Integer)
  | SeizeAct
      (directoryNodeIdx : Integer)
      (inputIdxs : List Integer)
      (outputsStartIdx : Integer)
      (lengthInputIdxs : Integer)
      (seizeParamsRefIdx : Integer)
      (issuerWdrlIdx : Integer)
deriving Repr

instance : IsData PLGRedeemer where
  toData
  | .TransferAct ps ws os ms pIdx =>
      mkDataConstr 0
        [ Data.List (integersToListData ps)
        , Data.List (integersToListData ws)
        , Data.List (integersToListData os)
        , Data.List (mintProofsToListData ms)
        , Data.I pIdx
        ]
  | .SeizeAct dirIdx inIdxs outStart lenIn paramsIdx issuerIdx =>
      mkDataConstr 1
        [ Data.I dirIdx
        , Data.List (integersToListData inIdxs)
        , Data.I outStart
        , Data.I lenIn
        , Data.I paramsIdx
        , Data.I issuerIdx
        ]
  fromData
  | Data.Constr 0 [Data.List r_ps, Data.List r_ws, Data.List r_os,
                   Data.List r_ms, Data.I pIdx] =>
      match listDataToIntegers r_ps, listDataToIntegers r_ws,
            listDataToIntegers r_os, listDataToMintProofs r_ms with
      | some ps, some ws, some os, some ms => some (.TransferAct ps ws os ms pIdx)
      | _, _, _, _ => none
  | Data.Constr 1 [Data.I dirIdx, Data.List r_inIdxs, Data.I outStart,
                   Data.I lenIn, Data.I paramsIdx, Data.I issuerIdx] =>
      match listDataToIntegers r_inIdxs with
      | some inIdxs => some (.SeizeAct dirIdx inIdxs outStart lenIn paramsIdx issuerIdx)
      | none => none
  | _ => none

/-! ## RegistrationWitness + MintRedeemer (issuance minting policy) -/

/-- Mirror of `RegistrationWitness` — how the minted policy proves directory
registration.

Source — `Issuance.hs` is BYTE-IDENTICAL between f918ec6 and 2306678
(`git diff` empty), so every line number below resolves unchanged at 2306678.
(tags frozen by `makeIsDataIndexed`, Issuance.hs:57-59:
`RegisteredByReferenceInput = 0`, `RegisteredByOutput = 1`); data decl
Issuance.hs:52-55 — each constructor carries one `Integer` index. -/
inductive RegWitness where
  | RegisteredByReferenceInput : Integer → RegWitness
  | RegisteredByOutput : Integer → RegWitness
deriving Repr

instance : IsData RegWitness where
  toData
  | .RegisteredByReferenceInput i => mkDataConstr 0 [Data.I i]
  | .RegisteredByOutput i => mkDataConstr 1 [Data.I i]
  fromData
  | Data.Constr 0 [Data.I i] => some (.RegisteredByReferenceInput i)
  | Data.Constr 1 [Data.I i] => some (.RegisteredByOutput i)
  | _ => none

/-- Mirror of `MintRedeemer` — the custody witness of the issuance policy.

Source — `Issuance.hs` VERIFIED unchanged by PR #112 (byte-identical file).
(tags frozen by `makeIsDataIndexed`, Issuance.hs:88-90:
`Local = 0`, `DelegateTransfer = 1`, `DelegateSeize = 2`, `BurnOnly = 3`):

* `Local` fields (Issuance.hs:66-70):
  1. `mrMintingLogicWdrlIdx :: Integer` (:67)
  2. `mrParamsRefIdx :: Integer` (:68)
  3. `mrRegistration :: RegistrationWitness` (:69)
* `DelegateTransfer` fields (Issuance.hs:71-76):
  1. `mrMintingLogicWdrlIdx` (:72)  2. `mrParamsRefIdx` (:73)
  3. `mrNodeRefIdx` (:74)  4. `mrGlobalWdrlIdx` (:75)
* `DelegateSeize` fields (Issuance.hs:77-82):
  1. `mrMintingLogicWdrlIdx` (:78)  2. `mrParamsRefIdx` (:79)
  3. `mrNodeRefIdx` (:80)  4. `mrSeizeRedeemerIdx` (:81)
* `BurnOnly` fields (Issuance.hs:83-85):
  1. `mrMintingLogicWdrlIdx` (:84)

Plutarch mirror confirming shape: `PMintRedeemer` Issuance.hs:99-122. -/
inductive MintRedeemer where
  | Local
      (mintingLogicWdrlIdx : Integer)
      (paramsRefIdx : Integer)
      (registration : RegWitness)
  | DelegateTransfer
      (mintingLogicWdrlIdx : Integer)
      (paramsRefIdx : Integer)
      (nodeRefIdx : Integer)
      (globalWdrlIdx : Integer)
  | DelegateSeize
      (mintingLogicWdrlIdx : Integer)
      (paramsRefIdx : Integer)
      (nodeRefIdx : Integer)
      (seizeRedeemerIdx : Integer)
  | BurnOnly
      (mintingLogicWdrlIdx : Integer)
deriving Repr

instance : IsData MintRedeemer where
  toData
  | .Local w p r => mkDataConstr 0 [Data.I w, Data.I p, IsData.toData r]
  | .DelegateTransfer w p n g => mkDataConstr 1 [Data.I w, Data.I p, Data.I n, Data.I g]
  | .DelegateSeize w p n s => mkDataConstr 2 [Data.I w, Data.I p, Data.I n, Data.I s]
  | .BurnOnly w => mkDataConstr 3 [Data.I w]
  fromData
  | Data.Constr 0 [Data.I w, Data.I p, r_reg] =>
      match (IsData.fromData r_reg : Option RegWitness) with
      | some r => some (.Local w p r)
      | none => none
  | Data.Constr 1 [Data.I w, Data.I p, Data.I n, Data.I g] =>
      some (.DelegateTransfer w p n g)
  | Data.Constr 2 [Data.I w, Data.I p, Data.I n, Data.I s] =>
      some (.DelegateSeize w p n s)
  | Data.Constr 3 [Data.I w] => some (.BurnOnly w)
  | _ => none

/-! ## DirectorySetNode (directory-node datum) -/

/-- Mirror of the `DirectorySetNode` datum.

FIDELITY-CRITICAL encoding fact: this datum is encoded as a **`Data.List` of 5
elements** (raw list, NOT a `Constr`!):

(`PTokenDirectory.hs` VERIFIED byte-identical between f918ec6 and 2306678.)

* data decl + field order: PTokenDirectory.hs:144-150 —
  1. `key : CurrencySymbol` 2. `next : CurrencySymbol`
  3. `transferLogicScript : Credential` 4. `issuerLogicScript : Credential`
  5. `globalStateCS : CurrencySymbol`.
* hand-written `ToData`: PTokenDirectory.hs:167-174 — `BI.mkList (key : next :
  transferLogicScript : issuerLogicScript : globalStateCS : [])`.
* hand-written `FromData` (list decode): PTokenDirectory.hs:154-165.
* Plutarch mirror via `DeriveAsDataRec` (data-record = list encoding):
  PTokenDirectory.hs:176-186.

NOTE (deviation from older docs): the node has a FIFTH field `globalStateCS`
beyond key/next/transferLogicScript/issuerLogicScript. -/
structure DirectorySetNode where
  key : CurrencySymbol
  next : CurrencySymbol
  transferLogicScript : Credential
  issuerLogicScript : Credential
  globalStateCS : CurrencySymbol
deriving Repr

instance : IsData DirectorySetNode where
  toData d :=
    Data.List
      [ Data.B d.key
      , Data.B d.next
      , IsData.toData d.transferLogicScript
      , IsData.toData d.issuerLogicScript
      , Data.B d.globalStateCS
      ]
  fromData
  | Data.List [Data.B k, Data.B n, r_tls, r_ils, Data.B g] =>
      match (IsData.fromData r_tls : Option Credential),
            (IsData.fromData r_ils : Option Credential) with
      | some tls, some ils => some ⟨k, n, tls, ils, g⟩
      | _, _ => none
  | _ => none

/-! ## ProgrammableLogicGlobalParams (protocol-params datum) -/

/-- Mirror of the `ProgrammableLogicGlobalParams` protocol-params datum.

FIDELITY-CRITICAL encoding fact: encoded as a **`Data.List` of 4 elements**
(raw list, NOT a `Constr`); field order is NORMATIVE and consensus-critical
(the issuance policy raw-accesses positions):

(`ProtocolParams.hs` VERIFIED byte-identical between f918ec6 and 2306678.)

* data decl + normative field-order comment: ProtocolParams.hs:44-68 —
  0. `directoryNodeCS : CurrencySymbol` 1. `progLogicCred : Credential`
  2. `globalLogicCred : Credential` 3. `seizeLogicCred : Credential`.
* hand-written `ToData` (`BI.mkList`): ProtocolParams.hs:84-96.
* hand-written `FromData` (list decode): ProtocolParams.hs:70-82.
* Plutarch mirror via `DeriveAsDataRec`: ProtocolParams.hs:98-108. -/
structure GlobalParams where
  directoryNodeCS : CurrencySymbol
  progLogicCred : Credential
  globalLogicCred : Credential
  seizeLogicCred : Credential
deriving Repr

instance : IsData GlobalParams where
  toData p :=
    Data.List
      [ Data.B p.directoryNodeCS
      , IsData.toData p.progLogicCred
      , IsData.toData p.globalLogicCred
      , IsData.toData p.seizeLogicCred
      ]
  fromData
  | Data.List [Data.B dcs, r_plc, r_glc, r_slc] =>
      match (IsData.fromData r_plc : Option Credential),
            (IsData.fromData r_glc : Option Credential),
            (IsData.fromData r_slc : Option Credential) with
      | some plc, some glc, some slc => some ⟨dcs, plc, glc, slc⟩
      | _, _, _ => none
  | _ => none

end WSC
