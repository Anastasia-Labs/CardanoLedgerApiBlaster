/-
WSC/Redeemer.lean (ADDENDUM E8) — Lean mirrors of the on-chain redeemer and
datum types, with `IsData` instances that reproduce the EXACT Data encodings
produced by the Haskell `makeIsDataIndexed` / hand-written `ToData` instances.

Every constructor tag, field order and encoding shape carries a source
citation (file:line into input-output-hk/wsc-poc at commit
f918ec6dcef4398952febe11e84fda089c064374 on main — the PR #110 squash-merge.
The line numbers were read at the export commit
7ae0024b185cf16f17e38c20c9ee97ae1410c51f, whose tree is identical, so they
resolve unchanged at f918ec6; see WSC/flats/PROVENANCE.md).

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

/-! ## MintProof -/

/-- Mirror of `MintProof` — classification of one minted currency symbol
against the directory.

Source (constructor tags frozen by `makeIsDataIndexed`):
* data decl: ProgrammableLogicBase.hs:1036-1039 (`Member | NonMember Integer`)
* tags: ProgrammableLogicBase.hs:1041-1043 — `Member = 0`, `NonMember = 1`.
* Plutarch mirror confirming shape: `PMintProof` ProgrammableLogicBase.hs:948-953
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

Source (tags frozen by `makeIsDataIndexed`, ProgrammableLogicBase.hs:1066-1068:
`TransferAct = 0`, `SeizeAct = 1`):

* `TransferAct` fields, in order (ProgrammableLogicBase.hs:1046-1054):
  1. `plgrTransferProofs   :: [Integer]`  (:1047)
  2. `plgrTransferWdrlIdxs :: [Integer]`  (:1048)
  3. `plgrMintProofs       :: [MintProof]` (:1052)
  4. `plgrParamsRefIdx     :: Integer`    (:1053)
* `SeizeAct` fields, in order (ProgrammableLogicBase.hs:1055-1063):
  1. `plgrDirectoryNodeIdx :: Integer`    (:1057)
  2. `plgrInputIdxs        :: [Integer]`  (:1058)
  3. `plgrOutputsStartIdx  :: Integer`    (:1059)
  4. `plgrLengthInputIdxs  :: Integer`    (:1060)
  5. `plgrSeizeParamsRefIdx :: Integer`   (:1061)
  6. `plgrIssuerWdrlIdx    :: Integer`    (:1062)

Plutarch mirror confirming field order/types: `PProgrammableLogicGlobalRedeemer`
ProgrammableLogicBase.hs:1135-1159. Note (fidelity): the current seize
validator no longer READS `pinputIdxs`/`plengthInputIdxs`
(ProgrammableLogicBase.hs:1299-1304) but the fields remain in the frozen
encoding, so they are mirrored here. -/
inductive PLGRedeemer where
  | TransferAct
      (transferProofs : List Integer)
      (transferWdrlIdxs : List Integer)
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
  | .TransferAct ps ws ms pIdx =>
      mkDataConstr 0
        [ Data.List (integersToListData ps)
        , Data.List (integersToListData ws)
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
  | Data.Constr 0 [Data.List r_ps, Data.List r_ws, Data.List r_ms, Data.I pIdx] =>
      match listDataToIntegers r_ps, listDataToIntegers r_ws, listDataToMintProofs r_ms with
      | some ps, some ws, some ms => some (.TransferAct ps ws ms pIdx)
      | _, _, _ => none
  | Data.Constr 1 [Data.I dirIdx, Data.List r_inIdxs, Data.I outStart,
                   Data.I lenIn, Data.I paramsIdx, Data.I issuerIdx] =>
      match listDataToIntegers r_inIdxs with
      | some inIdxs => some (.SeizeAct dirIdx inIdxs outStart lenIn paramsIdx issuerIdx)
      | none => none
  | _ => none

/-! ## RegistrationWitness + MintRedeemer (issuance minting policy) -/

/-- Mirror of `RegistrationWitness` — how the minted policy proves directory
registration.

Source (tags frozen by `makeIsDataIndexed`, Issuance.hs:57-59:
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

Source (tags frozen by `makeIsDataIndexed`, Issuance.hs:88-90:
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
