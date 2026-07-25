/-
WSC/Goldens/Decode.lean — the golden→Lean bridge (task Y4 step 1).

Turns a golden's `serialiseData` hex (see `WSC/Goldens/Vectors.lean`, generated
from `WSC/goldens/*.json`) into

  (a) PlutusCore `Data`, via PlutusCoreBlaster's CBOR decoder
      (`PlutusCore.Cbor.decodeData`, the exact inverse of
      `PlutusCore.Cbor.encodeData` = the `serialiseData` builtin — the same
      encoder `WSC/goldens/KVerify.lean.disabled` used to prove the applied
      flats carry byte-identical arguments), and then

  (b) a CLAB `CardanoLedgerApi.V3.ScriptContext`, via CLAB's own
      `IsData.fromData` instance (`CardanoLedgerApi/V3/Contexts.lean:587`).

Nothing here is hand-transcribed: the hex comes from the off-chain Haskell
driver, the CBOR decoder from PlutusCoreBlaster, and the `Data → ScriptContext`
step from CLAB.  That is what makes the results in `WSC/LR-CTX-AUDIT.md` and
`WSC/Goldens/Witnesses.lean` evidence about REAL ledger-shaped contexts rather
than about a Lean-side model of them.

EVALUATION STRATEGY (asked for explicitly by the task): every check over these
values is discharged with `native_decide`, never kernel `decide`/`rfl`.  Two
reasons: (i) the decoded contexts are ~1.2 kB of `Data` and the CBOR decoder is
`partial` (`PlutusCore/Cbor/Basic.lean:711-766`), so it has no equational
lemmas the kernel could unfold; (ii) whnf-ing a 1.2 kB `Data` tree through
`validScriptContext` in the kernel is orders of magnitude slower than the
compiled evaluator.  `native_decide` adds the Lean compiler + this module's
`Decidable` instances to the trust base and nothing else.
-/
import WSC.Goldens.Vectors
import CardanoLedgerApi.V3
import PlutusCore

namespace WSC.Goldens

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (ScriptContext ScriptInfo)
-- `CardanoLedgerApi.V3.Contexts` is opened wholesale rather than by name because
-- several of these identifiers (`validMintValue`, `validInputs`, `isBalanced`, …)
-- also exist in V1/V2 and are re-exported into `CardanoLedgerApi.V3`, which makes
-- a named `open CardanoLedgerApi.V3 (…)` ambiguous.  The V3 module is the one the
-- P-theorems' preconditions come from (`WSC/Props/P3_Base.lean`).
open CardanoLedgerApi.V3.Contexts
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

/-! ## Hex ↔ bytes

PlutusCoreBlaster represents a bytestring as a `String` whose `Char`s are the
bytes (`PlutusCore.ByteString`), so hex decoding is byte-wise.  We reuse
PCB's own hex decoder — the one `#import_uplc … double_cbor_hex` runs
(`PlutusCore/UPLC/ScriptEncoding/Basic.lean:42-48`) — so the golden bytes enter
Lean through exactly the same door as the validator bytecode. -/

/-- Hex string → raw byte string (`none` on an odd length or a non-hex digit). -/
def hexToBytes (h : String) : Option String :=
  String.mk <$> PlutusCore.UPLC.ScriptEncoding.Internal.hexStringToString h.data []

private def nibbleHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Raw byte string → lowercase hex (inverse of `hexToBytes` on valid input). -/
def bytesToHex (s : String) : String :=
  String.mk (s.data.flatMap fun c =>
    let b := c.toNat
    [nibbleHex (b / 16), nibbleHex (b % 16)])

/-! ## Hex → Data → ScriptContext -/

/-- Golden hex → `Data`.  Requires the CBOR decoder to consume the WHOLE input:
a trailing-garbage tolerant decode would silently accept a truncated context. -/
def dataOfHex (h : String) : Option Data :=
  match hexToBytes h with
  | none => none
  | some bs =>
      match PlutusCore.Cbor.decodeData bs with
      | some (rest, d) => if rest.isEmpty then some d else none
      | none => none

/-- Golden hex → `Data` → CLAB `ScriptContext` (CLAB's `IsData` instance). -/
def ctxOfHex (h : String) : Option ScriptContext :=
  match dataOfHex h with
  | none => none
  | some d => (IsData.fromData d : Option ScriptContext)

/-- Re-encode a `Data` with PCB's `serialiseData` encoder and hex it. -/
def hexOfData (d : Data) : Option String :=
  bytesToHex <$> PlutusCore.Cbor.encodeData d

/-- `Data`-level round-trip of a hex field: decode, re-encode, compare bytes.
`some true` means byte-identical. -/
def dataRoundTrips (h : String) : Option Bool :=
  match dataOfHex h with
  | none => none
  | some d => (fun h' => h' == h) <$> hexOfData d

/-! ## The matching `validXContext` predicate per validator

Which CLAB predicate a golden must satisfy is fixed by the validator's script
purpose, which is fixed by its Plutarch source (all citations into the wsc-poc
worktree recorded in `WSC/flats/PROVENANCE.md`):

| validator | purpose | CLAB predicate | source |
|---|---|---|---|
| `programmableLogicBase`    | spending  | `validSpendingContext`  | `ProgrammableLogicBase.hs:717-729` (base SPENDING script) |
| `programmableTokenMinting` | minting   | `validMintingContext`   | `Issuance.hs:132` (minting policy) |
| `programmableSeize`        | rewarding | `validRewardingContext` | `ProgrammableLogicBase.hs:1290` (`pisRewardingScript`) |
| `programmableLogicGlobal`  | rewarding | `validRewardingContext` | `ProgrammableLogicBase.hs:1176` (`pisRewardingScript`) |

These are the SAME predicates used as the hypothesis of every P-theorem (see
`WSC/Props/P3_Base.lean` and `WSC/Prep/*.lean`), which is what makes the audit
in `WSC/LR-CTX-AUDIT.md` an audit of the theorems' preconditions. -/
inductive Purpose where
  | spending | minting | rewarding
deriving Repr, DecidableEq

/-- Purpose of each validator, keyed by the `validator` field of a golden.
`none` for an unknown validator name (fails loudly rather than defaulting). -/
def purposeOfValidator : String → Option Purpose
  | "programmableLogicBase" => some .spending
  | "programmableTokenMinting" => some .minting
  | "programmableSeize" => some .rewarding
  | "programmableLogicGlobal" => some .rewarding
  | _ => none

def validContextFor : Purpose → ScriptContext → Bool
  | .spending, ctx => validSpendingContext ctx
  | .minting, ctx => validMintingContext ctx
  | .rewarding, ctx => validRewardingContext ctx

/-- The ADDENDUM E5 audit verdict for one golden: `some true` = decoded AND the
matching `validXContext` holds; `some false` = decoded but the precondition
FAILS (a serious finding — see `conjuncts` below); `none` = could not even
decode / unknown validator. -/
def auditVerdict (v : Vector) : Option Bool :=
  match purposeOfValidator v.validator, ctxOfHex v.scriptContextHex with
  | some p, some ctx => some (validContextFor p ctx)
  | _, _ => none

/-- Every conjunct of `validScriptContext` = `validScriptInfo && validTxInfo`,
in source order (`CardanoLedgerApi/V3/Contexts.lean:979-1002` and `:1197-1211`),
plus the purpose gate of `validXContext` (`:1231-1246`).  Used to localise a
FALSE verdict to the exact failing clause. -/
def conjuncts (p : Purpose) (ctx : ScriptContext) : List (String × Bool) :=
  let ti := ctx.scriptContextTxInfo
  [ ("purposeGate(validXContext)",
      match p, ctx.scriptContextScriptInfo with
      | .spending, .SpendingScript .. => true
      | .minting, .MintingScript _ => true
      | .rewarding, .RewardingScript _ => true
      | _, _ => false)
  , ("validScriptInfo", validScriptInfo ctx)
    -- the two halves of validScriptInfo (`:1001-1002`), split out so a failure
    -- can be attributed:
  , ("  scriptInfo.redeemerConsistent",
      findRedeemer ctx.scriptContextScriptInfo.toScriptPurpose ti.txInfoRedeemers
        == some ctx.scriptContextRedeemer)
  , ("  scriptInfo.purposeWellFormed",
      match ctx.scriptContextScriptInfo with
      | .SpendingScript ownRef datum =>
          match resolveInput ownRef ti.txInfoInputs with
          | some tin => CardanoLedgerApi.V2.isScriptCredentialAddress
                          tin.txInInfoResolved.txOutAddress
                        && validInputDatum datum tin.txInInfoResolved ctx
          | none => false
      | .MintingScript cs => CardanoLedgerApi.V2.hasCurrencySymbol cs ti.txInfoMint
      | .RewardingScript cred =>
          CardanoLedgerApi.V2.isScriptCredential cred
          && credentialInWithdrawals cred ti.txInfoWdrl
      | _ => false)
  , ("validInputs", validInputs ctx)
  , ("validReferenceInputs", validReferenceInputs ctx)
  , ("validOutputs", validOutputs ti.txInfoOutputs)
  , ("txInfoFee > 0", ti.txInfoFee > 0)
  , ("validMintValue", validMintValue ti.txInfoMint)
  , ("validWithdrawals", validWithdrawals ti.txInfoWdrl)
  , ("validTxRange", CardanoLedgerApi.V2.validTxRange ti.txInfoValidRange)
  , ("validSigners", CardanoLedgerApi.V2.validSigners ti.txInfoSignatories)
  , ("validRedeemerMap", validRedeemerMap ti.txInfoRedeemers)
  , ("validDatumMap", CardanoLedgerApi.V2.validDatumMap ti.txInfoData)
  , ("validVoterMap", validVoterMap ti.txInfoVotes)
  , ("validTreasuryAmount", validTreasuryAmount ti.txInfoCurrentTreasuryAmount)
  , ("validTreasuryDonation", validTreasuryDonation ti.txInfoTreasuryDonation)
  , ("isBalanced", isBalanced ctx)
  ]

/-- Per-conjunct report for a golden (`none` if it does not decode). -/
def conjunctReport (v : Vector) : Option (List (String × Bool)) :=
  match purposeOfValidator v.validator, ctxOfHex v.scriptContextHex with
  | some p, some ctx => some (conjuncts p ctx)
  | _, _ => none

/-- Names of the conjuncts that FAIL for a golden, in `conjuncts` order.
`some []` = the whole precondition holds. -/
def failingConjuncts (v : Vector) : Option (List String) :=
  (conjunctReport v).map fun l =>
    (l.filter (fun (p : String × Bool) => !p.2)).map (fun (p : String × Bool) => p.1.trim)

/-! ## Localising an ORDER failure to the adjacent pair that breaks it

`validRedeemerMap` / `validWithdrawals` are strict-ascending checks, so a failure
is always witnessed by ONE adjacent pair.  Naming that pair is what distinguishes
the two very different causes found in this suite:

* a `(Spending, Minting)` pair means the failure is at a PURPOSE-KIND boundary,
  where CLAB's order disagrees with `cardano-ledger`'s — a CLAB defect
  (`WSC/STATUS.md` §3 D1), not a defect of the transaction;
* a `(Rewarding c₁, Rewarding c₂)` pair with both credentials being script
  credentials means the failure is inside a kind, where CLAB and the ledger agree
  — so the transaction really is mis-ordered (a harness artifact). -/

/-- Coarse label of a `ScriptPurpose`: its constructor, and for `Rewarding` also
whether the credential is a script credential (the case where CLAB's and the
ledger's `Credential` orders agree — `WSC/STATUS.md` §3 D2). -/
def purposeKind : CardanoLedgerApi.V3.ScriptPurpose → String
  | .Minting _ => "Minting"
  | .Spending _ => "Spending"
  | .Rewarding c =>
      if CardanoLedgerApi.V2.isScriptCredential c then "Rewarding(script)"
      else "Rewarding(pubkey)"
  | .Certifying _ _ => "Certifying"
  | .Voting _ => "Voting"
  | .Proposing _ _ => "Proposing"

private def firstNonAscending {α : Type} [LT α] [DecidableLT α] (label : α → String) :
    List α → Option (String × String)
  | a :: b :: rest =>
      if decide (a < b) then firstNonAscending label (b :: rest)
      else some (label a, label b)
  | _ => none

/-- The first adjacent `txInfoRedeemers` pair that is not strictly ascending
under CLAB's `ltScriptPurpose`, labelled by purpose kind.  `none` = sorted. -/
def firstRedeemerOrderViolation (ctx : ScriptContext) : Option (String × String) :=
  firstNonAscending purposeKind
    (ctx.scriptContextTxInfo.txInfoRedeemers.map
      (fun (p : CardanoLedgerApi.V3.ScriptPurpose × CardanoLedgerApi.V2.Redeemer) => p.1))

/-- Same for `txInfoWdrl`, labelled by credential kind. -/
def firstWithdrawalOrderViolation (ctx : ScriptContext) : Option (String × String) :=
  firstNonAscending
    (fun c => if CardanoLedgerApi.V2.isScriptCredential c then "script" else "pubkey")
    (ctx.scriptContextTxInfo.txInfoWdrl.map
      (fun (p : CardanoLedgerApi.V2.Credential × PlutusCore.Integer.Integer) => p.1))

/-! ## Localising the audit failures: canonicalisation + named relaxations

The audit (`WSC/LR-CTX-AUDIT.md`) finds every golden context FALSE, and every
failure falls into one of four classes that the benchmark harness — not the
Cardano ledger — is responsible for.  To make that claim precise rather than
rhetorical, the two ORDERING classes are repaired by canonical re-sorting (a
pure permutation: no value is invented, `isBalanced` is untouched) and the two
VALUE classes are handled by two named, individually-justified relaxations.
Nothing else about the context is changed. -/

/-- Re-sort the withdrawal map (by credential) and the redeemer map (by
`ScriptPurpose`) into the order CLAB's `validWithdrawals` / `validRedeemerMap`
demand.  A permutation only: multiset content, values, fee and balance are all
unchanged, so its sole effect is to isolate "is the failure nothing but order?".

READ THE DIRECTION OF THIS REPAIR CAREFULLY (it differs per failure class, see
`WSC/LR-CTX-AUDIT.md` §4):

* For the withdrawal maps, and for the redeemer maps of the seize goldens, the
  violating pair is INSIDE one purpose/credential kind (two script credentials
  emitted descending), where CLAB's order and `cardano-ledger`'s agree — so
  sorting genuinely repairs a mis-ordered context.
* For the redeemer maps of the two accepting MINTING goldens the violating pair
  is `(Spending, Minting)`, and there CLAB's order is the one that is wrong:
  `cardano-ledger` emits `txInfoRedeemers` in `ConwayPlutusPurpose AsIx` order
  (`ConwaySpending < ConwayMinting < …`) and does not re-sort, so the golden is
  ledger-correct and re-sorting moves it AWAY from reality.  This function is
  still the right instrument there — it shows the failure is order-only — but the
  conclusion is "fix CLAB" (`WSC/STATUS.md` §3 D1, quarantined in
  `WSC/Honest.lean`'s `CLABMapOrderAgrees`), not "fix the transaction". -/
def canonicaliseOrder (ctx : ScriptContext) : ScriptContext :=
  let ti := ctx.scriptContextTxInfo
  { ctx with
    scriptContextTxInfo :=
      { ti with
        txInfoWdrl :=
          ti.txInfoWdrl.mergeSort
            (fun a b => !(decide (b.1 < a.1)))
        txInfoRedeemers :=
          ti.txInfoRedeemers.mergeSort
            (fun a b => !(decide (b.1 < a.1))) } }

/-- Does a `Value` carry a lovelace (ada) entry at all?  `validTxOutValue`
requires an ada-FIRST entry with a positive quantity; the harness emits
lovelace-free token-only outputs, which the real ledger's min-UTxO-ada rule
makes impossible. -/
def hasAdaEntry (v : CardanoLedgerApi.V1.Value.Value) : Bool :=
  match v with
  | (Data.B bs, _) :: _ => bs.data.isEmpty
  | _ => false

/-- `validTxOutValue` with RELAXATION A3 applied: if the value carries no
lovelace entry, a synthetic 2 ada entry is prepended before checking.  This
relaxes ONLY the min-ada requirement — currency-symbol sortedness, token-name
sortedness and positivity of the token part are still fully checked. -/
def validTxOutValueMinAdaRelaxed (v : CardanoLedgerApi.V1.Value.Value) : Bool :=
  if hasAdaEntry v then CardanoLedgerApi.V2.validTxOutValue v
  else CardanoLedgerApi.V2.validTxOutValue
         ((Data.B (ByteString.mk ""),
           Data.Map [(Data.B (ByteString.mk ""), Data.I 2000000)]) :: v)

/-- `validXContext` on `canonicaliseOrder ctx` with exactly two clauses relaxed:

* **A1** `txInfoFee > 0` is dropped — the harness sets `txInfoFee = 0`
  (`buildBalancedScriptContext`), while a real Cardano transaction always pays a
  positive fee.  Dropping it is the weaker choice; note that a real fee would
  also change `isBalanced`, so it cannot simply be patched in.
* **A3** `validOutputs` uses `validTxOutValueMinAdaRelaxed` (above).

Everything else — `validScriptInfo`, `validInputs`, `validReferenceInputs`,
`validMintValue`, `validTxRange`, `validSigners`, `validDatumMap`,
`validVoterMap`, treasury clauses and **`isBalanced`** — is checked verbatim.
So `relaxedVerdict v = some true` says: *the only obstructions between this real
golden context and CLAB's precondition are the four named harness artifacts.* -/
def validContextRelaxed (p : Purpose) (ctx₀ : ScriptContext) : Bool :=
  let ctx := canonicaliseOrder ctx₀
  let ti := ctx.scriptContextTxInfo
  (match p, ctx.scriptContextScriptInfo with
   | .spending, .SpendingScript .. => true
   | .minting, .MintingScript _ => true
   | .rewarding, .RewardingScript _ => true
   | _, _ => false) &&
  validScriptInfo ctx &&
  validInputs ctx &&
  validReferenceInputs ctx &&
  ti.txInfoOutputs.all (fun o => validTxOutValueMinAdaRelaxed o.txOutValue) &&
  -- A1: `ti.txInfoFee > 0` intentionally omitted
  validMintValue ti.txInfoMint &&
  validWithdrawals ti.txInfoWdrl &&
  CardanoLedgerApi.V2.validTxRange ti.txInfoValidRange &&
  CardanoLedgerApi.V2.validSigners ti.txInfoSignatories &&
  validRedeemerMap ti.txInfoRedeemers &&
  CardanoLedgerApi.V2.validDatumMap ti.txInfoData &&
  validVoterMap ti.txInfoVotes &&
  validTreasuryAmount ti.txInfoCurrentTreasuryAmount &&
  validTreasuryDonation ti.txInfoTreasuryDonation &&
  isBalanced ctx

def relaxedVerdict (v : Vector) : Option Bool :=
  match purposeOfValidator v.validator, ctxOfHex v.scriptContextHex with
  | some p, some ctx => some (validContextRelaxed p ctx)
  | _, _ => none

/-! ## Aggregate gates (the shape the audit/witness theorems assert) -/

/-- `true` iff EVERY golden decodes to a `ScriptContext` and satisfies its
matching `validXContext`.  This is the ADDENDUM E5 headline claim. -/
def allContextsValid : Bool :=
  all.all fun v => auditVerdict v == some true

/-- `true` iff every golden's `scriptContextHex` decodes and re-encodes
byte-identically (fidelity of the CBOR pipeline itself). -/
def allContextsRoundTrip : Bool :=
  all.all fun v => dataRoundTrips v.scriptContextHex == some true

/-- `true` iff every golden's `redeemerHex` decodes and re-encodes
byte-identically at the `Data` level (ADDENDUM E8, first half — the mirror-type
half lives in `WSC/Goldens/Witnesses.lean`). -/
def allRedeemersRoundTrip : Bool :=
  all.all fun v => dataRoundTrips v.redeemerHex == some true

/-- `true` iff every golden's params hexes decode and re-encode byte-identically. -/
def allParamsRoundTrip : Bool :=
  all.all fun v => v.paramsHex.all fun h => dataRoundTrips h == some true

/-- Consistency gate: the separately-exposed `redeemerHex` really is the
`scriptContextRedeemer` field of the decoded context (guards against a golden
whose redeemer and context drifted apart). -/
def redeemerMatchesContext (v : Vector) : Option Bool :=
  match ctxOfHex v.scriptContextHex, dataOfHex v.redeemerHex with
  | some ctx, some d => some (ctx.scriptContextRedeemer == d)
  | _, _ => none

def allRedeemersMatchContexts : Bool :=
  all.all fun v => redeemerMatchesContext v == some true

/-- Full round-trip through the CLAB `ScriptContext` TYPE (not just `Data`):
hex → `Data` → `ScriptContext` → `Data` → hex.  This is the decisive fidelity
gate on the bridge itself: if it holds, CLAB's `IsData ScriptContext` instance
loses NOTHING of the off-chain-produced context, so every audit result below is
a statement about the real golden and not about a lossy Lean reading of it. -/
def ctxTypeRoundTrips (v : Vector) : Option Bool :=
  match ctxOfHex v.scriptContextHex with
  | none => none
  | some ctx => (fun h => h == v.scriptContextHex) <$> hexOfData (IsData.toData ctx)

def allCtxTypeRoundTrip : Bool :=
  all.all fun v => ctxTypeRoundTrips v == some true

/-- `true` iff every golden decodes to a `ScriptContext` (weaker than
`allContextsValid`: says nothing about the ledger predicate). -/
def allContextsDecode : Bool :=
  all.all fun v => (ctxOfHex v.scriptContextHex).isSome

/-- `true` iff every golden satisfies its matching `validXContext` once the four
named harness artifacts are accounted for (`validContextRelaxed`). -/
def allContextsValidRelaxed : Bool :=
  all.all fun v => relaxedVerdict v == some true

/-- Same, restricted to the 9 ACCEPTING goldens.  The 4 rejecting goldens are
single-field tampers (`WSC/goldens/MANIFEST.md`) and two of them tamper by
DELETING an output, which necessarily breaks `isBalanced`, so they are not
expected to pass. -/
def acceptingContextsValidRelaxed : Bool :=
  (all.filter (fun v => v.accepts)).all fun v => relaxedVerdict v == some true

/-! ## Script parameters (for the real-suite positive witnesses, ADDENDUM E9) -/

/-- Golden `paramsHex` entry → CLAB `Credential` (the `PAsData PCredential`
parameters of `programmableLogicBase`). -/
def credentialOfHex (h : String) : Option CardanoLedgerApi.V3.Credential :=
  match dataOfHex h with
  | none => none
  | some d => (IsData.fromData d : Option CardanoLedgerApi.V3.Credential)

/-- Golden `paramsHex` entry → `ByteString` (the `PAsData PCurrencySymbol` /
`PAsData PScriptHash` parameters of the other three validators). -/
def byteStringOfHex (h : String) : Option ByteString :=
  match dataOfHex h with
  | none => none
  | some d =>
      match d with
      | Data.B bs => some bs
      | _ => none

end WSC.Goldens
