/-
WSC/Shaped/MintingShapedR.lean — **SHAPE M1R: the NODE-REALIZABLE re-cut of
SHAPE M1** (task C2, the `BurnOnly` arm of the issuance policy).

════════════════════════════════════════════════════════════════════════════
WHY A RE-CUT AT ALL — audit F2
════════════════════════════════════════════════════════════════════════════
SHAPE M1 (`WSC/Shaped/MintingShaped.lean`) bakes a **two-entry withdrawal map
whose BOTH credentials are SCRIPT credentials** together with a **one-entry
redeemer map** (`(Minting ownCS, BurnOnly 0)` only). Conway UTXOW's
`MissingRedeemers` rule needs one redeemer entry per script witness, and a
script-credential withdrawal IS a script witness, so
`WSC/Props/Shaped/ShapeRealizability.lean`'s `m1_class_is_empty_under_coverage`
proves SHAPE M1 is an EMPTY class of ledger transactions. Every theorem over it
is true and none of them can be composed.

SHAPE M1R fixes that, and the fix is a SHRINK, not a growth:

| | SHAPE M1 | **SHAPE M1R** | golden `mint-local-registered-by-ref` |
|---|---|---|---|
| inputs (script / total) | 0 / 1 | **0 / 1** | 0 / 1 |
| mint policies | 1 | **1** | 1 |
| withdrawals (script / total) | 2 / 2 | **1 / 1** | 1 / 1 |
| redeemer entries | 1 | **2** | 2 |
| coverage `#red = #scriptIn + #mintPol + #scriptWdrl` | 1 ≠ 3 ✗ | **2 = 2 ✓** | 2 = 2 ✓ |

The cheapest realizable template (audit §4b) is `transfer-nonmember-covering-node`
/ `mint-local-registered-by-ref`: ONE script withdrawal, TWO redeemer entries.
SHAPE M1R is exactly that cut.

════════════════════════════════════════════════════════════════════════════
WHAT THE VALIDATOR ACTUALLY REQUIRES — so the shrink loses nothing
════════════════════════════════════════════════════════════════════════════
The `BurnOnly` arm (Issuance.hs:247-258) reads the withdrawal map in ONE place:
common check C1, `mintingLogicInvokedAt # wdrlIdx`, defined at Issuance.hs:150-151
as

    (pfstBuiltin # (phead # (pcheckedDrop # pfromData wdrlIdx # withdrawalEntries)))
      #== mintingLogicCred

with `mintingLogicCred = pdata $ pcon $ PScriptCredential mintingLogicHash'`
(Issuance.hs:136). So **exactly one withdrawal entry has to be a SCRIPT
credential — the one at `pboMintingLogicWdrlIdx`** — and the arm's second
conjunct (:255-257) reads only `ptxInfo'mint`. The arm never touches
`ptxInfo'redeemers`, never touches the outputs, and never touches the reference
inputs. SHAPE M1's second withdrawal entry `w1` was pure generality; it is what
made the class empty, and dropping it costs no postcondition:
`P4a_shaped_mint_runs_minting_logic`'s conclusion is
`credentialInWithdrawals (ScriptCredential mlh) wdrl`, and at SHAPE M1R that is
`w0 == mlh` with `w0` a FREE variable — still earned from the bytecode, still not
hypothesis-implied (`validWithdrawals` on a singleton map says nothing at all
about WHICH credential appears).

WHY THE WITHDRAWAL ENTRY MUST STAY A *SCRIPT* CREDENTIAL. The task's instruction
is to make withdrawal entries PUBKEY wherever the validator does not dereference
a script. Here it cannot: C1 compares the entry's credential against
`PScriptCredential mintingLogicHash'`, so a pubkey entry at index 0 makes the arm
UNSATISFIABLE and the shape accept-UNSAT (a vacuous class — the failure mode the
mandatory vacuity probe exists to catch). One script withdrawal is the FLOOR for
this validator, on every one of its four arms.

════════════════════════════════════════════════════════════════════════════
FIXED (the published scope — quote this with any theorem over this prep)
════════════════════════════════════════════════════════════════════════════
Identical to SHAPE M1 (`WSC/Shaped/MintingShaped.lean`'s header) except for the
two dimensions above. In full: 1 input; 1 output; 0 reference inputs; empty
certificate / signatory / datum / vote / proposal lists; a mint field with
exactly one policy (the policy's own) carrying exactly one token name; **a
withdrawal map of exactly 1 entry, a SCRIPT credential**; **a redeemer map of
exactly 2 entries — `(Minting ownCS, BurnOnly 0)` then
`(Rewarding (ScriptCredential w0), Data.B mlRed)`**; the input and the output
both at PUBKEY addresses with no datum and no reference script and carrying
canonical ada-plus-one-token values; a finite closed validity interval;
`txInfoCurrentTreasuryAmount = txInfoTreasuryDonation = 1`; and the redeemer is
`BurnOnly` (tag 3, Issuance.hs:88-90, :118-120) with
`pboMintingLogicWdrlIdx = 0`.

SYMBOLIC: every byte string and every integer — `ownCS`, `tn`, the signed minted
quantity `q`, `owner`, `inAda`, `qIn`, `dest`, `outAda`, `qOut`, **the withdrawal
credential `w0`** and its amount `a0`, the fee, the input's `TxOutRef`, the
validity bounds, the transaction id, and **`mlRed`, the minting-logic script's own
redeemer payload** (a free `ByteString` under `Data.B`; the issuance policy never
decodes it on this arm).

REDEEMER-MAP ORDER. `[Minting ownCS, Rewarding (ScriptCredential w0)]` is sorted
under CLAB's corrected `ltScriptPurpose` (`Spending < Minting < Certifying <
Rewarding < Voting < Proposing`, `CardanoLedgerApi/V3/Contexts.lean:101-120`), so
`validRedeemerMap` accepts it for EVERY leaf assignment — no side condition. This
is the D1 fix doing real work: under the pre-fix Plutus-declaration order this
shape would have been ledger-UNSATISFIABLE.
-/
import WSC.Prep.Minting900
import WSC.Shaped.Shape
import WSC.Redeemer
import WSC.Realizability
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals ScriptPurpose mintingInputs findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE M1R's withdrawal map: **one** entry, a script credential, symbolic hash
and amount. The floor forced by C1 (Issuance.hs:150-151). -/
def mintRWdrl (w0 : ScriptHash) (a0 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0)]

/-- SHAPE M1R's mint field — unchanged from SHAPE M1. -/
def mintRMint (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer) : MintValue :=
  mintOne ownCS tn q

/-- SHAPE M1R's own redeemer: `BurnOnly { pboMintingLogicWdrlIdx = 0 }`. -/
def mintRRedeemer : Data := IsData.toData (MintRedeemer.BurnOnly 0)

/-- AUDIT: the shaped redeemer really is `Data.Constr 3 [Data.I 0]`. -/
theorem mintRRedeemer_eq : mintRRedeemer = Data.Constr 3 [Data.I 0] := by
  native_decide

/-- **SHAPE M1R's redeemer map — the whole point of the re-cut.** Two entries:
the policy's own `Minting` entry, and the `Rewarding` entry that COVERS the
transaction's single script withdrawal. `mlRed` is a free leaf: the issuance
policy does not decode the minting-logic script's redeemer on any arm. -/
def mintRRedeemerMap (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString)
    : List (ScriptPurpose × Data) :=
  [ (.Minting ownCS, mintRRedeemer)
  , (.Rewarding (.ScriptCredential w0), Data.B mlRed) ]

/-- **SHAPE M1R.** See the module header for the full FIXED / SYMBOLIC split. -/
def mintRCtx
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString)
    : ScriptContext :=
  let outRef : TxOutRef := ⟨txid, oidx⟩
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaPlusOne inAda ownCS tn qIn
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  let produced : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential dest, none⟩
    , txOutValue := adaPlusOne outAda ownCS tn qOut
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨outRef, resolved⟩]
      , txInfoReferenceInputs := []
      , txInfoOutputs := [produced]
      , txInfoFee := fee
      , txInfoMint := mintRMint ownCS tn q
      , txInfoTxCerts := []
      , txInfoWdrl := mintRWdrl w0 a0
      , txInfoValidRange := range lo hi
      , txInfoSignatories := []
      , txInfoRedeemers := mintRRedeemerMap ownCS w0 mlRed
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := mintRRedeemer
  , scriptContextScriptInfo := .MintingScript ownCS }

/-! ### AUDIT LINKS — the named projections ARE the shaped context's fields. -/

section Audit
variable (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
         (owner : ByteString) (inAda qIn : Integer)
         (dest : ByteString) (outAda qOut : Integer)
         (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
         (fee : Integer) (txid : ByteString) (oidx : Integer)
         (lo hi : Integer) (tid : ByteString)

theorem mintRCtx_wdrl :
    (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
      lo hi tid).scriptContextTxInfo.txInfoWdrl = mintRWdrl w0 a0 := rfl

theorem mintRCtx_mint :
    (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
      lo hi tid).scriptContextTxInfo.txInfoMint = mintRMint ownCS tn q := rfl

theorem mintRCtx_redeemers :
    (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
      lo hi tid).scriptContextTxInfo.txInfoRedeemers = mintRRedeemerMap ownCS w0 mlRed := rfl

end Audit

/-! ### REDEEMER COVERAGE AT THE SHAPE — for EVERY leaf assignment

These are the theorems that make SHAPE M1R immune to
`WSC/Props/Shaped/ShapeRealizability.lean`'s emptiness argument. They are `rfl`
/ `decide`-level facts precisely because the re-cut ties the redeemer key to the
SAME free variable `w0` the withdrawal carries — coverage is structural, not a
side condition. -/

/-- The redeemer map's `Rewarding` entry, resolved. Stated separately so the
coverage proofs below never have to name a shape leaf. -/
theorem mintR_findRewarding (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString) :
    findRedeemer (.Rewarding (.ScriptCredential w0)) (mintRRedeemerMap ownCS w0 mlRed)
      = some (Data.B mlRed) := by
  rw [mintRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

/-- The redeemer map's own `Minting` entry, resolved. -/
theorem mintR_findMinting (ownCS : CurrencySymbol) (w0 : ScriptHash) (mlRed : ByteString) :
    findRedeemer (.Minting ownCS) (mintRRedeemerMap ownCS w0 mlRed) = some mintRRedeemer := by
  rw [mintRRedeemerMap, Realizability.findRedeemer_cons_hit]

/-- SHAPE M1R's only script withdrawal is covered: the redeemer map's second entry
is `Rewarding (ScriptCredential w0)` for the very same `w0`. -/
theorem mintR_wdrl_covered :
    ∀ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
      (owner : ByteString) (inAda qIn : Integer)
      (dest : ByteString) (outAda qOut : Integer)
      (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
      (fee : Integer) (txid : ByteString) (oidx : Integer)
      (lo hi : Integer) (tid : ByteString),
      Realizability.WdrlCovered
        (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
          lo hi tid) := by
  intro ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid h n hmem
  simp [mintRCtx, mintRWdrl] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [mintRCtx_redeemers, mintR_findRewarding]
  exact Option.noConfusion

/-- SHAPE M1R spends nothing from a script credential, so the spending route of
`t1_class_is_empty` cannot fire either — vacuously covered. -/
theorem mintR_spend_covered :
    ∀ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
      (owner : ByteString) (inAda qIn : Integer)
      (dest : ByteString) (outAda qOut : Integer)
      (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
      (fee : Integer) (txid : ByteString) (oidx : Integer)
      (lo hi : Integer) (tid : ByteString),
      Realizability.SpendCovered
        (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
          lo hi tid) := by
  intro ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid i hin hscript
  simp [mintRCtx] at hin
  subst hin
  simp [CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

/-- SHAPE M1R's single minted policy is its own, covered by redeemer entry 0. -/
theorem mintR_mint_covered :
    ∀ (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
      (owner : ByteString) (inAda qIn : Integer)
      (dest : ByteString) (outAda qOut : Integer)
      (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
      (fee : Integer) (txid : ByteString) (oidx : Integer)
      (lo hi : Integer) (tid : ByteString),
      Realizability.MintCovered
        (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx
          lo hi tid) := by
  intro ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid cs m hmem
  simp [mintRCtx, mintRMint, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  rw [mintRCtx_redeemers, mintR_findMinting]
  exact Option.noConfusion

/-- Parameter evidence is unchanged from WSC/Prep/Minting900.lean. -/
def mintRInputs
    (protocolParamsCS : CurrencySymbol) (mintingLogicHash : ScriptHash)
    (ownCS : CurrencySymbol) (tn : TokenName) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 : ScriptHash) (a0 : Integer) (mlRed : ByteString)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString)
    : List Term :=
  toTerm protocolParamsCS :: toTerm mintingLogicHash ::
    mintingInputs
      (mintRCtx ownCS tn q owner inAda qIn dest outAda qOut w0 a0 mlRed fee txid oidx lo hi tid)

#prep_uplc appliedMintRShaped900 programmableTokenMinting900 mintRInputs 900

end WSC
