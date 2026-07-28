/-
WSC/Shaped/BaseShapedR.lean — **SHAPES B1RG / B1RS**, the post-#112, REALIZABLE
cut of the base spending validator's shape (task N3).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS AT ALL — and it is a REGRESSION, stated as one
════════════════════════════════════════════════════════════════════════════
Before wsc-poc PR #112, P3 was the ONE property in this library proved over a
FULLY SYMBOLIC `ScriptContext` (`WSC/Coverage.lean` §7,
`p3_lives_over_a_covering_class`: "the only property in the campaign of which
this is true"). The pre-#112 base validator scanned `txInfoWdrl` with a
`pfix` loop and `blaster` closed the unshaped goal in seconds.

The post-#112 validator instead reads an INDEX out of its redeemer and does
`pdropList <symbolic index>` into the withdrawal map
(ProgrammableLogicBase.hs:712-733). MEASURED (task N3, `WSC/Props/P3_Base.lean`
§MEASUREMENT for the table): with the same flat, same inputs function and same
600-step budget, **all three unshaped goals — the theorem, the negative control
and the vacuity probe — come back `⚠️ Undetermined` at a 600 s Z3 cap**, and an
UNCAPPED run of the same theorem was still running after 37 minutes. A symbolic
index into a symbolic list is what broke it.

So P3 now needs a shape, like every other property in the campaign. This module
supplies it, cut to be REALIZABLE from the start (audit finding **F2**: a shape
with two script-credential withdrawals and a ONE-entry redeemer map is
PROVABLY UNBUILDABLE, because Conway UTXOW's `hasExactSetOfRedeemers` needs a
`Rewarding` entry per script-credential withdrawal).

════════════════════════════════════════════════════════════════════════════
THE CUT
════════════════════════════════════════════════════════════════════════════
This is the OLD SHAPE B1 (`WSC/Shaped/BaseShaped.lean`) with exactly two
changes. Its withdrawal-and-redeemer cut is deliberately the SAME as SHAPE T1R's
(`WSC/Shaped/GlobalShapedR.lean` §3) — 2 script withdrawals, 3 redeemer entries,
own input at `TxOutRef ⟨"",0⟩` — because T1R is the class P1 is proved over and
B1R is the class the same transaction's base input would be spent under, and a
composition that wants to talk about one transaction should not have to
reconcile two different withdrawal/redeemer skeletons. NOT CLAIMED: that the two
classes are equal or that one contains the other. They are not — T1R also fixes
a second input, reference inputs and outputs that B1R has none of. What is
shared is the part P3's conclusion is about. The two changes vs B1 are:

1. **the redeemer is now a `Constr`, not a bare `Data.I`.** The base redeemer
   type is new at #112 — `BaseSpendRedeemer = SpendViaGlobal Integer |
   SpendViaSeize Integer`, `makeIsDataIndexed [(SpendViaGlobal,0),
   (SpendViaSeize,1)]` (ProgrammableLogicBase.hs:704-709), mirrored as
   `WSC.BaseSpendRedeemer` (`WSC/Redeemer.lean:99-111`). The CONSTRUCTOR TAG is
   part of the `Data` skeleton, so it must be frozen by the shape — which is why
   there are TWO shapes here, `B1RG` (tag 0) and `B1RS` (tag 1), one per arm.
   The tag is the only thing frozen: **the index field `red` stays a free
   symbolic `Integer`**, so an attacker choosing a wrong index is inside the
   class and the theorem has to survive it.
2. **three redeemer entries, not one** — `Spending ⟨"",0⟩` (the running script's
   own entry, carrying the base redeemer) plus one `Rewarding` entry per script
   withdrawal, carrying free symbolic payloads. This is the F2 fix, and it is
   also the measured shape of the real accepting golden
   `programmableLogicBase.base-spend-transfer-tx`: 1 input / 2 withdrawals /
   **3** redeemers (`WSC/AUDIT.md` §4b, re-verified against the N2-regenerated
   vectors).

FIXED (this is the published scope): exactly 1 input, the script's own, at
`TxOutRef ⟨"", 0⟩`; 0 reference inputs; 0 outputs; empty mint, certificate,
signatory, datum, vote and proposal lists; a withdrawal map of exactly 2
entries, both carrying SCRIPT credentials; exactly 3 redeemer entries as above;
the spent output carries an ada-only canonical value, no datum and no reference
script; a finite closed validity interval; treasury/donation present; the
redeemer's constructor tag.

SYMBOLIC (every scalar leaf): the base script hash the input sits at and its
lovelace amount, BOTH withdrawal credentials' script hashes and BOTH withdrawal
amounts, the fee, **the redeemer's index field**, both foreign redeemer
payloads, the validity bounds, the transaction id, and — this is the one that
matters for P3 — BOTH script parameters `gh`/`sh`.

Note what is deliberately symbolic and MUST stay so: the two withdrawal
credentials and the two parameters. P3's conclusion is a statement about exactly
those; shaping any of them concretely would smuggle the postcondition into the
shape. `red` is likewise symbolic: freezing it would make the theorem say
nothing about a dishonest witness index, which is the whole new attack surface
#112 introduced.

WHY FREEZING `TxOutRef ⟨"", 0⟩` IS NOT A SECURITY-RELEVANT RESTRICTION: the base
validator never reads `txInfoInputs` at all (it touches only `TxInfo` field 6,
`wdrl`, and the `ScriptContext`'s redeemer field — :712-733). The own-input
reference exists in this shape solely so the context is a well-formed SPENDING
context and so the redeemer map has a `Spending` purpose to cover. SHAPE T1R
freezes it the same way and for the same reason.
-/
import WSC.Prep.Base
import WSC.Shaped.Shape
import WSC.Redeemer
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash ScriptPurpose
                          RedeemerMap TxInInfo TxOutRef TxInfo Withdrawals
                          spendingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- The own input's `TxOutRef`, frozen (see the header). Identical to SHAPE
T1R's, so the two shapes agree on it. -/
def baseROutRef : TxOutRef := ⟨ByteString.mk "", 0⟩

/-- The withdrawal map of SHAPES B1RG / B1RS: two SCRIPT credentials, both
hashes and both amounts symbolic. -/
def baseRWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- The redeemer map: the running spending script's own entry (carrying `own`,
the `BaseSpendRedeemer`) plus one `Rewarding` entry per script withdrawal,
carrying free symbolic payloads. Ascending in `ScriptPurpose` order
(`Spending < Rewarding w0 < Rewarding w1`, the last step iff `w0 < w1`) — the
same order and the same three purposes as `p1RRedeemers`. -/
def baseRRedeemers (w0 w1 : ScriptHash) (rw0 rw1 : Integer) (own : Data) : RedeemerMap :=
  [ (.Spending baseROutRef, own)
  , (.Rewarding (.ScriptCredential w0), Data.I rw0)
  , (.Rewarding (.ScriptCredential w1), Data.I rw1) ]

/-- The `Data` form of `BaseSpendRedeemer` at a frozen constructor tag and a
SYMBOLIC index. `baseRRedeemer_is_mirror` below proves this is exactly what
`WSC/Redeemer.lean`'s mirror encodes, so the shape is not carrying a private,
possibly-wrong idea of the redeemer's wire form. -/
def baseRRedeemerData (tag : Nat) (red : Integer) : Data := Data.Constr tag [Data.I red]

/-- AUDIT LINK: the shape's redeemer `Data` at tag 0 / tag 1 is exactly the
mirror's encoding of `SpendViaGlobal red` / `SpendViaSeize red`. -/
theorem baseRRedeemer_is_mirror (red : Integer) :
    baseRRedeemerData 0 red
      = CardanoLedgerApi.IsData.Class.IsData.toData (BaseSpendRedeemer.SpendViaGlobal red)
  ∧ baseRRedeemerData 1 red
      = CardanoLedgerApi.IsData.Class.IsData.toData (BaseSpendRedeemer.SpendViaSeize red) :=
  ⟨rfl, rfl⟩

/-- **SHAPE B1R at a frozen redeemer constructor tag.** `tag = 0` is SHAPE
B1RG (`SpendViaGlobal red`), `tag = 1` is SHAPE B1RS (`SpendViaSeize red`). -/
def baseRShapedCtx (tag : Nat)
    (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red rw0 rw1 : Integer) (lo hi : Integer) (tid : ByteString)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.ScriptCredential baseHash, none⟩
    , txOutValue := adaOnly lovelace
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨baseROutRef, resolved⟩]
      , txInfoReferenceInputs := []
      , txInfoOutputs := []
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := baseRWdrl w0 w1 a0 a1
      , txInfoValidRange := range lo hi
      , txInfoSignatories := []
      , txInfoRedeemers := baseRRedeemers w0 w1 rw0 rw1 (baseRRedeemerData tag red)
      , txInfoData := []
      , txInfoId := tid
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := baseRRedeemerData tag red
  , scriptContextScriptInfo := .SpendingScript baseROutRef none }

/-- AUDIT LINK: `baseRWdrl` is exactly `txInfoWdrl` of the shaped context, so
quoting it in the theorem statements loses nothing. -/
theorem baseRShapedCtx_wdrl (tag : Nat)
    (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red rw0 rw1 : Integer) (lo hi : Integer) (tid : ByteString) :
    ((baseRShapedCtx tag baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi
        tid).scriptContextTxInfo).txInfoWdrl
      = baseRWdrl w0 w1 a0 a1 := rfl

/-- Shaped inputs function. Both script parameters are `ScriptCredential`s over
SYMBOLIC hashes (`gh`, `sh`) — which is what the honest deployment uses, both
the global transfer validator and the seize validator being scripts
(ProgrammableLogicBase.hs:711-712; offchain Scripts.hs:100-109) — and they are
never tied to `w0`/`w1`. -/
def baseRShapedInputs (tag : Nat) (gh sh : ScriptHash)
    (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red rw0 rw1 : Integer) (lo hi : Integer) (tid : ByteString)
    : List Term :=
  toTerm (Credential.ScriptCredential gh) :: toTerm (Credential.ScriptCredential sh)
    :: spendingInputs
         (baseRShapedCtx tag baseHash lovelace w0 w1 a0 a1 fee red rw0 rw1 lo hi tid)

/-- SHAPE B1RG — the `SpendViaGlobal` arm (redeemer constructor tag 0). -/
def baseRGInputs := baseRShapedInputs 0

/-- SHAPE B1RS — the `SpendViaSeize` arm (redeemer constructor tag 1). -/
def baseRSInputs := baseRShapedInputs 1

#prep_uplc appliedBaseB1RG programmableLogicBase baseRGInputs 600
#prep_uplc appliedBaseB1RS programmableLogicBase baseRSInputs 600

end WSC
