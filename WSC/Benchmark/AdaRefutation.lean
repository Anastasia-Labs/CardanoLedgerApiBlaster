/-
WSC/Benchmark/AdaRefutation.lean — **THE REFUTATION ARTIFACT for the corrected
`cs ≠ ada` defect of `WSC/Benchmark/P1UnshapedStatement.lean`.**

`P1UnshapedForm` as first published dropped `WSC.Model.P1_model`'s
`cs ≠ ByteString.mk ""` clause (`WSC/Props/P1_Transfer.lean:366`) while its header
claimed the two statements agreed clause for clause. This module is the machine
check that the unguarded form was not merely stronger but FALSE, and it is kept in
the tree so the record survives the fix. The guard is now present; the theorems
below are what forced it.

**IT IS DELIBERATELY STANDALONE.** It imports `CardanoLedgerApi` and NOTHING from
`WSC`, and re-derives every definition it needs from the cited definition site, so
that it cannot be made to agree with the library by a shared mistake:

  * `WSC.Model.outSum` / `inSum`      (WSC/Model/Ground.lean:45-49, :53-58)
  * `WSC.Model.mintSigned`            (WSC/Props/P1_Transfer.lean:203-204)
  * `WSC.Model.coveringNodeExists`    (WSC/Props/P1_Transfer.lean:222-234)
  * `WSC.payCred`                     (WSC/Spec.lean:31-32)
  * `WSC.Shape.adaPlusOne`            (WSC/Shaped/Shape.lean:60-63)
  * the mini-ledger in/out of `p1RShapedCtx` at `WSC.P1RShapedWitness.ctxOk`'s
    OWN leaves (WSC/Props/Shaped/P1ShapedR.lean:582-596;
    WSC/Shaped/GlobalShapedP1.lean:257-289)

Nothing here imports the benchmark, and the benchmark does not import this: they
are cross-referenced by comment only.

WHAT THE FOUR THEOREMS SAY, in the order the argument needs them:

1. `covering_false_at_ada` — at `cs = adaSymbol` the REGISTRATION hypothesis is
   free for EVERY reference-input list, so it shuts nothing. Proved against a
   deliberately over-permissive reading of `coveringNodeExists` (the `hasCSH`
   authentication gate replaced by `some true`), so it holds a fortiori of the
   real one.
2. `ctxOk_quantities_MMM` — sanity: at the ADVERTISED asset the mini-ledger
   numbers agree with `WSC.P1RShapedWitness.ctxOk_quantities` (out = 5, in = 5),
   i.e. this really is that witness's ledger data and not a look-alike.
3. `ctxOk_refutes_P1_at_ada` — at `cs = tn = adaSymbol` the SAME accepting witness
   gives out = 150, in = 200, mint = 0, so `outSum ≥ inSum + mintSigned` is FALSE.
   The 50-lovelace gap IS `txInfoFee := 50`: `ctxOk`'s leaves are `inAda = 200`,
   `outAda = 150`, `in2Ada = 100`, `escAda = 100`, `fee = 50`, i.e. ada in 300 =
   ada out 250 + fee 50. The transfer validator does not constrain the ada slot on
   this path — and by design it cannot, because a transaction has to be able to
   pay its fee out of a mini-ledger UTxO.
4. `shaped_value_invalid_at_ada` / `shaped_value_valid_off_ada` — why the SHAPED
   theorems escape: `adaPlusOne` puts `cs` second, `validTxOutValue` demands
   strictly ascending currency symbols, so at `cs = adaSymbol` the shaped value is
   not ledger-valid and the shaped statements are VACUOUS there — while off ada
   the same value IS valid, so the shapes are not vacuous in general. That vacuity
   is the protection the unshaped statement lost, and
   `WSC/Benchmark/P1UnshapedStatement.lean` §3.1 is where it is re-supplied.
-/
import CardanoLedgerApi

namespace WSC.AdaRefutation

open CardanoLedgerApi.V1 (Credential Address)
open CardanoLedgerApi.V2 (TxOut OutputDatum)
open CardanoLedgerApi.V3 (TxInInfo TxOutRef CurrencySymbol TokenName Value MintValue valueOf)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-- WSC/Spec.lean:31-32 -/
def payCred (o : TxOut) : Credential := o.txOutAddress.addressCredential

/-- WSC/Model/Ground.lean:45-49 -/
def outSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if payCred o == base then valueOf cs tn o.txOutValue else 0) + outSum base cs tn rest

/-- WSC/Model/Ground.lean:53-58 -/
def inSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if payCred i.txInInfoResolved == base then
         valueOf cs tn i.txInInfoResolved.txOutValue else 0) + inSum base cs tn rest

/-- WSC/Props/P1_Transfer.lean:203-204 -/
def mintSigned (cs : CurrencySymbol) (tn : TokenName) (mint : MintValue) : Integer :=
  valueOf cs tn mint

/-- WSC/Model/GlobalModel.lean:318-320 -/
def dirNodeFields : Data → Option (CurrencySymbol × CurrencySymbol × Data)
  | Data.List (Data.B k :: Data.B n :: tls :: _) => some (k, n, tls)
  | _ => none

/-- Stand-in for `WSC.hasCSH`; ONLY used under a `&&` whose left conjunct we
show is already `false`, so its exact body is irrelevant to the result. -/
def hasCSHStub (_dirCS : CurrencySymbol) (_v : Value) : Option Bool := some true

/-- WSC/Props/P1_Transfer.lean:222-234, with `hasCSH` replaced by the STUB that
returns `some true` — i.e. the MOST PERMISSIVE possible reading. If this
returns `false` then the real one does too. -/
def coveringNodeExistsPermissive (dirCS : CurrencySymbol) (cs : CurrencySymbol) :
    List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeFields d with
            | some (k, n, _) =>
                decide (k < cs) && decide (cs < n) &&
                  (hasCSHStub dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || coveringNodeExistsPermissive dirCS cs rest

/-! ### FACT 1 — the registration hypothesis is FREE at `cs = adaSymbol`. -/

theorem covering_false_at_ada (dirCS : CurrencySymbol) :
    ∀ xs : List TxInInfo, coveringNodeExistsPermissive dirCS (ByteString.mk "") xs = false := by
  intro xs
  induction xs with
  | nil => rfl
  | cons i rest ih =>
      simp only [coveringNodeExistsPermissive, ih, Bool.or_false]
      split
      · split
        · rename_i k n _ _
          have : ¬ (k < (ByteString.mk "")) := by simp [LT.lt]
          simp [this]
        · rfl
      · rfl

/-! ### FACT 2 — `ctxOk`'s own mini-ledger leaves. -/

def adaCS : ByteString := ByteString.mk ""
def adaTN : ByteString := ByteString.mk ""

/-- WSC/Shaped/Shape.lean:60-63 -/
def adaPlusOne (n : Integer) (cs : CurrencySymbol) (tn : TokenName) (q : Integer) : Value :=
  [ (Data.B adaCS, Data.Map [(Data.B adaTN, Data.I n)])
  , (Data.B cs,    Data.Map [(Data.B tn,    Data.I q)]) ]

/-- WSC/Shaped/GlobalShapedP1.lean:257-263, at ctxOk's leaves
(plc = "PROGLOGIC", owner = "OWNER", inAda = 200, cs = "MMM", tn = "TOK", qIn = 5). -/
def ctxOkBaseIn : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"),
                      some (.StakingHash (.PubKeyCredential (ByteString.mk "OWNER")))⟩
   , txOutValue := adaPlusOne 200 (ByteString.mk "MMM") (ByteString.mk "TOK") 5
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- WSC/Shaped/GlobalShapedP1.lean:267-273 (ext = "EXT", in2Ada = 100, qIn2 = 4). -/
def ctxOkExtIn : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.PubKeyCredential (ByteString.mk "EXT"), none⟩
   , txOutValue := adaPlusOne 100 (ByteString.mk "MMM") (ByteString.mk "TOK") 4
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- WSC/Shaped/GlobalShapedP1.lean:276-281 (outAda = 150, qOut = 5). -/
def ctxOkBaseOut : TxOut :=
  { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"), none⟩
  , txOutValue := adaPlusOne 150 (ByteString.mk "MMM") (ByteString.mk "TOK") 5
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- WSC/Shaped/GlobalShapedP1.lean:284-289 (dest = "DEST", escAda = 100, qEsc = 4). -/
def ctxOkEscOut : TxOut :=
  { txOutAddress := ⟨.PubKeyCredential (ByteString.mk "DEST"), none⟩
  , txOutValue := adaPlusOne 100 (ByteString.mk "MMM") (ByteString.mk "TOK") 4
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

def base : Credential := .ScriptCredential (ByteString.mk "PROGLOGIC")

/-- Sanity: at the ADVERTISED asset (cs = "MMM", tn = "TOK") the numbers agree
with `P1RShapedWitness.ctxOk_quantities` (P1ShapedR.lean, out = 5, in = 5). -/
theorem ctxOk_quantities_MMM :
    outSum base (ByteString.mk "MMM") (ByteString.mk "TOK") [ctxOkBaseOut, ctxOkEscOut] = 5
    ∧ inSum base (ByteString.mk "MMM") (ByteString.mk "TOK") [ctxOkBaseIn, ctxOkExtIn] = 5
    ∧ mintSigned (ByteString.mk "MMM") (ByteString.mk "TOK") ([] : MintValue) = 0 := by
  native_decide

/-- **THE REFUTATION.** At `cs = tn = adaSymbol` the SAME accepting witness has
out = 150, in = 200, mint = 0 — so `outSum ≥ inSum + mintSigned` is FALSE. -/
theorem ctxOk_refutes_P1_at_ada :
    outSum base adaCS adaTN [ctxOkBaseOut, ctxOkEscOut] = 150
    ∧ inSum base adaCS adaTN [ctxOkBaseIn, ctxOkExtIn] = 200
    ∧ mintSigned adaCS adaTN ([] : MintValue) = 0
    ∧ ¬ (outSum base adaCS adaTN [ctxOkBaseOut, ctxOkEscOut]
           ≥ inSum base adaCS adaTN [ctxOkBaseIn, ctxOkExtIn]
             + mintSigned adaCS adaTN ([] : MintValue)) := by
  native_decide

/-! ### FACT 3 — WHY THE SHAPED THEOREMS ESCAPE, and how §3 was repaired.

`adaPlusOne` puts `cs` SECOND, after the ada slot. `validTxOutValue`
(CardanoLedgerApi/V1/Contexts.lean:787-802) demands `prev_cs < cs`, so at
`cs = adaSymbol` the shaped value is NOT ledger-valid and the whole shaped
statement is vacuous there. That is the ONLY reason `P1R_T1` survives with `cs`
free — and it is exactly the protection the unshaped statement lost.
`WSC/Benchmark/P1UnshapedStatement.lean` §2.1 restates the first theorem below
with the quantities SYMBOLIC (`validTxOutValue_adaPlusOne_at_ada`), which is what
§3.1's four vacuity branches consume. -/
theorem shaped_value_invalid_at_ada :
    CardanoLedgerApi.V2.validTxOutValue (adaPlusOne 200 adaCS (ByteString.mk "TOK") 5)
      = false := by
  native_decide

/-- …and the same value IS ledger-valid at a non-ada `cs`, so the shape is not
vacuous in general. -/
theorem shaped_value_valid_off_ada :
    CardanoLedgerApi.V2.validTxOutValue
      (adaPlusOne 200 (ByteString.mk "MMM") (ByteString.mk "TOK") 5) = true := by
  native_decide

#print axioms covering_false_at_ada
#print axioms ctxOk_quantities_MMM
#print axioms ctxOk_refutes_P1_at_ada
#print axioms shaped_value_invalid_at_ada
#print axioms shaped_value_valid_off_ada

end WSC.AdaRefutation
