/-
WSC/Props/Shaped/P6Vocab.lean — P6's GROUND-TRUTH vocabulary, split out of
`WSC/Props/Shaped/P6Shaped.lean` (task N4, PR #112).

WHY THE SPLIT. `P6Shaped` states P6 over SHAPE G6, the pre-re-cut shape whose
class is EMPTY (two script withdrawals, one redeemer entry). `P6ShapedR` states
the same property over the realizable SHAPE G6R and needs nothing from
`P6Shaped` except these two definitions — but it was importing the whole module,
and therefore inheriting its solver results.

Against the PR #112 bytecode that stopped being harmless: four of `P6Shaped`'s
stanzas now die with `Unexpected smt error: (error "… Overflow encountered when
expanding vector")` from the SMT backend (defect **D9**, recorded in
WSC/IMPACT-PR112.md). Those are failures of the INVALIDATED shape, and there is
no reason for the realizable result to be held hostage to them.

Keeping the definitions here rather than duplicating them in `P6ShapedR` matters
for the anti-tautology discipline: `P6ShapedR`'s postcondition must be the SAME
object `P6Shaped`'s was, in ground-truth vocabulary, not a restatement that
drifted. Both modules import this one, so that is now structural.

These are ledger-side definitions over `ScriptContext` fields. They mention no
validator accumulator; the "validator-side counterpart" lines are commentary,
and the line numbers in them are re-read at wsc-poc main @ 2306678.
-/
import WSC.Spec
import CardanoLedgerApi.V3
import PlutusCore.UPLC

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName TxOut TxInInfo valueOf)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **GROUND TRUTH.** Total quantity of the asset `(cs, tn)` sitting at outputs
whose payment credential is the mini-ledger base credential `base`.

Validator-side counterpart (commentary only): the accumulator of
`hasAtLeastAssetInProgOutputs` (ProgrammableLogicBase.hs:604-621, re-read at 2306678), which sums
`passetQtyInValue` over exactly those outputs. -/
def outAtBaseQty (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if payCred o == base then valueOf cs tn o.txOutValue else 0)
        + outAtBaseQty base cs tn rest

/-- **GROUND TRUTH.** Total quantity of the asset `(cs, tn)` spent from the
mini-ledger base credential.

Validator-side counterpart (commentary only): `pvalueFromCred`
(ProgrammableLogicBase.hs:328-439, re-read at 2306678 — PR #112 rewrote this
function: the owner witness for a SCRIPT-owned input is now an INDEXED lookup at
:386-393 rather than a scan). -/
def inAtBaseQty (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if payCred i.txInInfoResolved == base then valueOf cs tn i.txInInfoResolved.txOutValue else 0)
        + inAtBaseQty base cs tn rest

/-! ## Witness helpers, shared by SHAPE G6 and SHAPE G6R

Also split out of `P6Shaped` (task N4): `P6ShapedR`'s §5 witness section uses
these, and they are pure definitions with no solver content, so there is no
reason for them to travel with the invalidated shape's theorems. Kept in the
`P6ShapedWitness` namespace so every existing reference resolves unchanged. -/
namespace P6ShapedWitness

def ppCS  : CurrencySymbol := ByteString.mk "PARAMS"
def base  : Credential     := .ScriptCredential (ByteString.mk "PROGLOGIC")
def cs    : CurrencySymbol := ByteString.mk "MMM"
def tn    : TokenName      := ByteString.mk "TOK"

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

end P6ShapedWitness

end WSC
