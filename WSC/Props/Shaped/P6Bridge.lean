/-
WSC/Props/Shaped/P6Bridge.lean — connects the shaped P6 theorem (task V3) to the
COMPOSITION layer's vocabulary (task V4, `WSC/Composition.lean`), which landed in
parallel.

WHY THIS FILE. The two tasks independently defined the same two ground-truth
quantities:

* `WSC.outAtBaseQty` / `WSC.inAtBaseQty` (WSC/Props/Shaped/P6Shaped.lean) — over
  the output / input LISTS;
* `WSC.Composition.outAtB` / `WSC.Composition.inAtB` (WSC/Composition.lean:189-203)
  — over a whole `ScriptContext`, via `sumOutsIf (atBaseB base)` /
  `sumInsIf (atBaseB base)`.

They are the same function.  The two `rfl`s below prove it, and
`P6_shaped_CONTAIN` then restates the shaped P6 theorem in exactly the form
`WSC.Composition`'s `CONTAIN` obligation is stated in — so the composition layer
can consume the bytecode result directly instead of re-deriving it.

NO NEW TRUST.  Everything here is `rfl` plus the already-proved
`P6_shaped_member_adds_to_requirement`; the axiom set is unchanged (see
WSC/Shaped/Probe/V3Axioms.lean).
-/
import WSC.Props.Shaped.P6Shaped
import WSC.Composition

set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## The two vocabularies coincide -/

/-- `WSC.outAtBaseQty` (task V3) IS `WSC.Composition.outAtB` (task V4). -/
theorem outAtBaseQty_eq_outAtB (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) :
    outAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoOutputs
      = Composition.outAtB base cs tn ctx := by
  show outAtBaseQty base cs tn _ = Composition.sumOutsIf (Composition.atBaseB base) cs tn _
  induction ctx.scriptContextTxInfo.txInfoOutputs with
  | nil => rfl
  | cons o rest ih =>
      simp only [outAtBaseQty, Composition.sumOutsIf, Composition.atBaseB, ih]

/-- `WSC.inAtBaseQty` (task V3) IS `WSC.Composition.inAtB` (task V4). -/
theorem inAtBaseQty_eq_inAtB (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) :
    inAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoInputs
      = Composition.inAtB base cs tn ctx := by
  show inAtBaseQty base cs tn _ = Composition.sumInsIf (Composition.atBaseB base) cs tn _
  induction ctx.scriptContextTxInfo.txInfoInputs with
  | nil => rfl
  | cons i rest ih =>
      simp only [inAtBaseQty, Composition.sumInsIf, Composition.atBaseB, ih]

/-! ## P6, at UPLC, in the composition layer's own words -/

/-- **The shaped P6 theorem restated as `WSC.Composition`'s containment
inequality.** *An accepted `Member`-classified transfer of shape G6 satisfies
`outAtB base cs tn ctx ≥ inAtB base cs tn ctx + mintOf cs tn txInfoMint`, where
`base` is the credential the validator itself read out of the params datum.*

This is the form the composition's branch analysis consumes for the
"exit via global, `Member` classification" case. Scope is UNCHANGED and still
binding: budget 3300 AND shape G6 (see WSC/Props/Shaped/P6Shaped.lean's SCOPE
block, including the single-asset containment-path restriction). The composition
layer may NOT read this as a statement about all transactions. -/
theorem P6_shaped_CONTAIN
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (hv : validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee))
    (ha : isSuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)) :
    Composition.outAtB (Credential.ScriptCredential plc) cs tn
        (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
          pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)
      ≥ Composition.inAtB (Credential.ScriptCredential plc) cs tn
          (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
            pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)
        + mintOf cs tn
            (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
              pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo.txInfoMint := by
  have h := P6_shaped_member_adds_to_requirement ppCS cs tn q owner inAda ob0 outAda0 qq0
    ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee hv ha
  rw [← outAtBaseQty_eq_outAtB, ← inAtBaseQty_eq_inAtB]
  exact h

end WSC
