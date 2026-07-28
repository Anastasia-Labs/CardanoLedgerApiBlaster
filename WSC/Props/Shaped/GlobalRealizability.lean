-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/Shaped/GlobalRealizability.lean — **the REALIZABILITY theorems for the
re-cut global shapes, and the emptiness theorems for the ones they replace**
(task C1; the acceptance criterion of that task).

════════════════════════════════════════════════════════════════════════════
WHAT IS PROVED HERE, AND WHAT IT IS WORTH
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/ShapeRealizability.lean` (task A2) proves that every shape in
this library is EMPTY as a class of ledger transactions, by exhibiting a script
witness with no redeemer-map entry:

* SHAPE T1 — UNCONDITIONALLY (`t1_class_is_empty`): it spends an input at
  `ScriptCredential plc`, so `LR_SPEND_RUNS_VALIDATOR` + `LR_CTX` demand a
  `Spending` entry in a map that holds one `Rewarding` entry;
* SHAPES G1/L1/M1/S1/DT1 — under `RedeemerCoverageAllPlutus`, the `Prop` form of Conway
  UTXOW's `MissingRedeemers` rule stated there (§2).

This module does the converse for the six RE-CUT global shapes of
`WSC/Shaped/GlobalShapedR.lean`:

1. **§2 class level** — for EVERY leaf assignment, the shape's redeemer map
   covers every script witness the transaction has: a `Spending` entry per
   script-payment-credential input, a `Rewarding` entry per script-credential
   withdrawal, a `Minting` entry per minted policy. This is `RedeemerCovered`,
   stated below with all three clauses; its withdrawal clause is exactly the
   consequent of `ShapeRealizability.RedeemerCoverageAllPlutus`, so no member of these
   classes can be refuted the way the old ones were.
2. **§3 point level** — a CONCRETE context of each shape which is
   `validRewardingContext = true`, `RedeemerCovered`, and ACCEPTED by the real
   compiled bytecode. That is a witness that the class is non-empty in exactly
   the sense the emptiness proofs refute.
3. **§4** — the emptiness proofs for the three OLD shapes this task retires that
   `ShapeRealizability.lean` did not state (SHAPE G6 for P6, SHAPES T2/T6/T7 for
   P1), so the before/after table's "old verdict" column is PROVED, not asserted.

WHAT `RedeemerCovered` IS NOT. It is a NECESSARY condition for a node to accept
the transaction, not a sufficient one. A fully node-accepted transaction must
additionally have every OTHER script succeed — the base spending validator on
T1R's input 0, the per-policy transfer-logic script at withdrawal entry 1, the
issuance policy behind a `Minting` entry — and must satisfy the protocol
parameters (min-ada, fees, ex-units). Those are separate validators and separate
properties. What this module establishes is precisely the property whose absence
made the old classes EMPTY: nothing in the ledger's redeemer bookkeeping excludes
these transactions, and the strongest ledger predicate CLAB offers accepts a
concrete member of each class.

COORDINATION WITH TASK C3 — DONE, NOT DEFERRED. C3 landed the rule itself while
this unit was in flight (canonical HEAD 7174e3d): CLAB now has
`scriptPurposesWitnessed` (the `scriptsNeeded` transcription over all six
sources), `redeemerCoverageAllPlutus`, `noExtraRedeemersAllPlutus` and `redeemersExactAllPlutus`
(`CardanoLedgerApi/V3/Contexts.lean`), and `WSC/Honest.lean` has LR-CTX audit row
S plus the axiom `LR_REDEEMER_COVERAGE` with its corollary
`redeemerCoverageAllPlutus_wdrl`. This module was re-stated against them:

* **§2b** proves `redeemerCoverageAllPlutus … = true` for every leaf assignment of every
  re-cut shape — the class-level statement in CLAB's own ledger vocabulary;
* **§3** adds `redeemersExactAllPlutus … = true` (BOTH halves of the Conway rule) at each
  concrete witness;
* **§4**'s SHAPE G6 emptiness is now UNCONDITIONAL, discharged from
  `redeemerCoverageAllPlutus_wdrl` instead of a `RedeemerCoverageAllPlutus` hypothesis.

`RedeemerCovered` (§1) is KEPT because it is the ∀-form the emptiness proofs
consume directly and it makes each shape's three live arms readable one by one;
it is a consequence of §2b, not an extra assumption.
-/
import WSC.Props.Shaped.ShapeRealizability
import WSC.Props.Shaped.P1ShapedR
import WSC.Props.Shaped.P5ShapedR
import WSC.Props.Shaped.P6ShapedR
import WSC.Shaped.GlobalShapedP1Out

set_option warn.sorry false
set_option maxHeartbeats 0
-- the §3 realizability terms unify a witness `def` against its shape application
set_option maxRecDepth 1000000

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash ScriptPurpose
                          ScriptInfo TxInInfo TxOutRef TxOut RedeemerMap
                          findRedeemer hasCurrencySymbol validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
-- task C3 landed the Conway MissingRedeemers/ExtraRedeemers rule in CLAB itself;
-- §2b below states the class-level coverage in ITS vocabulary.
open CardanoLedgerApi.V3.Contexts (redeemerCoverageAllPlutus noExtraRedeemersAllPlutus redeemersExactAllPlutus
                                   coveredBy scriptPurposesWitnessed
                                   spendingPurposesWitnessed rewardingPurposesWitnessed
                                   certifyingPurposesWitnessed certifyingPurposesWitnessedFrom
                                   mintingPurposesWitnessed votingPurposesWitnessed
                                   proposingPurposesWitnessed proposingPurposesWitnessedFrom)

/-! # §1 The coverage predicate, and the two `findRedeemer` facts it needs -/

/-- **REDEEMER COVERAGE, POSITIVE FORM (a `Prop` about ONE context).** Every
script the Conway UTXOW rule `scriptsNeeded` collects for this transaction has a
redeemer-map entry:

* clause 1 — every SPENT input whose payment credential is a script hash has a
  `Spending` entry keyed by its `TxOutRef`;
* clause 2 — every SCRIPT-credential withdrawal has a `Rewarding` entry (this is
  exactly the consequent of `ShapeRealizability.RedeemerCoverageAllPlutus`, the rule the
  emptiness proofs use);
* clause 3 — every policy occurring in the mint field has a `Minting` entry.

Reference inputs are not spent and need no witness; pubkey inputs and pubkey
withdrawals need a VKey witness, not a redeemer; certificates, votes and
proposals are empty in every shape here. -/
def RedeemerCovered (ctx : ScriptContext) : Prop :=
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs, ∀ h : ScriptHash,
      payCred t.txInInfoResolved = Credential.ScriptCredential h →
      findRedeemer (.Spending t.txInInfoOutRef) ctx.scriptContextTxInfo.txInfoRedeemers ≠ none)
  ∧ (∀ (h : ScriptHash) (n : Integer),
      (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl →
      findRedeemer (.Rewarding (.ScriptCredential h))
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none)
  ∧ (∀ c : CurrencySymbol, hasCurrencySymbol c ctx.scriptContextTxInfo.txInfoMint = true →
      findRedeemer (.Minting c) ctx.scriptContextTxInfo.txInfoRedeemers ≠ none)

/-- The two-entry map of SHAPES G1R / G6R covers the own rewarding credential.
Kernel computation after one `beq_self`. -/
theorem globalR_rewarding_covered (cs w0 h : ByteString) (rMint : Integer) (own : Data)
    (hh : h = w0) :
    findRedeemer (.Rewarding (.ScriptCredential h)) (globalRRedeemers cs w0 rMint own) ≠ none := by
  subst hh
  show (if (ScriptPurpose.Minting cs == ScriptPurpose.Rewarding (Credential.ScriptCredential h))
          = true then some (Data.I rMint)
        else if (ScriptPurpose.Rewarding (Credential.ScriptCredential h)
                  == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
             then some own else none) ≠ none
  rw [show (ScriptPurpose.Minting cs
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  simp

/-- …and covers the minted policy. -/
theorem globalR_minting_covered (cs w0 : ByteString) (rMint : Integer) (own : Data) :
    findRedeemer (.Minting cs) (globalRRedeemers cs w0 rMint own) ≠ none := by
  show (if (ScriptPurpose.Minting cs == ScriptPurpose.Minting cs) = true
        then some (Data.I rMint)
        else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                  == ScriptPurpose.Minting cs) = true
             then some own else none) ≠ none
  simp

/-- The three-entry map of SHAPES T1R / T6R covers BOTH script withdrawals. The
`w0`/`w1` case split is on a decidable `Bool`, so no side condition is needed —
in particular the proof does not assume `w0 ≠ w1` (which `validWithdrawals`
supplies anyway). -/
theorem p1R_rewarding_covered (w0 w1 h : ByteString) (rBase rTls : Integer) (own : Data)
    (hh : h = w0 ∨ h = w1) :
    findRedeemer (.Rewarding (.ScriptCredential h)) (p1RRedeemers w0 w1 rBase rTls own) ≠ none := by
  show (if (ScriptPurpose.Spending ⟨ByteString.mk "", 0⟩
            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
        then some (Data.I rBase)
        else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                  == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
             then some own
             else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w1)
                       == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                  then some (Data.I rTls) else none) ≠ none
  rw [show (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  by_cases hw : (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
  · simp [hw]
  · have hw1 : h = w1 := by
      rcases hh with h1 | h1
      · exact absurd (by rw [h1]; simp) hw
      · exact h1
    subst hw1
    simp [hw]

/-- The three-entry map covers the `Spending` purpose of input 0 — the
mini-ledger input, the witness `t1_class_is_empty` used to prove SHAPE T1 empty
UNCONDITIONALLY. -/
theorem p1R_spending_covered (w0 w1 : ByteString) (rBase rTls : Integer) (own : Data) :
    findRedeemer (.Spending ⟨ByteString.mk "", 0⟩) (p1RRedeemers w0 w1 rBase rTls own)
      ≠ none := by
  have : findRedeemer (.Spending ⟨ByteString.mk "", 0⟩) (p1RRedeemers w0 w1 rBase rTls own)
      = some (Data.I rBase) := rfl
  simp [this]

/-- The four-entry map of SHAPE T2R covers the `Spending` purpose of input 0. -/
theorem p1RMint_spending_covered (cs w0 w1 : ByteString) (rBase rMint rTls : Integer)
    (own : Data) :
    findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
      (p1RMintRedeemers cs w0 w1 rBase rMint rTls own) ≠ none := by
  have : findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
      (p1RMintRedeemers cs w0 w1 rBase rMint rTls own) = some (Data.I rBase) := rfl
  simp [this]

/-- …the minted policy… -/
theorem p1RMint_minting_covered (cs w0 w1 : ByteString) (rBase rMint rTls : Integer)
    (own : Data) :
    findRedeemer (.Minting cs) (p1RMintRedeemers cs w0 w1 rBase rMint rTls own) ≠ none := by
  show (if (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
            == ScriptPurpose.Minting cs) = true then some (Data.I rBase)
        else if (ScriptPurpose.Minting cs == ScriptPurpose.Minting cs) = true
             then some (Data.I rMint)
             else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                       == ScriptPurpose.Minting cs) = true
                  then some own
                  else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w1)
                            == ScriptPurpose.Minting cs) = true
                       then some (Data.I rTls) else none) ≠ none
  rw [show (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
      == ScriptPurpose.Minting cs) = false from rfl]
  simp

/-- …and both script withdrawals. -/
theorem p1RMint_rewarding_covered (cs w0 w1 h : ByteString) (rBase rMint rTls : Integer)
    (own : Data) (hh : h = w0 ∨ h = w1) :
    findRedeemer (.Rewarding (.ScriptCredential h))
      (p1RMintRedeemers cs w0 w1 rBase rMint rTls own) ≠ none := by
  show (if (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
        then some (Data.I rBase)
        else if (ScriptPurpose.Minting cs
                  == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
             then some (Data.I rMint)
             else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
                       == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                  then some own
                  else if (ScriptPurpose.Rewarding (Credential.ScriptCredential w1)
                            == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
                       then some (Data.I rTls) else none) ≠ none
  rw [show (ScriptPurpose.Spending (⟨ByteString.mk "", 0⟩ : TxOutRef)
        == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl,
      show (ScriptPurpose.Minting cs
        == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = false from rfl]
  by_cases hw : (ScriptPurpose.Rewarding (Credential.ScriptCredential w0)
      == ScriptPurpose.Rewarding (Credential.ScriptCredential h)) = true
  · simp [hw]
  · have hw1 : h = w1 := by
      rcases hh with h1 | h1
      · exact absurd (by rw [h1]; simp) hw
      · exact h1
    subst hw1
    simp [hw]

/-- The mint field of every shape here is `Shape.mintOne cs tn q`, whose only
policy is `cs`. -/
theorem mintOne_hasCurrencySymbol (c cs tn : ByteString) (q : Integer)
    (h : hasCurrencySymbol c (Shape.mintOne cs tn q) = true) : c = cs := by
  simpa [Shape.mintOne, hasCurrencySymbol] using h

/-- `≠ none` in the `isSome` form CLAB's `coveredBy` unfolds to. -/
theorem isSome_of_findRedeemer_ne_none {o : Option PlutusCore.Data.Data} (h : o ≠ none) :
    o.isSome = true := by
  cases o with
  | none => exact absurd rfl h
  | some _ => rfl

/-! # §2 CLASS-LEVEL COVERAGE — every leaf assignment of every re-cut shape -/

/-- **SHAPE G1R is redeemer-covered, for every leaf assignment.** The sole input
is at a PUBKEY credential (clause 1 is vacuous), the sole withdrawal is the own
script credential (clause 2), and the sole minted policy is `cs` (clause 3). -/
theorem g1R_class_covered
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint fee : Integer) :
    RedeemerCovered
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [globalRShapedCtx] at ht
    subst ht
    exact absurd hpc (by simp [payCred])
  · intro h n hw
    simp [globalRShapedCtx, globalRWdrl] at hw
    exact globalR_rewarding_covered cs w0 h rMint globalShapedRedeemer hw.1
  · intro c hc
    rw [mintOne_hasCurrencySymbol c cs tn q hc]
    exact globalR_minting_covered cs w0 rMint globalShapedRedeemer

/-- **SHAPE G6R is redeemer-covered, for every leaf assignment.** Same three
clauses; the two outputs sit at script addresses, which need no witness. -/
theorem g6R_class_covered
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 qq0 : Integer)
    (ob1 : ByteString) (outAda1 qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint fee : Integer) :
    RedeemerCovered
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [memberRShapedCtx] at ht
    subst ht
    exact absurd hpc (by simp [payCred, memberShapedInput])
  · intro h n hw
    simp [memberRShapedCtx, globalRWdrl] at hw
    exact globalR_rewarding_covered cs w0 h rMint memberShapedRedeemer hw.1
  · intro c hc
    rw [mintOne_hasCurrencySymbol c cs tn q hc]
    exact globalR_minting_covered cs w0 rMint memberShapedRedeemer

/-- **SHAPE T1R is redeemer-covered, for every leaf assignment.** Clause 1 is the
one SHAPE T1 failed unconditionally: input 0 sits at `ScriptCredential plc` and
its `TxOutRef` is `⟨"",0⟩`, which the map's first entry names. Input 1 is at a
pubkey credential. Clause 3 is vacuous (empty mint). -/
theorem t1R_class_covered
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    RedeemerCovered
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1RShapedCtx] at ht
    rcases ht with rfl | rfl
    · exact p1R_spending_covered w0 w1 rBase rTls p1ShapedRedeemer
    · exact absurd hpc (by simp [payCred, p1ShapedExtIn])
  · intro h n hw
    simp [p1RShapedCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inl hh)
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inr hh)
  · intro c hc
    simp [p1RShapedCtx, hasCurrencySymbol] at hc

/-- **SHAPE T2R is redeemer-covered, for every leaf assignment.** T1R's clauses
plus the `Minting cs` entry the nonzero mint field needs. -/
theorem t2R_class_covered
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    RedeemerCovered
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1RShapedMintCtx] at ht
    rcases ht with rfl | rfl
    · exact p1RMint_spending_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint
    · exact absurd hpc (by simp [payCred, p1ShapedExtIn])
  · intro h n hw
    simp [p1RShapedMintCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1RMint_rewarding_covered cs w0 w1 h rBase rMint rTls p1ShapedRedeemerMint
        (Or.inl hh)
    · exact p1RMint_rewarding_covered cs w0 w1 h rBase rMint rTls p1ShapedRedeemerMint
        (Or.inr hh)
  · intro c hc
    rw [mintOne_hasCurrencySymbol c cs tn q hc]
    exact p1RMint_minting_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint

/-- **SHAPE T6R is redeemer-covered, for every leaf assignment.** -/
theorem t6R_class_covered
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    RedeemerCovered
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1ROutCtx] at ht
    rcases ht with rfl | rfl
    · exact p1R_spending_covered w0 w1 rBase rTls p1ShapedRedeemer
    · exact absurd hpc (by simp [payCred, p1ShapedExtIn])
  · intro h n hw
    simp [p1ROutCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inl hh)
    · exact p1R_rewarding_covered w0 w1 h rBase rTls p1ShapedRedeemer (Or.inr hh)
  · intro c hc
    simp [p1ROutCtx, hasCurrencySymbol] at hc

/-- **SHAPE T7R is redeemer-covered, for every leaf assignment.** T6R's clauses
plus the `Minting cs` entry. -/
theorem t7R_class_covered
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    RedeemerCovered
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht h hpc
    simp [p1ROutMintCtx] at ht
    rcases ht with rfl | rfl
    · exact p1RMint_spending_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint
    · exact absurd hpc (by simp [payCred, p1ShapedExtIn])
  · intro h n hw
    simp [p1ROutMintCtx, p1ShapedWdrl] at hw
    rcases hw with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact p1RMint_rewarding_covered cs w0 w1 h rBase rMint rTls p1ShapedRedeemerMint (Or.inl hh)
    · exact p1RMint_rewarding_covered cs w0 w1 h rBase rMint rTls p1ShapedRedeemerMint (Or.inr hh)
  · intro c hc
    rw [mintOne_hasCurrencySymbol c cs tn q hc]
    exact p1RMint_minting_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint

/-! # §2b THE SAME, IN CLAB'S OWN LEDGER VOCABULARY (task C3's `redeemerCoverageAllPlutus`)

Task C3 landed Conway UTXOW's `MissingRedeemers` / `ExtraRedeemers` rule inside
CLAB (`CardanoLedgerApi/V3/Contexts.lean`: `scriptPurposesWitnessed` transcribes
`scriptsNeeded` over all SIX sources, `redeemerCoverageAllPlutus` is the coverage half,
`redeemersExactAllPlutus` both halves) and assumed the coverage half in
`WSC/Honest.lean` as `LR_REDEEMER_COVERAGE` (LR-CTX audit row S). The six
theorems below are the strongest class-level statement available: for EVERY leaf
assignment, the re-cut shape satisfies CLAB's own transcription of the rule that
made the old shapes empty. They subsume §2's `RedeemerCovered` (which is kept
because it is the ∀-form the emptiness proofs consume directly) and additionally
discharge the certificate / vote / proposal arms, which are empty in every shape
here. -/

theorem g1R_class_coverage
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint fee : Integer) :
    redeemerCoverageAllPlutus
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint
        fee).scriptContextTxInfo = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        globalRShapedCtx, globalRWdrl, globalRRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (globalR_rewarding_covered cs w0 w0 rMint globalShapedRedeemer rfl),
         isSome_of_findRedeemer_ne_none
           (globalR_minting_covered cs w0 rMint globalShapedRedeemer)⟩

theorem g6R_class_coverage
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 qq0 : Integer)
    (ob1 : ByteString) (outAda1 qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint fee : Integer) :
    redeemerCoverageAllPlutus
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee).scriptContextTxInfo
      = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        memberRShapedCtx, memberShapedInput, globalRWdrl, globalRRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (globalR_rewarding_covered cs w0 w0 rMint memberShapedRedeemer rfl),
         isSome_of_findRedeemer_ne_none
           (globalR_minting_covered cs w0 rMint memberShapedRedeemer)⟩

theorem t1R_class_coverage
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    redeemerCoverageAllPlutus
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        p1RShapedCtx, p1ShapedBaseIn, p1ShapedExtIn, p1ShapedWdrl, p1RRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (p1R_spending_covered w0 w1 rBase rTls p1ShapedRedeemer),
         isSome_of_findRedeemer_ne_none
           (p1R_rewarding_covered w0 w1 w0 rBase rTls p1ShapedRedeemer (Or.inl rfl)),
         isSome_of_findRedeemer_ne_none
           (p1R_rewarding_covered w0 w1 w1 rBase rTls p1ShapedRedeemer (Or.inr rfl))⟩

theorem t2R_class_coverage
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    redeemerCoverageAllPlutus
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee).scriptContextTxInfo
      = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        p1RShapedMintCtx, p1ShapedBaseIn, p1ShapedExtIn, p1ShapedWdrl, p1RMintRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (p1RMint_spending_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint),
         isSome_of_findRedeemer_ne_none
           (p1RMint_rewarding_covered cs w0 w1 w0 rBase rMint rTls p1ShapedRedeemerMint
             (Or.inl rfl)),
         isSome_of_findRedeemer_ne_none
           (p1RMint_rewarding_covered cs w0 w1 w1 rBase rMint rTls p1ShapedRedeemerMint
             (Or.inr rfl)),
         isSome_of_findRedeemer_ne_none
           (p1RMint_minting_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint)⟩

theorem t6R_class_coverage
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rTls fee : Integer) :
    redeemerCoverageAllPlutus
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee).scriptContextTxInfo = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        p1ROutCtx, p1ShapedBaseIn, p1ShapedExtIn, p1ShapedWdrl, p1RRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (p1R_spending_covered w0 w1 rBase rTls p1ShapedRedeemer),
         isSome_of_findRedeemer_ne_none
           (p1R_rewarding_covered w0 w1 w0 rBase rTls p1ShapedRedeemer (Or.inl rfl)),
         isSome_of_findRedeemer_ne_none
           (p1R_rewarding_covered w0 w1 w1 rBase rTls p1ShapedRedeemer (Or.inr rfl))⟩

theorem t7R_class_coverage
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 rBase rMint rTls fee : Integer) :
    redeemerCoverageAllPlutus
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee).scriptContextTxInfo
      = true := by
  simp [redeemerCoverageAllPlutus, scriptPurposesWitnessed, spendingPurposesWitnessed,
        rewardingPurposesWitnessed, certifyingPurposesWitnessed, mintingPurposesWitnessed,
        votingPurposesWitnessed, proposingPurposesWitnessed, coveredBy,
        certifyingPurposesWitnessedFrom, proposingPurposesWitnessedFrom,
        CardanoLedgerApi.V3.Contexts.credScriptHash, Shape.mintOne,
        CardanoLedgerApi.V3.findRedeemer,
        p1ROutMintCtx, p1ShapedBaseIn, p1ShapedExtIn, p1ShapedWdrl, p1RMintRedeemers]
  exact ⟨isSome_of_findRedeemer_ne_none
           (p1RMint_spending_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint),
         isSome_of_findRedeemer_ne_none
           (p1RMint_rewarding_covered cs w0 w1 w0 rBase rMint rTls p1ShapedRedeemerMint
             (Or.inl rfl)),
         isSome_of_findRedeemer_ne_none
           (p1RMint_rewarding_covered cs w0 w1 w1 rBase rMint rTls p1ShapedRedeemerMint
             (Or.inr rfl)),
         isSome_of_findRedeemer_ne_none
           (p1RMint_minting_covered cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint)⟩

/-! # §3 POINT-LEVEL REALIZABILITY — a concrete member of each class

Each theorem below packages three facts about ONE concrete context of the shape:

* it satisfies `validRewardingContext` — the strongest ledger-normalization
  predicate CLAB offers, and the hypothesis of the corresponding P-theorem;
* it satisfies CLAB's `redeemersExactAllPlutus` — **BOTH halves** of Conway UTXOW's
  `hasExactSetOfRedeemers` (`MissingRedeemers` AND `ExtraRedeemers`, task C3's
  transcription): every needed script has an entry AND no entry names a purpose
  the transaction does not need. Machine-checked by `native_decide`;
* it is `RedeemerCovered` — the ∀-form of the condition whose failure made the
  OLD class empty;
* the REAL compiled bytecode accepts it inside the theorem's budget.

Taken together: the class the re-proved P-theorem quantifies over contains a
transaction that is ledger-consistent, redeemer-covered and actually accepted.
That is the acceptance criterion of task C1. -/

/-- **SHAPE G1R IS REALIZABLE** (P5's shape). Budget 1600, witness K = 1541. -/
theorem g1R_realizable :
    validRewardingContext P5RShapedWitness.ctx = true
    ∧ redeemersExactAllPlutus P5RShapedWitness.ctx.scriptContextTxInfo = true
    ∧ RedeemerCovered P5RShapedWitness.ctx
    ∧ isSuccessful
        (appliedGlobalShapedG1R.exec P5RShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK") 7
          (ByteString.mk "OWNER") 200
          (ByteString.mk "DEST") 150 7
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
          (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") 0 99
          50) :=
  ⟨P5RShapedWitness.ctx_valid, by native_decide, (g1R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") 7 (ByteString.mk "OWNER") 200 (ByteString.mk "DEST") 150 7
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
      (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1 (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS") (ByteString.mk "GLOBAL") 0 99 50), P5RShapedWitness.exec_accepts_at_1600⟩

/-- **SHAPE G6R IS REALIZABLE** (P6's shape). Budget 3300, witness K = 2837. -/
theorem g6R_realizable :
    validRewardingContext P6RShapedWitness.ctx = true
    ∧ redeemersExactAllPlutus P6RShapedWitness.ctx.scriptContextTxInfo = true
    ∧ RedeemerCovered P6RShapedWitness.ctx
    ∧ isSuccessful
        (appliedGlobalMemberShapedG6R.exec P6ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK") 7
          (ByteString.mk "OWNER") 200
          (ByteString.mk "PROGLOGIC") 100 4
          (ByteString.mk "PROGLOGIC") 50 3
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
          (ByteString.mk "SEIZE")
          (ByteString.mk "GLOBAL") 0 99
          50) :=
  ⟨P6RShapedWitness.ctx_valid, by native_decide, (g6R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") 7 (ByteString.mk "OWNER") 200 (ByteString.mk "PROGLOGIC") 100 4 (ByteString.mk "PROGLOGIC") 50 3
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE") (ByteString.mk "GLOBAL") 0 99 50), P6RShapedWitness.exec_accepts_at_3300⟩

/-- **SHAPE T1R IS REALIZABLE** (P1's base shape) — the one whose predecessor was
proved empty UNCONDITIONALLY. Budget 4400, witness K = 2603. -/
theorem t1R_realizable :
    validRewardingContext P1RShapedWitness.ctxOk = true
    ∧ redeemersExactAllPlutus P1RShapedWitness.ctxOk.scriptContextTxInfo = true
    ∧ RedeemerCovered P1RShapedWitness.ctxOk
    ∧ isSuccessful
        (appliedGlobalShapedT1R.exec P1ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
          (ByteString.mk "EXT") 100 4
          150 5
          (ByteString.mk "DEST") 100 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 88
          50) :=
  ⟨P1RShapedWitness.ctxOk_valid, by native_decide, (t1R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 (ByteString.mk "EXT") 100 4 150 5 (ByteString.mk "DEST") 100 4
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
      (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1 (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 88 50),
   P1RShapedWitness.exec_accepts_T1R_at_4400⟩

/-- **SHAPE T2R IS REALIZABLE** (P1's mint shape), at the BURN witness — the same
context that refutes the `mintPos` form. Budget 4400, witness K = 3572. -/
theorem t2R_realizable :
    validRewardingContext P1RShapedWitness.ctxBurn = true
    ∧ redeemersExactAllPlutus P1RShapedWitness.ctxBurn.scriptContextTxInfo = true
    ∧ RedeemerCovered P1RShapedWitness.ctxBurn
    ∧ isSuccessful
        (appliedGlobalShapedT2R.exec P1ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
          (ByteString.mk "EXT") 100 4
          150 1
          (ByteString.mk "DEST") 100 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 99 88
          50) :=
  ⟨P1RShapedWitness.ctxBurn_valid, by native_decide, (t2R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") (-4) (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 (ByteString.mk "EXT") 100 4 150 1 (ByteString.mk "DEST") 100 4
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
      (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1 (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 99 88 50),
   P1RShapedWitness.exec_accepts_T2R_burn_at_4400⟩

/-- **SHAPE T6R IS REALIZABLE** (P1's output-aggregation shape). Budget 4400,
witness K = 3150. -/
theorem t6R_realizable :
    validRewardingContext P1RShapedWitness.ctxOut = true
    ∧ redeemersExactAllPlutus P1RShapedWitness.ctxOut.scriptContextTxInfo = true
    ∧ RedeemerCovered P1RShapedWitness.ctxOut
    ∧ isSuccessful
        (appliedGlobalShapedT6R.exec P1ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK")
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
          (ByteString.mk "EXT") 100 4
          100 3 60 2
          (ByteString.mk "DEST") 90 4
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 88
          50) :=
  ⟨P1RShapedWitness.ctxOut_valid, by native_decide, (t6R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 (ByteString.mk "EXT") 100 4 100 3 60 2 (ByteString.mk "DEST") 90 4
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
      (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1 (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 88 50),
   P1RShapedWitness.exec_accepts_T6R_at_4400⟩

/-- **SHAPE T7R IS REALIZABLE** (P1's strongest shape: aggregation + mint), at the
burn witness. Budget 4400, witness K = 3572. -/
theorem t7R_realizable :
    validRewardingContext P1RShapedWitness.ctxOutBurn = true
    ∧ redeemersExactAllPlutus P1RShapedWitness.ctxOutBurn.scriptContextTxInfo = true
    ∧ RedeemerCovered P1RShapedWitness.ctxOutBurn
    ∧ isSuccessful
        (appliedGlobalShapedT7R.exec P1ShapedWitness.ppCS
          (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
          (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
          (ByteString.mk "EXT") 100 4
          100 1 60 1
          (ByteString.mk "DEST") 90 3
          (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
          (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
          (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
          (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
          (ByteString.mk "GS")
          (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
          77 99 88
          50) :=
  ⟨P1RShapedWitness.ctxOutBurn_valid, by native_decide, (t7R_class_covered (ByteString.mk "MMM") (ByteString.mk "TOK") (-4) (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 (ByteString.mk "EXT") 100 4 100 1 60 1 (ByteString.mk "DEST") 90 3
      (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1 (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
      (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1 (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS") (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 77 99 88 50),
   P1RShapedWitness.exec_accepts_T7R_burn_at_4400⟩

/-! # §4 THE SHAPES THIS TASK RETIRES — their emptiness, proved

`ShapeRealizability.lean` proves T1 (unconditionally) and G1 (under
`RedeemerCoverageAllPlutus`). The three shapes below carry the other P1/P6 dimensions this
task re-cuts, and their emptiness was not stated anywhere. Proving it here is
what makes the before/after table's "old verdict" column evidence rather than
extrapolation. -/

open ShapeRealizability (RedeemerCoverageAllPlutus empty_of_uncovered_wdrl
                         RedeemerCoverageTrue RedeemerCoverageAt_of_true
                         empty_of_uncovered_wdrl_at
                         rewarding_singleton_covers_only_itself
                         not_onChain_of_no_redeemer)

/-- **SHAPE G6 (P6's shape) — EMPTY, UNCONDITIONALLY.** Withdrawal entry 1 is
`ScriptCredential w1` and the one-entry redeemer map covers only `Rewarding w0`,
so Conway's `MissingRedeemers` excludes the whole class. When
`ShapeRealizability.lean` was written this needed its local `RedeemerCoverageAllPlutus`
`Prop` as a hypothesis; task C3 has since landed the rule as
`WSC.LR_REDEEMER_COVERAGE` (LR-CTX audit row S) with the ready-made corollary
`WSC.redeemerCoverageAllPlutus_wdrl`, so the statement is now unconditional — this is the
first shape-emptiness result to use it. (`w0 ≠ w1` is forced by
`validWithdrawals`, audit row L.)

**F18 DOWNGRADE (task G2). The word UNCONDITIONALLY above is conditional on an
over-strong axiom.** `LR_REDEEMER_COVERAGE` asserts the ALL-PLUTUS reading of
`MissingRedeemers`; Conway keeps only needed scripts with
`not (isNativeScript script)` (`Alonzo/Rules/Utxow.hs:247-251`), and `w1` here is
a free `ByteString` parameter of `memberShapedCtx` — nothing pins it to a Plutus
script. Under the TRUE rule this class is empty only for members whose
withdrawal at `w1` is not a native timelock. `g6_class_is_empty_nonNative` below
is that statement, with the side condition explicit; this theorem is retained
because it is what the library's axiom set actually proves, and the census entry
`#print axioms WSC.g6_class_is_empty` is where the dependence on
`LR_REDEEMER_COVERAGE` is visible. See `ShapeRealizability.lean` §2.3 for the
full per-use audit. -/
theorem g6_class_is_empty
    (ctx : ScriptContext) (hoc : OnChain ctx)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 qq0 : Integer)
    (ob1 : ByteString) (outAda1 qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hne : w1 ≠ w0)
    (hsh : ctx.scriptContextTxInfo =
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine redeemerCoverageAllPlutus_wdrl ctx w1 a1 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hsh]; exact rewarding_singleton_covers_only_itself w0 w1 _ hne

/-- **SHAPE G6 — EMPTY UNDER THE TRUE CONWAY RULE, with the F18 side condition
made explicit.** Identical to `g6_class_is_empty` except that the coverage rule
is `ShapeRealizability.RedeemerCoverageTrue`, i.e. the rule with the ledger's
`not (isNativeScript …)` filter restored, and the argument therefore has to be
told that the shape's second withdrawal credential `w1` is not a native script.

This is the honest statement of what retiring SHAPE G6 rests on. Note what it
does NOT need: no axiom at all — `isNative` is an arbitrary predicate and `rc`
is a hypothesis, so this theorem's axiom census is empty where
`g6_class_is_empty`'s carries `LR_REDEEMER_COVERAGE`. -/
theorem g6_class_is_empty_nonNative {isNative : ByteString → Prop}
    (rc : RedeemerCoverageTrue isNative)
    (ctx : ScriptContext) (hoc : OnChain ctx)
    (cs tn : ByteString) (q : Integer) (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 qq0 : Integer)
    (ob1 : ByteString) (outAda1 qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hne : w1 ≠ w0)
    (hnn : ¬ isNative w1)
    (hsh : ctx.scriptContextTxInfo =
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at (RedeemerCoverageAt_of_true rc hnn) ctx a1 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hsh]; exact rewarding_singleton_covers_only_itself w0 w1 _ hne

/-- **SHAPE T2 (P1's mint shape) — EMPTY UNCONDITIONALLY**, by SHAPE T1's
spending route: it spends the same `ScriptCredential plc` input at `⟨"",0⟩` and
its redeemer map holds exactly one `Rewarding` entry. Trust cost identical to
`t1_class_is_empty`: `Deployed`, `OnChain`, `LR_SPEND_RUNS_VALIDATOR`, `LR_CTX`. -/
theorem t2_class_is_empty
    (hp : HonestParams) (ctx : ScriptContext)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hdep : Deployed hp) (hoc : OnChain ctx)
    (hbase : hp.progLogicCred = Credential.ScriptCredential plc)
    (hsh : ctx.scriptContextTxInfo =
      (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  have ht : p1ShapedBaseIn plc owner inAda cs tn qIn ∈ ctx.scriptContextTxInfo.txInfoInputs := by
    rw [hsh]; exact List.mem_cons_self ..
  have hpc : payCred (p1ShapedBaseIn plc owner inAda cs tn qIn).txInInfoResolved
      = hp.progLogicCred := by rw [hbase]; rfl
  obtain ⟨r, d, hoc', -⟩ := LR_SPEND_RUNS_VALIDATOR hp ctx _ hdep hoc ht hpc
  refine not_onChain_of_no_redeemer _ ?_ hoc'
  show findRedeemer (.Spending _) ctx.scriptContextTxInfo.txInfoRedeemers = none
  rw [hsh]
  rfl

/-- **SHAPE T6 (P1's output-aggregation shape) — EMPTY UNCONDITIONALLY**, same
route. -/
theorem t6_class_is_empty
    (hp : HonestParams) (ctx : ScriptContext)
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hdep : Deployed hp) (hoc : OnChain ctx)
    (hbase : hp.progLogicCred = Credential.ScriptCredential plc)
    (hsh : ctx.scriptContextTxInfo =
      (p1ShapedOutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  have ht : p1ShapedBaseIn plc owner inAda cs tn qIn ∈ ctx.scriptContextTxInfo.txInfoInputs := by
    rw [hsh]; exact List.mem_cons_self ..
  have hpc : payCred (p1ShapedBaseIn plc owner inAda cs tn qIn).txInInfoResolved
      = hp.progLogicCred := by rw [hbase]; rfl
  obtain ⟨r, d, hoc', -⟩ := LR_SPEND_RUNS_VALIDATOR hp ctx _ hdep hoc ht hpc
  refine not_onChain_of_no_redeemer _ ?_ hoc'
  show findRedeemer (.Spending _) ctx.scriptContextTxInfo.txInfoRedeemers = none
  rw [hsh]
  rfl

/-- **SHAPE T7 (P1's aggregation + mint shape) — EMPTY UNCONDITIONALLY**, same
route. -/
theorem t7_class_is_empty
    (hp : HonestParams) (ctx : ScriptContext)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hdep : Deployed hp) (hoc : OnChain ctx)
    (hbase : hp.progLogicCred = Credential.ScriptCredential plc)
    (hsh : ctx.scriptContextTxInfo =
      (p1ShapedOutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  have ht : p1ShapedBaseIn plc owner inAda cs tn qIn ∈ ctx.scriptContextTxInfo.txInfoInputs := by
    rw [hsh]; exact List.mem_cons_self ..
  have hpc : payCred (p1ShapedBaseIn plc owner inAda cs tn qIn).txInInfoResolved
      = hp.progLogicCred := by rw [hbase]; rfl
  obtain ⟨r, d, hoc', -⟩ := LR_SPEND_RUNS_VALIDATOR hp ctx _ hdep hoc ht hpc
  refine not_onChain_of_no_redeemer _ ?_ hoc'
  show findRedeemer (.Spending _) ctx.scriptContextTxInfo.txInfoRedeemers = none
  rw [hsh]
  rfl

/-! # §5 AXIOM CENSUS — printed at build time

The class-coverage and realizability theorems must depend on NO project axiom
(they are statements about `Data` skeletons and CLAB predicates); the three
emptiness theorems in §4 depend on exactly the LR axioms their SHAPE-T1/G1
counterparts do. -/
#print axioms WSC.g1R_class_covered
#print axioms WSC.g6R_class_covered
#print axioms WSC.t1R_class_covered
#print axioms WSC.t2R_class_covered
#print axioms WSC.t6R_class_covered
#print axioms WSC.t7R_class_covered
#print axioms WSC.g1R_class_coverage
#print axioms WSC.g6R_class_coverage
#print axioms WSC.t1R_class_coverage
#print axioms WSC.t2R_class_coverage
#print axioms WSC.t6R_class_coverage
#print axioms WSC.t7R_class_coverage
#print axioms WSC.g1R_realizable
#print axioms WSC.g6R_realizable
#print axioms WSC.t1R_realizable
#print axioms WSC.t2R_realizable
#print axioms WSC.t6R_realizable
#print axioms WSC.t7R_realizable
#print axioms WSC.g6_class_is_empty
-- F18: the true-rule form of the same result. Its census must be EMPTY of
-- project axioms — that is the point of stating it.
#print axioms WSC.g6_class_is_empty_nonNative
#print axioms WSC.t2_class_is_empty
#print axioms WSC.t6_class_is_empty
#print axioms WSC.t7_class_is_empty
-- the five re-proved headlines: `sorryAx` is blaster's `admit` (SPIKE-FINDINGS),
-- and the point of the census is that NO project axiom appears in any of them.
#print axioms WSC.P1R_T1
#print axioms WSC.P1R_T2
#print axioms WSC.P1R_T6
#print axioms WSC.P1R_T7
#print axioms WSC.P5R_shaped_indexed
#print axioms WSC.P6R_shaped_member_adds_to_requirement

end WSC
