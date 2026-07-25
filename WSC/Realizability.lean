/-
WSC/Realizability.lean — the **Conway `MissingRedeemers` rule as a decidable
predicate on a `ScriptContext`**, i.e. the LR-CTX row that
`WSC/Props/Shaped/ShapeRealizability.lean` §2 identified as missing from
`WSC/Honest.lean` and from CLAB's `validScriptContext` (task C2).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
`CardanoLedgerApi.V3.validScriptInfo` checks the redeemer map for the script
that is CURRENTLY RUNNING only
(`CardanoLedgerApi/V3/Contexts.lean:1035-1037`); there is no clause for "every
script this transaction needs has a redeemer-map entry". A context can therefore
satisfy `validMintingContext` / `validRewardingContext` and still be the context
of NO transaction a node would accept — which is exactly audit finding F2, and
exactly why every shape in the pre-C2 library is an empty class of ledger
transactions.

`redeemerCovered` below is that missing clause, spelled out as a `Bool` so a
concrete witness can discharge it by `native_decide`, and `RedeemerCoverage`
(the `Prop` form, restated here from `ShapeRealizability` so the shape modules
do not have to import the whole composition) is the hypothesis under which the
old shapes are provably empty.

**COORDINATION WITH C3 — RESOLVED, and the two predicates agree.** Task C3 landed
the rule on the CLAB side while this was being written
(`CardanoLedgerApi/V3/Contexts.lean`, commit `755d75e`): `scriptPurposesWitnessed`
(the six-source `getConwayScriptsNeeded`), `redeemerCoverage`, `noExtraRedeemers`,
`redeemersExact`, plus `LR_REDEEMER_COVERAGE` as row **S** of `WSC/Honest.lean`'s
LR-CTX table. This module survives as the WSC-local, `Bool`-shaped statement the
C2 shape proofs are written against, and §5 pins the relationship: **every re-cut
witness satisfies C3's `redeemersExact` — BOTH halves of `hasExactSetOfRedeemers`,
not merely the coverage half this module checks** (`WSC/Props/Shaped/
RealizableShapes.lean` §4). The two definitions are independent transcriptions of
the same Conway rule and they agree on all 12 witnesses tested, which is a
cross-check worth having.

Neither is a conjunct of `validScriptContext`, and C3's section header explains
why that is deliberate rather than an omission: the ledger filters `scriptsNeeded`
to non-native scripts (`Alonzo/Rules/Utxow.hs:247-251`) and `TxInfo` does not
record a script's language, so a coverage CONJUNCT would be over-strong. Nothing
here is an axiom and nothing here strengthens any assumption.

════════════════════════════════════════════════════════════════════════════
THE RULE, AND ITS SOURCE
════════════════════════════════════════════════════════════════════════════
Conway UTXOW's `scriptsNeeded`
(`eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxow.hs`, Alonzo
`ScriptsNeeded` / `MissingRedeemers`) needs one witness — and hence one
`Redeemers` entry — per

* **spending**: every transaction input whose payment credential is a script;
* **minting**: every policy id appearing in the mint field (ada cannot appear —
  `validMintValue` starts its fold at `adaSymbol` and demands
  `prev_cs < cs`, `CardanoLedgerApi/V3/Contexts.lean:836-848`);
* **rewarding**: every withdrawal whose credential is a script;
* certifying / voting / proposing: the analogous cases, which every shape in
  this library leaves EMPTY (`txInfoTxCerts = txInfoVotes =
  txInfoProposalProcedures = []`), so they are stated for completeness and are
  vacuously true at every shape here.

The Plutus `txInfoRedeemers` map IS that `Redeemers` set
(`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, audit row B
of `WSC/Honest.lean`'s LR-CTX table).

**MEASURED CORROBORATION (this task, over all 13 goldens).** Decoding each
golden `ScriptContext` and counting gives
`#redeemers = #script-inputs + #mint-policies + #script-withdrawals` **exactly**,
13/13:

| golden | script ins | mint policies | script wdrl | = | redeemers |
|---|---|---|---|---|---|
| `mint-local-registered-by-ref` | 0 | 1 | 1 | 2 | **2** |
| `mint-burnonly` | 1 | 1 | 3 | 5 | **5** |
| `mint-delegate-transfer-topup` | 1 | 1 | 3 | 5 | **5** |
| `seize-1-input` | 1 | 0 | 2 | 3 | **3** |
| `seize-2-inputs-partial-with-noise` | 2 | 0 | 2 | 4 | **4** |
| `transfer-nonmember-covering-node` | 1 | 0 | 1 | 2 | **2** |
| `base-spend-transfer-tx` | 1 | 0 | 2 | 3 | **3** |

and the decoded purpose kinds match the predicted multiset in every case (e.g.
`mint-burnonly` = `[Spending, Minting, Rewarding, Rewarding, Rewarding]`). So the
predicate below is not a guess at the rule: it reproduces the real node's output
on every vector this campaign measured. It also shows the goldens carry NO extra
redeemer, which is the other half of the Conway rule (`ExtraRedeemers`) — the
re-cut shapes of task C2 are built to hit the count EXACTLY, so they satisfy both
directions.
-/
import CardanoLedgerApi.V3

namespace WSC.Realizability

open CardanoLedgerApi.V3 (Credential CurrencySymbol MintValue RedeemerMap ScriptContext
                          ScriptHash ScriptPurpose TxInInfo Withdrawals findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## §0 Two `findRedeemer` lemmas the per-shape coverage proofs need

`findRedeemer` is `Recursor.findMap?`, i.e. a lifted `let rec go` whose `cons`
step is `if x.1 == purpose then some x.2 else go t`
(`CardanoLedgerApi/Recursors.lean:61-75`). The two lemmas below are that step, in
the two directions the coverage proofs use it. Both are the `show`-the-`if`-chain
technique `WSC/Props/Shaped/ShapeRealizability.lean` §2 uses; neither needs any
`Data`-level reasoning, so they hold for symbolic keys. -/

/-- Hit: the head entry's purpose IS the one looked up. -/
theorem findRedeemer_cons_hit (p : ScriptPurpose) (r : CardanoLedgerApi.V2.Redeemer)
    (rest : RedeemerMap) : findRedeemer p ((p, r) :: rest) = some r := by
  show (if (p == p) = true then some r else findRedeemer p rest) = some r
  simp

/-- Miss: the head entry's purpose is provably a different one. -/
theorem findRedeemer_cons_miss (p q : ScriptPurpose) (r : CardanoLedgerApi.V2.Redeemer)
    (rest : RedeemerMap) (h : (q == p) = false) :
    findRedeemer p ((q, r) :: rest) = findRedeemer p rest := by
  show (if (q == p) = true then some r else findRedeemer p rest) = findRedeemer p rest
  rw [h]; simp

/-- A `Minting` key never matches a `Rewarding` lookup — `rfl`, the constructors
differ before the symbolic hashes are inspected. -/
theorem minting_beq_rewarding (cs : CurrencySymbol) (c : Credential) :
    (ScriptPurpose.Minting cs == ScriptPurpose.Rewarding c) = false := rfl

/-- A `Spending` key never matches a `Minting` lookup. -/
theorem spending_beq_minting (o : CardanoLedgerApi.V3.TxOutRef) (cs : CurrencySymbol) :
    (ScriptPurpose.Spending o == ScriptPurpose.Minting cs) = false := rfl

/-- A `Spending` key never matches a `Rewarding` lookup. -/
theorem spending_beq_rewarding (o : CardanoLedgerApi.V3.TxOutRef) (c : Credential) :
    (ScriptPurpose.Spending o == ScriptPurpose.Rewarding c) = false := rfl

/-- A `Minting` key never matches a `Spending` lookup. -/
theorem minting_beq_spending (cs : CurrencySymbol) (o : CardanoLedgerApi.V3.TxOutRef) :
    (ScriptPurpose.Minting cs == ScriptPurpose.Spending o) = false := rfl

/-- A `Rewarding` key never matches a `Spending` lookup. -/
theorem rewarding_beq_spending (c : Credential) (o : CardanoLedgerApi.V3.TxOutRef) :
    (ScriptPurpose.Rewarding c == ScriptPurpose.Spending o) = false := rfl

/-- Two `Rewarding` keys at DIFFERENT script credentials do not match. (Restated
here from `WSC/Props/Shaped/ShapeRealizability.lean` §2 so the re-cut shape modules
need not import the composition layer.) -/
theorem rewarding_beq_rewarding_of_ne (w0 w1 : ScriptHash) (hne : w1 ≠ w0) :
    (ScriptPurpose.Rewarding (Credential.ScriptCredential w0) ==
      ScriptPurpose.Rewarding (Credential.ScriptCredential w1)) = false := by
  refine beq_eq_false_iff_ne.mpr ?_
  intro h
  injection h with h
  injection h with h
  exact hne h.symm

/-- A `Rewarding` key never matches a `Minting` lookup. -/
theorem rewarding_beq_minting (c : Credential) (cs : CurrencySymbol) :
    (ScriptPurpose.Rewarding c == ScriptPurpose.Minting cs) = false := rfl

/-- `Option.isSome` from `≠ none`, the shim the CLAB-vocabulary coverage proofs
need (CLAB's `coveredBy` is stated with `isSome`, this module's clauses with
`≠ none`). -/
theorem isSome_of_ne_none {o : Option PlutusCore.Data.Data} (h : o ≠ none) : o.isSome = true := by
  cases o with
  | none => exact absurd rfl h
  | some _ => rfl

/-! ## §1 The four coverage clauses, as `Bool`s -/

/-- Every input at a SCRIPT payment credential has a `Spending` redeemer entry. -/
def spendingCovered (ctx : ScriptContext) : Bool :=
  ctx.scriptContextTxInfo.txInfoInputs.all fun i =>
    if CardanoLedgerApi.V2.isScriptCredentialAddress i.txInInfoResolved.txOutAddress
    then (findRedeemer (.Spending i.txInInfoOutRef)
            ctx.scriptContextTxInfo.txInfoRedeemers).isSome
    else true

/-- Every policy id in the mint field has a `Minting` redeemer entry. A mint entry
whose key is not a `Data.B` is malformed and rejected outright (so is one carrying
the ada symbol, which `validMintValue` already forbids). -/
def mintingCovered (ctx : ScriptContext) : Bool :=
  ctx.scriptContextTxInfo.txInfoMint.all fun e =>
    match e.1 with
    | Data.B cs => (findRedeemer (.Minting cs)
                     ctx.scriptContextTxInfo.txInfoRedeemers).isSome
    | _ => false

/-- Every withdrawal at a SCRIPT credential has a `Rewarding` redeemer entry. -/
def rewardingCovered (ctx : ScriptContext) : Bool :=
  ctx.scriptContextTxInfo.txInfoWdrl.all fun e =>
    match e.1 with
    | .ScriptCredential h => (findRedeemer (.Rewarding (.ScriptCredential h))
                               ctx.scriptContextTxInfo.txInfoRedeemers).isSome
    | _ => true

/-- The certifying / voting / proposing clauses. Every shape in this library has
all three lists empty, so this is `true` by computation at each of them; it is
stated so that `redeemerCovered` is the WHOLE rule and not the part that happens
to bite. -/
def otherCovered (ctx : ScriptContext) : Bool :=
  ctx.scriptContextTxInfo.txInfoTxCerts.isEmpty &&
  ctx.scriptContextTxInfo.txInfoVotes.isEmpty &&
  ctx.scriptContextTxInfo.txInfoProposalProcedures.isEmpty

/-- **THE MISSING LR-CTX ROW.** Conway UTXOW `MissingRedeemers`, as a decidable
predicate on a `ScriptContext`. `validScriptContext ctx && redeemerCovered ctx` is
strictly stronger than `validScriptContext ctx` alone —
`WSC/Props/Shaped/ShapeRealizability.lean` §5 exhibits a witness satisfying the
first conjunct and provably NOT the second. -/
def redeemerCovered (ctx : ScriptContext) : Bool :=
  spendingCovered ctx && mintingCovered ctx && rewardingCovered ctx && otherCovered ctx

/-! ## §2 The `Prop` forms the emptiness proofs consume

`WSC/Props/Shaped/ShapeRealizability.lean` derives `False` from a shaped context
by exhibiting a SCRIPT withdrawal with no `Rewarding` entry
(`empty_of_uncovered_wdrl`), or — for SHAPE T1, unconditionally — a spent
mini-ledger input with no `Spending` entry. A re-cut shape is immune to BOTH
routes exactly when it satisfies the two predicates below at every leaf
assignment, and that is what the per-shape theorems in
`WSC/Props/Shaped/RealizableShapes.lean` prove. -/

/-- Withdrawal-side coverage, in the ∀-form that blocks
`ShapeRealizability.empty_of_uncovered_wdrl`. -/
def WdrlCovered (ctx : ScriptContext) : Prop :=
  ∀ (h : ScriptHash) (n : Integer),
    (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl →
      findRedeemer (.Rewarding (.ScriptCredential h))
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-- Spending-side coverage, in the ∀-form that blocks
`ShapeRealizability.t1_class_is_empty`'s route: for every input the transaction
spends from a script credential there is a `Spending` entry naming its
`TxOutRef`. -/
def SpendCovered (ctx : ScriptContext) : Prop :=
  ∀ i ∈ ctx.scriptContextTxInfo.txInfoInputs,
    CardanoLedgerApi.V2.isScriptCredentialAddress i.txInInfoResolved.txOutAddress = true →
      findRedeemer (.Spending i.txInInfoOutRef)
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-- Mint-side coverage, in ∀-form. -/
def MintCovered (ctx : ScriptContext) : Prop :=
  ∀ (cs : CurrencySymbol) (m : Data),
    (Data.B cs, m) ∈ ctx.scriptContextTxInfo.txInfoMint →
      findRedeemer (.Minting cs) ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-- **Realizability of one context, at the fidelity this substrate can express:**
the strongest ledger predicate CLAB offers, PLUS the `MissingRedeemers` row it is
missing, PLUS the two ∀-forms that block both emptiness routes.

WHAT THIS IS NOT. It is not "a node would accept this transaction": CLAB models
neither fees against a real protocol-parameter set, nor script-hash agreement
between a withdrawal credential and the script actually supplied, nor
`ExtraRedeemers` (though the C2 shapes hit the coverage count exactly, so they
carry no extra), nor anything about the UTxO set the inputs are drawn from. It is
the *removal of the one defect audit F2 identified*, and the honest claim is
exactly that. -/
def Realizable (ctx : ScriptContext) : Prop :=
  CardanoLedgerApi.V3.validScriptContext ctx = true ∧ redeemerCovered ctx = true ∧
    WdrlCovered ctx ∧ SpendCovered ctx ∧ MintCovered ctx

/-! ## §5 The STRONGER form, against C3's CLAB predicate

`Realizable` checks the `MissingRedeemers` half against this module's own
transcription. `RealizableExact` additionally demands C3's `redeemersExact`, i.e.
**both** halves of Conway's `hasExactSetOfRedeemers` — no needed script without an
entry AND no entry without a needed script — measured against CLAB's independent
six-source `scriptPurposesWitnessed`. The C2 shapes are cut to hit the count
exactly, so they satisfy it; `WSC/Props/Shaped/RealizableShapes.lean` §4 proves it
for every re-cut witness. -/
def RealizableExact (ctx : ScriptContext) : Prop :=
  Realizable ctx ∧ CardanoLedgerApi.V3.Contexts.redeemersExact ctx.scriptContextTxInfo = true

end WSC.Realizability
