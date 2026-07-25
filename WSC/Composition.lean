/-
WSC/Composition.lean — the composition layer (task V4): the ledger-level
objects the per-validator leaves cannot express, the per-transaction
Preservation theorem, and the lift to the top-level plain-English claim.

READ `§9 DISCHARGE STATUS` AT THE BOTTOM BEFORE CITING ANYTHING FROM THIS FILE.

## What this file is, and what it is not

It is a **machine-checked reduction** of

> *In an honest deployment, programmable tokens cannot exist outside the
> mini-ledger (the `programmableLogicBase` payment credential).*

to a precise, small, honest list of obligations. The reduction itself — §7's
`preservation` and §8's `top_claim` — is real, unconditional Lean: it is proved
from EXPLICIT hypotheses, one per leaf it consumes, plus the ledger-level axioms
of §4 and the per-transaction axioms of `WSC/Honest.lean`. It is NOT a claim that
those hypotheses hold. §9 instantiates each one with what the library actually
has today and labels it
`PROVED-UNSHAPED` / `PROVED-SHAPED(scope)` / `MODEL+AXIOM` / `STILL-OPEN`.

**That list IS the deliverable, including the entries that are open.** Swapping
an entry from open to discharged is a one-line change: replace the corresponding
field of `LeafSet` (§6) with the library theorem, in §9.

## The honest scope of the top theorem, in full

1. **BOUNDED TRANSACTIONS (ADDENDUM E1).** Every transaction in the class carries
   `WithinBudget` (§5): its validator runs halt within the PUBLISHED per-validator
   CEK step bounds `K_base = 600`, `K_mint = 900`, `K_global = 4400`
   (`WSC/Honest.lean`; `K_global` was republished from 1600 by task U2 — see its
   docstring for the measurement that forced it). No result here covers
   unboundedly large transactions.
   There is deliberately **no `K_seize`** (`WSC/Honest.lean` "K_seize —
   DELIBERATELY UNAVAILABLE"), so the seize route is bridged by
   `LR_SEIZE_HALTS` (§4) instead, which is unbounded but weaker.
2. **SHAPE RESTRICTIONS (task Z2).** Every transaction in the class also carries
   an abstract `Shape` predicate. Instantiating a leaf with a `by blaster`
   theorem proved over a SHAPED context (P4a/P4-burn over SHAPE M1/M2, P5 over
   SHAPE G1) forces `Shape` to be "`ctx` is an instance of that shape", which is
   a severe restriction on list lengths, constructor tags and `Option`s — and,
   additionally, needs the SHAPE-BRIDGE obligation of §9.4. `Shape := fun _ =>
   True` is the unrestricted class, and no shaped leaf can discharge a hypothesis
   at that instantiation.
3. **`DirWF` IS ASSUMED, AND IT IS ESCAPE-CRITICAL.** The top claim is exactly as
   strong as the directory well-formedness axioms `DIRWF` (four conjuncts,
   `WSC/Honest.lean`) and `DIRWF_L` (§4, the ledger-level non-overlap form).
   Conjuncts (i) insert-only, (iii) NFT-name/datum binding and (iv) interval
   non-overlap are the escape-critical ones. `U10` — formalizing
   `mkDirectoryNodeMP` at UPLC and proving per-insert preservation, then lifting
   over history — is what would discharge them.
4. **FAITHFULNESS AXIOMS.** Where a leaf is discharged by the source-model route
   the corresponding `<model>_faithful` axiom (`WSC.SeizeModel.seizeModel_faithful`
   for P2, `WSC.Model.globalModel_faithful` for P1/P6) enters the trust base. Each
   is a WHOLE-VALIDATOR equivalence between a hand transcription and the compiled
   bytecode, evidenced by source-line citations and golden differential agreement
   (13/13 seize, 4/4 global) — not proved.
5. **`OnChain` / `Deployed` are never discharged**: they are the model/chain
   bridge (`WSC/Honest.lean`).

Nothing in this file uses the phrase "PROVEN-BY-DESIGN" (ADDENDUM E10 forbids
it), and no statement here claims unbounded coverage.

## Layout

* §1 ledger-level objects: `UTxO`, `Ledger`, `OutOfBase`, `RegisteredIn`, `I`
* §2 per-transaction sums (`inAtB`/`outAtB`/`inOff`/`outOff`)
* §3 proved arithmetic and `Value` facts
* §4 the ledger-level axioms genuinely missing from `WSC/Honest.lean`
* §5 the transaction class (`WithinBudget`, `Shape`, `HonestTx`) — ADDENDUM E1
* §6 `LeafSet` — one explicit hypothesis per leaf consumed
* §7 `preservation` (proved) + the branch lemmas
* §8 `Reachable` and `top_claim` (proved)
* §9 DISCHARGE STATUS
-/
import WSC.Honest
import WSC.Props.P3_Base
-- Task U2: `WSC.P4Witness` (the concrete `BurnOnly` minting context) and
-- `appliedMinting900`, used to DISCHARGE `WSC.MintingNonVacuous` as a theorem in
-- §9.5a. This module does NOT import `WSC.Honest`, so there is no cycle, and it
-- is already elaborated by the time this file is built (no prep cost added).
import WSC.Props.P4_Minting
-- Task U2: the SOURCE-MODEL ground-truth vocabulary (`Model.outSum`,
-- `Model.inSum`, `Model.hasCSH`, `Model.dirNodeFields`), so that §10's
-- VOCABULARY BRIDGES are real theorems rather than prose. `WSC/Model/Ground.lean`
-- imports only `CardanoLedgerApi.V3`, `WSC.Redeemer`, `WSC.Spec` and
-- `PlutusCore.Value.Algebra` — no `#prep_uplc`, no `blaster`, no `WSC.Honest`.
import WSC.Model.Ground

namespace WSC.Composition

open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo ScriptHash TxInInfo TxOutRef
                          hasCurrencySymbol valueOf credentialInWithdrawals
                          validSpendingContext validScriptContext
                          merge withoutLovelace valueSpent valueProduced isBalanced)
open CardanoLedgerApi.V1.Value (adaSymbol)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! # §1 Ledger-level objects

These are the objects no leaf can express, because a leaf only ever sees one
`ScriptContext`. -/

/-- A ledger UTxO: an output together with the reference that identifies it. The
`TxOutRef` is what makes ledger-level uniqueness statements meaningful
(`WSC/Honest.lean`'s `dirKeyUniqueOuts` records the limitation this fixes). -/
structure UTxO where
  utxoRef : TxOutRef
  utxoOut : TxOut
deriving Repr

/-- The ledger state: its UTxO set, as a list. A list rather than a `Finset`
because every statement below is either a membership fact or a SUM, and the sums
are the reason: `OutOfBase` must not silently deduplicate.

HONEST NOTE: consequently `Ledger` does not itself enforce that `utxoRef`s are
distinct. Distinctness is a ledger rule (no double spend) and is not needed by
anything below — `preservation` consumes only membership facts and the
`OutOfBase` balance equation of `lr_utxo_semantics`. -/
abbrev Ledger := List UTxO

/-- The outputs of a ledger, forgetting the references — the snapshot the
directory predicates of `WSC/Honest.lean` are stated over. -/
def ledgerOuts (L : Ledger) : List TxOut := L.map (·.utxoOut)

/-- Total quantity of the asset slot `(cs, tn)` held by a list of UTxOs. -/
def sumHoldU (cs : CurrencySymbol) (tn : TokenName) : Ledger → Int
  | [] => 0
  | u :: rest => valueOf cs tn u.utxoOut.txOutValue + sumHoldU cs tn rest

/-- `u` does NOT sit at the mini-ledger base payment credential. -/
def offBase (base : Credential) (u : UTxO) : Bool := !(WSC.payCred u.utxoOut == base)

/-- **`OutOfBase(L, cs, tn)`** (ARCHITECTURE.md §5.1): the total amount of the
asset slot `(cs, tn)` held OUTSIDE the mini-ledger.

DEVIATION FROM §5.1, stated: §5.1 writes `hold(u,cs) = Σ_tn valueOf cs tn`, a sum
over token names. This file indexes by the SLOT `(cs, tn)` instead, which avoids
needing a finite-support sum over an unbounded `TokenName` and is EQUIVALENT
given non-negativity (`NONNEG_L`): `∀ tn, OutOfBase … = 0` iff the per-policy sum
is 0. It is also the vocabulary the leaves speak — every containment leaf is
per-slot. -/
def OutOfBase (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (L : Ledger) : Int :=
  sumHoldU cs tn (L.filter (offBase base))

/-- **`R(L)`** (ARCHITECTURE.md §5.1): `cs` is a REGISTERED programmable policy in
ledger state `L` — some UTxO of `L` is an authentic directory node keyed `cs`.
Ground truth: `WSC/Honest.lean`'s `registeredIn` over the ledger snapshot. -/
def RegisteredIn (hp : WSC.HonestParams) (L : Ledger) (cs : CurrencySymbol) : Prop :=
  WSC.registeredIn hp.directoryNodeCS cs (ledgerOuts L)

/-- **THE INVARIANT `I(L)`** (ARCHITECTURE.md §5.1): *no registered programmable
token exists outside the mini-ledger.*

**FINDING — why the `cs ≠ adaSymbol` side condition is MANDATORY.** §5.1 writes
`I(L) = ∀ cs ∈ R L, OutOfBase L cs = 0` with no exclusion. That statement is
FALSE in every live deployment: the directory's HEAD SENTINEL node is keyed with
the empty `ByteString` (`PTokenDirectory.hs:216-223`, cited in `WSC.TS4`'s
docstring), and `adaSymbol = ""` (`CardanoLedgerApi/V1/Value.lean:14`), so the
sentinel makes `RegisteredIn hp L adaSymbol` TRUE — and the invariant would then
demand that no lovelace exists outside the mini-ledger. The exclusion is not a
weakening trick: `cs ≠ ByteString.mk ""` is already carried by every containment
leaf in the library (`WSC.Model.P1_model`, `L1_3_valueFromCred_counts_all_base_inputs`,
`L1_1b_pathB_sound`), and `WSC.LR3` makes `txInfoMint` ada-free, so ada can never
be a programmable-token policy in the first place. -/
def I (hp : WSC.HonestParams) (L : Ledger) : Prop :=
  ∀ (cs : CurrencySymbol) (tn : TokenName),
    cs ≠ adaSymbol → RegisteredIn hp L cs → OutOfBase hp.progLogicCred cs tn L = 0

/-! # §2 Per-transaction sums

The four quantities the branch analysis moves value between. All are ground
truth: CLAB `valueOf` over `ScriptContext` fields, filtered by the payment
credential (ARCHITECTURE.md Tier 0.1 — no validator accumulator appears
anywhere). -/

/-- `o` sits at the mini-ledger base payment credential. -/
def atBaseB (base : Credential) (o : TxOut) : Bool := WSC.payCred o == base

/-- `o` does NOT sit at the mini-ledger base payment credential. -/
def offBaseB (base : Credential) (o : TxOut) : Bool := !(WSC.payCred o == base)

def sumOutsIf (p : TxOut → Bool) (cs : CurrencySymbol) (tn : TokenName) :
    List TxOut → Int
  | [] => 0
  | o :: rest => (if p o then valueOf cs tn o.txOutValue else 0) + sumOutsIf p cs tn rest

def sumInsIf (p : TxOut → Bool) (cs : CurrencySymbol) (tn : TokenName) :
    List TxInInfo → Int
  | [] => 0
  | t :: rest =>
      (if p t.txInInfoResolved then valueOf cs tn t.txInInfoResolved.txOutValue else 0)
      + sumInsIf p cs tn rest

/-- Amount of `(cs, tn)` at the transaction's mini-ledger OUTPUTS. -/
def outAtB (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Int :=
  sumOutsIf (atBaseB base) cs tn ctx.scriptContextTxInfo.txInfoOutputs

/-- Amount of `(cs, tn)` at the transaction's outputs OUTSIDE the mini-ledger —
the ESCAPE quantity. -/
def outOff (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Int :=
  sumOutsIf (offBaseB base) cs tn ctx.scriptContextTxInfo.txInfoOutputs

/-- Amount of `(cs, tn)` at the transaction's mini-ledger INPUTS. -/
def inAtB (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Int :=
  sumInsIf (atBaseB base) cs tn ctx.scriptContextTxInfo.txInfoInputs

/-- Amount of `(cs, tn)` at the transaction's inputs OUTSIDE the mini-ledger. -/
def inOff (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Int :=
  sumInsIf (offBaseB base) cs tn ctx.scriptContextTxInfo.txInfoInputs

/-- **`NE(tx, cs, tn)`** — the NON-ESCAPE obligation the whole branch analysis
reduces to: this transaction puts none of `(cs, tn)` outside the mini-ledger. -/
def NonEscape (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Prop :=
  outOff base cs tn ctx = 0

/-- **`CONTAIN(tx, cs, tn)`** — the per-slot containment inequality the leaves
actually produce. ARCHITECTURE.md §5.2 calls it `B_out(cs) ≥ B_in(cs) + mint(cs)`.

SIGNED, not `mintPos` — the correction recorded in `WSC/Props/P1_Transfer.lean`'s
`P1_model` docstring: §3-P1's `mintPos` form is REFUTED for burns (with
`inSum = 5`, `mintOf = -3` the validator's expected value is `2 < 5`), and the
SIGNED form is both the true one and the one this reduction consumes. -/
def Contain (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Prop :=
  outAtB base cs tn ctx ≥ inAtB base cs tn ctx + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-! # §3 Proved arithmetic and `Value` facts

Everything in this section is an ordinary Lean proof — no `blaster`, no
`native_decide`, no axiom. -/

/-! ### Int helpers

`omega` does not fire on goals whose type is spelled `PlutusCore.Integer.Integer`
(the `abbrev` for `Int`), so the four arithmetic steps the reduction needs are
isolated here over plain `Int` variables and applied by name. This is a
tactic-plumbing detail, not a mathematical one. -/

theorem int_add_nonneg' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by omega
theorem int_add_zero' {a b : Int} (ha : a = 0) (hb : b = 0) : a + b = 0 := by omega
theorem int_split_zero {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 ∧ b = 0 := by omega

/-- The escape quantity vanishes: conservation + containment + non-negativity. -/
theorem int_escape_zero {iA iO m oA oO : Int}
    (hbal : iA + iO + m = oA + oO) (hin : iO = 0) (hcon : oA ≥ iA + m) (hge : 0 ≤ oO) :
    oO = 0 := by omega

/-- Branch A of the case analysis: nothing came from the mini-ledger and nothing
was minted, so containment is free. -/
theorem int_contain_trivial {iA m oA : Int} (hi : iA = 0) (hm : m ≤ 0) (ho : 0 ≤ oA) :
    oA ≥ iA + m := by omega

/-- The Preservation step: `0 - 0 + 0 = 0`. -/
theorem int_step_zero {x y i o : Int} (h : x = y - i + o) (hy : y = 0) (hi : i = 0)
    (ho : o = 0) : x = 0 := by omega

/-! ### `Value`-level facts -/

/-- A `Value` that does not carry the policy `cs` holds none of any `(cs, tn)`.
Follows `valueOf`'s own recursion (`CardanoLedgerApi/V1/Value.lean:85-103`);
note the non-`Map` head case, where `valueOf` returns 0 without recursing. -/
theorem valueOf_zero_of_not_hasCS (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (v : Value), hasCurrencySymbol cs v = false → valueOf cs tn v = (0:Int) := by
  intro v
  induction v with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro h
      simp only [hasCurrencySymbol, Bool.or_eq_false_iff] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨a, b⟩ := p
      cases b with
      | Map m =>
          show valueOf.visit cs tn _ = 0
          simp only [valueOf.visit, h1]
          exact ih h2
      | _ => rfl

/-- Contrapositive: a non-zero holding of `(cs, tn)` means the policy is present.
This is what upgrades "the slot is minted" to `WSC.LR_MINT_RUNS_POLICY`'s
`hasCurrencySymbol cs txInfoMint` trigger. -/
theorem hasCS_of_valueOf_ne_zero (cs : CurrencySymbol) (tn : TokenName) (v : Value)
    (h : valueOf cs tn v ≠ (0:Int)) : hasCurrencySymbol cs v = true := by
  by_cases hb : hasCurrencySymbol cs v = true
  · exact hb
  · exact absurd (valueOf_zero_of_not_hasCS cs tn v (by simpa using hb)) h

/-- Token-map level: if no token name under the policy has a strictly positive
quantity then the lookup of any one of them is `≤ 0`. Mirrors `WSC.anyPosTokens`
(`WSC/Spec.lean:50-53`) against `valueOf`'s inner `find_token`. -/
theorem findToken_nonpos (tn : TokenName) :
    ∀ (tns : List (Data × Data)), WSC.anyPosTokens tns = false →
      valueOf.find_token tn tns ≤ (0:Int) := by
  intro tns
  induction tns with
  | nil => intro _; exact Int.le_refl 0
  | cons p rest ih =>
      intro h
      obtain ⟨a, b⟩ := p
      show valueOf.find_token tn (_ :: _) ≤ 0
      by_cases hx : Data.B tn = a
      · cases b with
        | I n =>
            simp only [WSC.anyPosTokens, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
            simp only [valueOf.find_token, if_pos hx]
            obtain ⟨h1, h2⟩ := h
            exact Int.not_lt.mp h1
        | _ => simp only [valueOf.find_token, if_pos hx]; exact Int.le_refl 0
      · simp only [valueOf.find_token, if_neg hx]
        cases b with
        | I n =>
            simp only [WSC.anyPosTokens, Bool.or_eq_false_iff] at h
            exact ih h.2
        | _ => simp only [WSC.anyPosTokens] at h; exact ih h

/-- **The `BurnOnly` bridge.** A transaction whose mint field has no strictly
positive quantity under `cs` mints a non-positive amount of every slot of `cs`.
This is what turns P4's arm-4 conclusion (`WSC.BurnOnlyOk`, proved at UPLC over
SHAPE M1/M2) into the arithmetic fact the branch analysis needs. -/
theorem mintOf_nonpos_of_not_mintPos (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (mint : MintValue), WSC.mintPos cs mint = false →
      WSC.mintOf cs tn mint ≤ (0:Int) := by
  intro mint
  induction mint with
  | nil => intro _; exact Int.le_refl 0
  | cons p rest ih =>
      intro h
      obtain ⟨a, b⟩ := p
      show valueOf.visit cs tn (_ :: _) ≤ 0
      cases b with
      | Map m =>
          simp only [valueOf.visit]
          by_cases hc : ((Data.B cs : Data) == a) = true
          · rw [if_pos hc]
            have ha : a = Data.B cs :=
              ((beq_iff_eq (a := (Data.B cs : Data)) (b := a)).mp hc).symm
            subst ha
            simp only [WSC.mintPos, beq_self_eq_true, if_pos] at h
            exact findToken_nonpos tn m h
          · rw [if_neg hc]
            refine ih ?_
            cases a with
            | B cs' =>
                simp only [WSC.mintPos] at h
                have hne : ¬ ((cs' == cs) = true) := by
                  intro hb
                  exact hc (by simp [(beq_iff_eq (a := cs') (b := cs)).mp hb])
                rw [if_neg hne] at h
                exact h
            | _ => simpa only [WSC.mintPos] using h
      | _ => exact Int.le_refl 0

/-! ### Sum facts -/

theorem sumOutsIf_nonneg (p : TxOut → Bool) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (os : List TxOut), (∀ o ∈ os, (0:Int) ≤ valueOf cs tn o.txOutValue) →
      0 ≤ sumOutsIf p cs tn os := by
  intro os
  induction os with
  | nil => intro _; exact Int.le_refl 0
  | cons o rest ih =>
      intro h
      have h1 : (0:Int) ≤ (if p o then valueOf cs tn o.txOutValue else 0) := by
        by_cases hp : p o = true
        · rw [if_pos hp]; exact h o (List.mem_cons_self ..)
        · rw [if_neg (by simpa using hp)]; exact Int.le_refl 0
      have h2 := ih (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
      exact int_add_nonneg' h1 h2

theorem sumInsIf_eq_zero (p : TxOut → Bool) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (ts : List TxInInfo),
      (∀ t ∈ ts, p t.txInInfoResolved = true →
        valueOf cs tn t.txInInfoResolved.txOutValue = (0:Int)) →
      sumInsIf p cs tn ts = 0 := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t rest ih =>
      intro h
      have h1 : (if p t.txInInfoResolved then valueOf cs tn t.txInInfoResolved.txOutValue else 0)
          = (0:Int) := by
        by_cases hp : p t.txInInfoResolved = true
        · rw [if_pos hp]; exact h t (List.mem_cons_self ..) hp
        · rw [if_neg (by simpa using hp)]
      have h2 := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
      exact int_add_zero' h1 h2

theorem sumHoldU_nonneg (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (L : Ledger), (∀ u ∈ L, (0:Int) ≤ valueOf cs tn u.utxoOut.txOutValue) →
      0 ≤ sumHoldU cs tn L := by
  intro L
  induction L with
  | nil => intro _; exact Int.le_refl 0
  | cons v rest ih =>
      intro hnn
      exact int_add_nonneg' (hnn v (List.mem_cons_self ..))
        (ih (fun x hx => hnn x (List.mem_cons_of_mem _ hx)))

/-- A sum of non-negative holdings that vanishes has every term zero — the step
that turns `I L` into "no out-of-base UTxO of `L` holds `cs`". -/
theorem sumHoldU_elim (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (L : Ledger), (∀ u ∈ L, (0:Int) ≤ valueOf cs tn u.utxoOut.txOutValue) →
      sumHoldU cs tn L = 0 → ∀ u ∈ L, valueOf cs tn u.utxoOut.txOutValue = (0:Int) := by
  intro L
  induction L with
  | nil => intro _ _ u hu; exact absurd hu (by simp)
  | cons v rest ih =>
      intro hnn hz u hu
      have hv : (0:Int) ≤ valueOf cs tn v.utxoOut.txOutValue := hnn v (List.mem_cons_self ..)
      have hr : (0:Int) ≤ sumHoldU cs tn rest :=
        sumHoldU_nonneg cs tn rest (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
      obtain ⟨hv0, hr0⟩ := int_split_zero hv hr hz
      rcases List.mem_cons.mp hu with h | h
      · exact h ▸ hv0
      · exact ih (fun x hx => hnn x (List.mem_cons_of_mem _ hx)) hr0 u h

/-- **The `Local` arm bridge.** The issuance policy's own no-escape scan
(`WSC.noEscape`, the ground-truth counterpart of `Issuance.hs:183-193`) implies the
NON-ESCAPE obligation outright, with no appeal to conservation. -/
theorem nonEscape_of_noEscape (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (os : List TxOut), WSC.noEscape base cs os = true →
      sumOutsIf (offBaseB base) cs tn os = (0:Int) := by
  intro os
  induction os with
  | nil => intro _; rfl
  | cons o rest ih =>
      intro h
      simp only [WSC.noEscape, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hhd : (if offBaseB base o then valueOf cs tn o.txOutValue else 0) = (0:Int) := by
        rcases h1 with hb | hnc
        · rw [if_neg (by simp [offBaseB, hb])]
        · have hz : hasCurrencySymbol cs o.txOutValue = false := by simpa using hnc
          by_cases hp : offBaseB base o = true
          · rw [if_pos hp]; exact valueOf_zero_of_not_hasCS cs tn _ hz
          · rw [if_neg (by simpa using hp)]
      exact int_add_zero' hhd (ih h2)

/-! ### §3.5 `LR_BALANCE_SLOT` — the `Value`-algebra residue, isolated (task U2)

§9.5 recorded `LR_BALANCE_SLOT` as an axiom that "should be a theorem": the
per-slot projection of `WSC.LR7` (`isBalanced`,
`CardanoLedgerApi/V3/Contexts.lean:1185-1189`). This section does as much of that
derivation as CLAB supports, and isolates the rest into THREE named `Value`-level
facts (`ValueAlgebra`) that mention no ledger notion at all.

WHAT `isBalanced` GIVES (`:1188-1189`), for `sv = valueSpent ctx`,
`pv = valueProduced ctx`:

    lovelaceOf sv = lovelaceOf pv + txInfoFee   ∧
    merge (withoutLovelace sv) txInfoMint == withoutLovelace pv

The `cs ≠ adaSymbol` side condition of `LR_BALANCE_SLOT` is what lets the first
conjunct (and hence the fee) be dropped entirely; §3.5's job is to turn the second
into the per-slot equation.

WHY THIS IS NOT MECHANICAL, and the FINDING that makes the canonicity hypothesis
mandatory: **`valueOf` is NOT additive over `merge` in general.** `merge`'s
`cs_visit` (`CardanoLedgerApi/V1/Value.lean:151-164`) is a SORTED merge — it
compares heads with `cs < cs'` and its own comment says "assume `Value` is
well-formed". On unsorted input it duplicates keys and `valueOf`, which returns at
the FIRST matching key (`:95-103`), then loses the later copy.
`merge_not_additive_without_canonicity` below is that counterexample,
machine-checked. So any derivation must carry a canonicity predicate, and the
predicate must be preserved by `merge` (because `valueSpent` folds `merge` over
every input). `CanonV` is that predicate.

WHAT CLAB SUPPLIES TOWARDS THIS: **nothing.** There is no lemma anywhere in
`CardanoLedgerApi/` relating `valueOf` to `merge`, `withoutLovelace`,
`valueSpent` or `valueProduced` (grep for `valueOf.*merge`: the only hit is
§9.5's own note). The analogous development DOES exist one layer down, for
PlutusCoreBlaster's CIP-153 `ValueRep`: `PlutusCore/Value/Algebra.lean`'s
`unionInner_lookup` (:561-660), `unionOuter_lookup` (:809-910),
`unionInner_sortedFrom` (:493-561), `unionOuter_sortedFrom` (:746-809) — ~330
lines, and they are the template for the CLAB versions. They are NOT reusable
directly: `merge`/`valueOf` on `List (Data × Data)` and `unionOuter`/`lookupCoin`
on `ValueRep` are different functions, and bridging them is a proof of the same
size.

STATUS, stated exactly: `LR_BALANCE_SLOT` remains an axiom, but it is NO LONGER
OPAQUE — `LR_BALANCE_SLOT_of_valueAlgebra` (§4) proves it from `ValueAlgebra` plus
`WSC.LR7`, with NO new ledger assumption and no appeal to anything outside
`CardanoLedgerApi`. Instantiating `ValueAlgebra` deletes the axiom; the work is
the ~330-line CLAB `Value`-algebra port described above. -/

/-- The `Data`-level key of an assoc-list entry, when the key is a `Data.B`. -/
def bKeyOf : Data × Data → Option ByteString
  | (Data.B b, _) => some b
  | _ => none

/-- **Canonical token map**: every entry is `(Data.B tn, Data.I n)` and the token
names strictly ascend. This is the shape `merge.tn_visit` and
`valueOf.find_token` both assume. Implied by `validTxOutValue`'s `validTokens`
(`CardanoLedgerApi/V1/Contexts.lean:788-792`) and by `validMintValue`'s
`validMintTokens` (`:824-828`); NOTE that neither the positivity of
`validTxOutValue` nor the non-zeroness of `validMintValue` is needed for
additivity, which is why this predicate says nothing about quantities. -/
def CanonToks : List (Data × Data) → Prop
  | [] => True
  | (Data.B tn, Data.I _) :: rest =>
      (∀ q ∈ rest, ∀ tn', bKeyOf q = some tn' → tn < tn') ∧ CanonToks rest
  | _ => False

/-- **Canonical `Value`**: every entry is `(Data.B cs, Data.Map toks)` with `toks`
canonical, and the policy ids strictly ascend. Implied by `validTxOutValue` and by
`validMintValue`, and — crucially — expected to be PRESERVED by `merge`, which is
what makes the `valueSpent` fold well-behaved. -/
def CanonV : Value → Prop
  | [] => True
  | (Data.B cs, Data.Map toks) :: rest =>
      CanonToks toks ∧ (∀ q ∈ rest, ∀ cs', bKeyOf q = some cs' → cs < cs') ∧ CanonV rest
  | _ => False

/-- **FINDING (machine-checked): `valueOf` is NOT additive over `merge` without
canonicity.** Take `a = [(B "b", …1), (B "a", …1)]` — the SAME entries a canonical
value would have, in the wrong order — and `b = [(B "a", …1)]`. `merge a b`
emits `b`'s `"a"` entry first (because `"b" < "a"` is false and `"b" == "a"` is
false, so `cs_visit` takes the right head, `:161`) and then, with the right list
exhausted, appends `a` unchanged (`:153`). The result carries `"a"` TWICE and
`valueOf "a"` stops at the first copy, reporting 1 instead of 2.

So the `CanonV` hypotheses in `ValueAlgebra` are load-bearing, not defensive. -/
theorem merge_not_additive_without_canonicity :
    let a : Value := [ (Data.B (ByteString.mk "b"), Data.Map [(Data.B (ByteString.mk "t"), Data.I 1)])
                     , (Data.B (ByteString.mk "a"), Data.Map [(Data.B (ByteString.mk "t"), Data.I 1)]) ]
    let b : Value := [ (Data.B (ByteString.mk "a"), Data.Map [(Data.B (ByteString.mk "t"), Data.I 1)]) ]
    valueOf (ByteString.mk "a") (ByteString.mk "t") (merge a b)
      ≠ valueOf (ByteString.mk "a") (ByteString.mk "t") a
        + valueOf (ByteString.mk "a") (ByteString.mk "t") b := by
  native_decide

/-- **THE RESIDUE.** Three facts about CLAB's `Value` operations, each an instance
of "`valueOf` distributes over `merge` on `CanonV` values, and `merge` preserves
`CanonV`", specialized to the two folds `isBalanced` actually uses.

None of the three mentions a ledger rule, a validator, or `OnChain`: they are pure
statements about `CardanoLedgerApi/V1/Value.lean` and
`CardanoLedgerApi/V3/Contexts.lean:683-697`. Each carries the canonicity of the
per-`TxOut` values as an explicit hypothesis, which is exactly what `WSC.LR1`
(`validInputs`) and `WSC.LR2` (`validOutputs`) supply for a real transaction, and
`WSC.LR3` (`validMintValue`) supplies for the mint field.

UNPROVED. See §3.5's header for what the proof costs and why CLAB has none of it.
-/
structure ValueAlgebra : Prop where
  /-- `valueOf` of the merge-fold over inputs is the plain per-input sum. -/
  ofValueSpent : ∀ (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
      CanonV t.txInInfoResolved.txOutValue) →
      valueOf cs tn (valueSpent ctx)
        = sumInsIf (fun _ => true) cs tn ctx.scriptContextTxInfo.txInfoInputs
  /-- `valueOf` of the merge-fold over outputs is the plain per-output sum. -/
  ofValueProduced : ∀ (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, CanonV o.txOutValue) →
      valueOf cs tn (valueProduced ctx)
        = sumOutsIf (fun _ => true) cs tn ctx.scriptContextTxInfo.txInfoOutputs
  /-- `valueOf` distributes over the ONE `merge` that appears in `isBalanced`'s
  non-ada conjunct. The `CanonV` hypotheses are on the two arguments; canonicity of
  `withoutLovelace (valueSpent ctx)` is itself a consequence of `merge` preserving
  `CanonV`, which is why this field is stated at the point of use rather than as a
  general distributivity law. -/
  ofMergeMint : ∀ (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
      CanonV t.txInInfoResolved.txOutValue) →
    CanonV ctx.scriptContextTxInfo.txInfoMint →
      valueOf cs tn (merge (withoutLovelace (valueSpent ctx))
          ctx.scriptContextTxInfo.txInfoMint)
        = valueOf cs tn (withoutLovelace (valueSpent ctx))
          + valueOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-! ### §3.5b The parts of the derivation that ARE proved here -/

/-- **`withoutLovelace` is invisible to a non-ada slot** — PROVED, and
UNCONDITIONALLY (no canonicity needed). `withoutLovelace`
(`CardanoLedgerApi/V1/Value.lean:77-80`) either drops a leading ada entry, which
`valueOf cs` skips anyway for `cs ≠ ""`, or is the identity. -/
theorem valueOf_withoutLovelace (cs : CurrencySymbol) (tn : TokenName) (v : Value)
    (hcs : cs ≠ adaSymbol) :
    valueOf cs tn (withoutLovelace v) = valueOf cs tn v := by
  unfold CardanoLedgerApi.V1.Value.withoutLovelace
  split
  · next n rest =>
      show valueOf cs tn rest = valueOf.visit cs tn (_ :: rest)
      simp only [valueOf.visit]
      split
      · next hb => exact absurd (by simpa [adaSymbol] using hb) hcs
      · rfl
  · rfl

/-- The two per-slot input sums partition the inputs: base + off-base = total. -/
theorem sumInsIf_split (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (ts : List TxInInfo),
      sumInsIf (atBaseB base) cs tn ts + sumInsIf (offBaseB base) cs tn ts
        = sumInsIf (fun _ => true) cs tn ts := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      simp only [sumInsIf]
      by_cases hb : atBaseB base t.txInInfoResolved = true
      · rw [if_pos hb, if_neg (by simp [offBaseB, atBaseB] at hb ⊢; simpa using hb),
          if_pos (by simp)]
        omega
      · rw [if_neg (by simpa using hb), if_pos (by
            simp only [offBaseB, atBaseB] at hb ⊢; simpa using hb), if_pos (by simp)]
        omega

/-- The two per-slot output sums partition the outputs: base + off-base = total. -/
theorem sumOutsIf_split (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (os : List TxOut),
      sumOutsIf (atBaseB base) cs tn os + sumOutsIf (offBaseB base) cs tn os
        = sumOutsIf (fun _ => true) cs tn os := by
  intro os
  induction os with
  | nil => rfl
  | cons o rest ih =>
      simp only [sumOutsIf]
      by_cases hb : atBaseB base o = true
      · rw [if_pos hb, if_neg (by simp [offBaseB, atBaseB] at hb ⊢; simpa using hb),
          if_pos (by simp)]
        omega
      · rw [if_neg (by simpa using hb), if_pos (by
            simp only [offBaseB, atBaseB] at hb ⊢; simpa using hb), if_pos (by simp)]
        omega

/-- **The `Value` EQUALITY inside `isBalanced`**, extracted from its `==`.
`Value = List (Data × Data)` has a `LawfulBEq` instance
(`CardanoLedgerApi/V1/Value.lean:26-32`), so the `BEq` in `isBalanced`'s second
conjunct is genuine equality — this is the step that lets `valueOf` be applied to
both sides. -/
theorem isBalanced_nonAda_eq (ctx : ScriptContext) (h : isBalanced ctx = true) :
    merge (withoutLovelace (valueSpent ctx)) ctx.scriptContextTxInfo.txInfoMint
      = withoutLovelace (valueProduced ctx) := by
  simp only [CardanoLedgerApi.V3.Contexts.isBalanced, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-! # §4 The ledger-level axioms

`WSC/Honest.lean` deliberately does NOT state these: they need a `Ledger` type,
and inventing them there would have been a wrong axiom (see its numbering table,
rows `ts_genesis` and `lr_utxo_semantics`). Each one below is stated in the
weakest form the reduction consumes, with its ledger rule or its discharge. -/

/-- The abstract per-transaction ledger transition relation: `L'` is the UTxO set
after applying the transaction whose script-context view is `ctx` to `L`.

DECLARED, NOT DEFINED, and deliberately: defining it would mean building a
Cardano ledger in Lean. Everything the reduction needs about it is stated as one
of the four axioms below, so the trust surface is exactly those four. -/
axiom LedgerStep : Ledger → ScriptContext → Ledger → Prop

/-- **§5.3 `lr_utxo_semantics`, arithmetic form.** `L' = (L \ tx.inputs) ∪
tx.outputs`, projected onto the only quantity the reduction reads: the
out-of-base total of one asset slot changes by exactly minus the out-of-base
inputs plus the out-of-base outputs.

WHY UNAVOIDABLE / LEDGER RULE: it IS the Conway UTXO state-transition rule.
WHY THIS FORM: the set-theoretic form would additionally require modelling
double-spend prevention and reference uniqueness, neither of which the reduction
uses. -/
axiom lr_utxo_semantics :
  ∀ (L : Ledger) (ctx : ScriptContext) (L' : Ledger),
    LedgerStep L ctx L' →
    ∀ (base : Credential) (cs : CurrencySymbol) (tn : TokenName),
      OutOfBase base cs tn L' =
        OutOfBase base cs tn L - inOff base cs tn ctx + outOff base cs tn ctx

/-- **§5.3 `lr_utxo_semantics`, membership half.** Every input a transaction
spends was in the pre-state UTxO set. (Reference inputs too: the ledger resolves
them against the same UTxO set.)

WHY IT MATTERS: it is what lets `I L` — a fact about `L` — constrain the
transaction's out-of-base inputs, and what puts the tx's covering directory node
inside the ledger snapshot `DIRWF_L` talks about. -/
axiom lr_inputs_in_ledger :
  ∀ (L : Ledger) (ctx : ScriptContext) (L' : Ledger),
    LedgerStep L ctx L' →
    (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
       UTxO.mk t.txInInfoOutRef t.txInInfoResolved ∈ L) ∧
    (∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
       UTxO.mk t.txInInfoOutRef t.txInInfoResolved ∈ L)

/-- **Where a NEW registration can come from.** If `cs` is registered after the
step, then either it already was, or one of THIS transaction's outputs is the
authentic node keyed `cs`.

WHY UNAVOIDABLE / LEDGER RULE: `L' ⊆ (L \ inputs) ∪ outputs`, so any UTxO of `L'`
is a surviving UTxO of `L` or a produced output. This is the half of UTxO
semantics that makes the quantifier over the GROWING registry `R(L)` sound
(ARCHITECTURE.md §5.1 `L-monotone`). -/
axiom lr_registration_source :
  ∀ (hp : WSC.HonestParams) (L : Ledger) (ctx : ScriptContext) (L' : Ledger)
    (cs : CurrencySymbol),
    LedgerStep L ctx L' →
    RegisteredIn hp L' cs →
      RegisteredIn hp L cs ∨
      WSC.registeredIn hp.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoOutputs

/-- **§5.3 `lr_value_conservation`, per-slot form** (ADDENDUM E6's companion).
For a non-ada asset slot, value in = value out: base inputs + off-base inputs +
mint = base outputs + off-base outputs. The fee term is absent precisely because
`cs ≠ adaSymbol`.

STATUS, honestly (REVISED BY TASK U2): this is the per-slot PROJECTION of
`WSC/Honest.lean`'s `LR7` (`isBalanced ctx`,
`CardanoLedgerApi/V3/Contexts.lean:1185-1189`, whose non-ada conjunct is
`merge (withoutLovelace (valueSpent ctx)) txInfoMint == withoutLovelace
(valueProduced ctx)`). It is STILL an axiom, but it is no longer opaque:
`LR_BALANCE_SLOT_of_valueAlgebra` below PROVES this exact statement from `LR7`
plus two named, purely-`CardanoLedgerApi` residues — `ValueAlgebra` (three
`valueOf`/`merge` facts) and `LedgerCanon` (canonicity of the values a real
transaction shows) — with NO new ledger assumption. Read §3.5's header for why the
`Value` algebra is not one-line mechanical (`valueOf` is NOT additive over `merge`
without sortedness — `merge_not_additive_without_canonicity` is the
machine-checked counterexample) and for the measured size of the port.

DELETE THIS AXIOM when `ValueAlgebra` and `LedgerCanon` are instantiated: the
replacement is `LR_BALANCE_SLOT_of_valueAlgebra va lc`. -/
axiom LR_BALANCE_SLOT :
  ∀ (ctx : ScriptContext) (base : Credential) (cs : CurrencySymbol) (tn : TokenName),
    WSC.OnChain ctx → cs ≠ adaSymbol →
      inAtB base cs tn ctx + inOff base cs tn ctx
        + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint
      = outAtB base cs tn ctx + outOff base cs tn ctx

/-- **The LEDGER-side residue of `LR_BALANCE_SLOT`**: every `Value` a real
transaction shows is `CanonV`.

This is NOT a new ledger assumption — it is the projection of `WSC.LR1`
(`validInputs`, hence `validTxOutValue` on every resolved input), `WSC.LR2`
(`validOutputs`) and `WSC.LR3` (`validMintValue`) through the two CLAB validity
predicates, whose sortedness clauses are literally `prev_cs < cs` /
`prev_tn < tn` (`CardanoLedgerApi/V1/Contexts.lean:787-802, 823-838`). Reading
`CanonV` off them is mechanical unfolding of two nested `let rec`s with an
accumulator — no algebra — and it is UNWRITTEN. It is kept separate from
`ValueAlgebra` precisely so the two kinds of missing work are not conflated. -/
def LedgerCanon : Prop :=
  ∀ (ctx : ScriptContext), WSC.OnChain ctx →
    (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
      CanonV t.txInInfoResolved.txOutValue) ∧
    (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, CanonV o.txOutValue) ∧
    CanonV ctx.scriptContextTxInfo.txInfoMint

/-- **`LR_BALANCE_SLOT`, PROVED from `WSC.LR7` + `ValueAlgebra` + `LedgerCanon`
(task U2).** This is the derivation §9.5 asked for, complete except for the two
residues, which are stated in §3.5/above and contain no ledger content.

THE DERIVATION, in full:
1. `sumInsIf_split` / `sumOutsIf_split` (§3.5b, PROVED): the base and off-base
   per-slot sums partition the inputs and the outputs, so the goal reduces to
   `totalIn + mint = totalOut`;
2. `WSC.LR7` + `isBalanced_nonAda_eq` (§3.5b, PROVED, via `LawfulBEq Value`):
   `merge (withoutLovelace (valueSpent ctx)) txInfoMint = withoutLovelace
   (valueProduced ctx)` — a genuine `Value` equality, so `valueOf cs tn` can be
   applied to both sides;
3. `ValueAlgebra.ofMergeMint` on the left, then `valueOf_withoutLovelace`
   (§3.5b, PROVED, unconditional for `cs ≠ adaSymbol`) on both sides — this is
   where the FEE disappears, because the fee lives only in `isBalanced`'s ada
   conjunct;
4. `ValueAlgebra.ofValueSpent` / `ofValueProduced` turn the two folds into the
   per-input and per-output sums;
5. `WSC.mintOf` is `valueOf` (`WSC/Spec.lean:45-46`), so step 3's mint term is
   already the goal's. -/
theorem LR_BALANCE_SLOT_of_valueAlgebra (va : ValueAlgebra) (lc : LedgerCanon) :
    ∀ (ctx : ScriptContext) (base : Credential) (cs : CurrencySymbol) (tn : TokenName),
      WSC.OnChain ctx → cs ≠ adaSymbol →
        inAtB base cs tn ctx + inOff base cs tn ctx
          + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint
        = outAtB base cs tn ctx + outOff base cs tn ctx := by
  intro ctx base cs tn hoc hcs
  obtain ⟨hcIn, hcOut, hcMint⟩ := lc ctx hoc
  -- step 2
  have hbal := isBalanced_nonAda_eq ctx (WSC.LR7 ctx hoc)
  have hv : valueOf cs tn (merge (withoutLovelace (valueSpent ctx))
      ctx.scriptContextTxInfo.txInfoMint)
      = valueOf cs tn (withoutLovelace (valueProduced ctx)) := by rw [hbal]
  -- step 3
  rw [va.ofMergeMint ctx cs tn hcIn hcMint, valueOf_withoutLovelace cs tn _ hcs,
    valueOf_withoutLovelace cs tn _ hcs] at hv
  -- step 4
  rw [va.ofValueSpent ctx cs tn hcIn, va.ofValueProduced ctx cs tn hcOut] at hv
  -- steps 1 + 5
  have hin := sumInsIf_split base cs tn ctx.scriptContextTxInfo.txInfoInputs
  have hout := sumOutsIf_split base cs tn ctx.scriptContextTxInfo.txInfoOutputs
  have hgoal : sumInsIf (atBaseB base) cs tn ctx.scriptContextTxInfo.txInfoInputs
        + sumInsIf (offBaseB base) cs tn ctx.scriptContextTxInfo.txInfoInputs
        + valueOf cs tn ctx.scriptContextTxInfo.txInfoMint
      = sumOutsIf (atBaseB base) cs tn ctx.scriptContextTxInfo.txInfoOutputs
        + sumOutsIf (offBaseB base) cs tn ctx.scriptContextTxInfo.txInfoOutputs := by
    rw [hin, hout]; exact hv
  simpa only [inAtB, inOff, outAtB, outOff, WSC.mintOf] using hgoal

/-- **§5.3 `ts_genesis`.** The deployment's initial ledger state satisfies the
invariant: the directory holds only sentinels, no live-`cs` node exists, and
nothing is held outside the mini-ledger.

WHY UNAVOIDABLE: it is the induction's base case and a fact about the deployment
transaction, not about any validator.
AUDIT / DISCHARGE: inspect the genesis transaction of the audited deployment. -/
axiom Genesis : WSC.HonestParams → Ledger → Prop

/-- **§5.3 `ts_minting_identity`, LEDGER form.** Every registered programmable
policy id is the script hash of a `mkProgrammableLogicMinting` instance
parameterized by the deployed `protocolParamsCS`.

WHY IT IS NEEDED IN ADDITION TO `WSC.TS_MINTING_IDENTITY`: the latter is
conditioned on `IsRegistered` over ONE transaction's reference inputs, i.e. on the
policy's node being visible to that transaction. The composition needs it for a
policy registered in the LEDGER, whose node the transaction need not reference at
all. Same fact, same discharge (deployment audit / U10), stated where it bites. -/
axiom ts_minting_identity_L :
  ∀ (hp : WSC.HonestParams) (L : Ledger) (cs : CurrencySymbol),
    WSC.Deployed hp → RegisteredIn hp L cs →
      ∃ mlh : ScriptHash, cs = WSC.mlhPolicyId hp.protocolParamsCS mlh

/-! ### NOT stated here as an axiom: the seize halting bridge

The seize leaf (§6 `LeafSet.p2`) is triggered by `WSC.NodeAcceptsSeize` — real node
acceptance — and NOT by any prepped term, because there is no published `K_seize`
and every affordable prep budget is MEASURED vacuous (`WSC/Honest.lean`, "K_seize —
DELIBERATELY UNAVAILABLE"), which makes `WSC.LR_BUDGET_seize` unusable by
construction. Discharging `LeafSet.p2` from `WSC.P2.P2a_bytecode` /
`WSC.P2.P2b_bytecode` therefore additionally requires

    LR_SEIZE_HALTS : NodeAcceptsSeize pcs ctx → SeizeModel.seizeAcceptsUnbounded pcs ctx

("the node ran the same CEK machine to a terminal state, so some finite step count
suffices"). It is deliberately NOT introduced here: it would be an axiom nothing in
this file can use, and it is recorded in §9.3 as part of the cost of that
discharge instead. Its justification is the same `runSteps` monotonicity
meta-theorem the whole `LR_BUDGET_*` family needs. -/

/-! # §5 The transaction class (ADDENDUM E1)

E1 is binding: the invariant, Preservation and the top claim are scoped to the
bounded-transaction class, and the top theorem's docstring must say so. -/

/-- Two contexts are views of the SAME transaction. ARCHITECTURE.md Tier 5.1: the
composition instantiates every per-validator theorem at ONE shared `TxInfo`, never
at independently quantified contexts. `WSC.withPurpose` is the constructor that
respects this by definition. -/
def SameTx (ctx ctx' : ScriptContext) : Prop :=
  ctx'.scriptContextTxInfo = ctx.scriptContextTxInfo

theorem sameTx_withPurpose (ctx : ScriptContext) (r : Data) (si : ScriptInfo) :
    SameTx ctx (WSC.withPurpose ctx r si) := rfl

/-- **`WithinBudget` (ADDENDUM E1).** Every validator run this transaction can
trigger halts within the PUBLISHED per-validator CEK step bound of
`WSC/Honest.lean` (`K_base = 600`, `K_mint = 900`, `K_global = 4400`), whichever
purpose it is invoked under.

TASK U2 NOTE — the global clause was WIDENED. It used to read
`nodeStepsGlobal … ≤ 1600`, which EXCLUDED every transaction the P1 containment
theorems talk about (their witnesses cost 2,603 / 3,150 / 3,572 CEK steps, and the
containment-carrying off-chain goldens 3,262 / 3,726). Widening it weakens a
HYPOTHESIS, so `preservation` and `top_claim` got strictly stronger; nothing in
§7 consumes the global clause (only the base clause, in `p3_lifted`).
The minting clause is still `K_mint = 900` and is still TOO TIGHT for P4's
`Local`/`DelegateTransfer`/`DelegateSeize` arms (K = 1,681 / 1,257 / 1,466) —
§10.5.

THERE IS NO SEIZE CLAUSE, deliberately: no `K_seize` exists (see
`LR_SEIZE_HALTS`). -/
def WithinBudget (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  (∀ ctx', SameTx ctx ctx' →
     WSC.nodeStepsBase hp.globalLogicCred hp.seizeLogicCred ctx' ≤ WSC.K_base) ∧
  (∀ (mlh : ScriptHash) (ctx' : ScriptContext), SameTx ctx ctx' →
     WSC.nodeStepsMinting hp.protocolParamsCS mlh ctx' ≤ WSC.K_mint) ∧
  (∀ ctx', SameTx ctx ctx' →
     WSC.nodeStepsGlobal hp.protocolParamsCS ctx' ≤ WSC.K_global)

/-- **The honest, in-scope transaction class (ADDENDUM E1).** `Shape` is a
PARAMETER, not a definition: instantiate it with `fun _ => True` for the
unrestricted class, or with "`ctx` is an instance of SHAPE M1 / M2 / G1" when a
leaf is discharged by a shaped `by blaster` theorem (task Z2). A shaped leaf can
NEVER discharge a hypothesis at `Shape := fun _ => True`. -/
def HonestTx (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (ctx : ScriptContext) : Prop :=
  WSC.OnChain ctx ∧ WithinBudget hp ctx ∧ Shape ctx

/-! # §6 The leaves, as explicit hypotheses

Each field of `LeafSet` is the WEAKEST consequence of a leaf property that §7
consumes, stated in this file's ground-truth vocabulary. Every field's docstring
names the library artifact that would discharge it and at what strength; §9 is the
audited table.

The trigger of each leaf is `NodeAccepts*` — real node acceptance — NOT
`isSuccessful (applied*.prop …)`. That boundary is deliberate and is where the
library's budget bridges stop being usable:

* for the BASE validator the bridge works today, so §7 does that plumbing itself
  (`p3_lifted`) and P3 is NOT a `LeafSet` field;
* for MINTING the bridge NOW EXISTS at `K_mint = 900`: task U2 repointed
  `WSC.LR_BUDGET_minting` from the budget-600 `appliedMinting.prop` (machine-checked
  vacuous, `WSC.minting600_is_vacuous`) to `appliedMinting900.prop`, and DISCHARGED
  its non-vacuity hypothesis (`mintingNonVacuous`, §7). It still does not reach
  P4's three non-burn arms, which need a bridge at the 2500 prep (§10.5);
* for GLOBAL, task U2 made `WSC.LR_BUDGET_global` PREP-PARAMETRIC (it now carries
  the prepped term and its budget as arguments plus a `GlobalPreppedAt` side
  condition), which removes the old defect — it used to name the budget-600
  `appliedGlobal.prop` while quoting `K_global`. It is still not INSTANTIABLE at
  the shaped preps without the SHAPE BRIDGE (§9.4), so §7 still does no global
  budget plumbing;
* for SEIZE there is no bridge at all, only `LR_SEIZE_HALTS`.

Putting the trigger at `NodeAccepts*` therefore keeps §7's proof honest: it
consumes no bridge that does not exist. -/

/-- The four leaf hypotheses the branch analysis consumes. -/
structure LeafSet (hp : WSC.HonestParams) (Shape : ScriptContext → Prop) : Prop where
  /-- **LEAF-P4 (entrance).** *An accepted mint of policy `cs` satisfies one of
  the four custody arms* — reduced to the one conjunct of each arm the reduction
  uses: `Local` ⟹ its own no-escape scan, `DelegateTransfer` ⟹ the global
  credential is in `wdrl`, `DelegateSeize` ⟹ the seize credential is in `wdrl`,
  `BurnOnly` ⟹ nothing positive is minted under `cs`.

  DISCHARGED BY: `WSC.P4_mint_routes_or_burns` (`Prop`, STILL-OPEN over a fully
  symbolic context: `Undetermined` after 3,208 s) — arm 4 only is PROVED-SHAPED
  (`WSC.P4_burnonly_arm_shaped`, `WSC.P4_burn_only_shapedIdx`) — plus the minting
  budget bridge. Arms 1-3 need K ≥ 1,257/1,681 and no shape has been written.

  NOTE on the `DelegateSeize` arm: `WSC/Spec.lean`'s `DelegateSeizeOk` concludes
  `seizeScopedToNodeOf`, which exhibits a `Rewarding seizeCred` entry in the
  REDEEMER MAP; upgrading that to "`seizeCred ∈ txInfoWdrl`" is `WSC.LR5`'s
  rewarding clause (`validScriptInfo`) and is folded into this hypothesis. -/
  p4 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (mlh : ScriptHash),
    WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → SameTx ctx ctx' →
    ctx'.scriptContextScriptInfo = ScriptInfo.MintingScript cs →
    WSC.NodeAcceptsMinting hp.protocolParamsCS mlh ctx' →
      WSC.noEscape hp.progLogicCred cs ctx.scriptContextTxInfo.txInfoOutputs = true
      ∨ credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
      ∨ credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
      ∨ WSC.mintPos cs ctx.scriptContextTxInfo.txInfoMint = false

  /-- **LEAF-P1 (exit via the global transfer validator), with P6 folded in.**
  *If the global validator accepts and `cs` cannot be exempted, then `cs` is
  contained.* The exemption hypothesis is `¬ coveringIn` — the GROUND-TRUTH form
  of "no authentic directory node covers `cs`", which §7 discharges from
  "`cs` is registered" through the new bridge lemma.

  P6 needs no separate field: the SIGNED `Contain` already puts the positive mint
  on the requirement side (that IS Member self-penalization), and for burns the
  signed form is the one that is true (`WSC/Props/P1_Transfer.lean`, FINDING).

  DISCHARGED BY: `WSC.Model.P1_bytecode` — MODEL+AXIOM
  (`WSC.Model.globalModel_faithful`) and STILL-OPEN even there, since
  `WSC.Model.P1_model` is a `Prop` whose links L1.1a/b, L1.2-L1.6 are unproved.
  Vocabulary gap to close when it lands: `P1_model` states the exemption as
  `coveringNodeExists … = false` (raw `hasCSH` + 2-field `dirNodeFields`), this
  field states it as `¬ coveringIn` (ground-truth `authenticDirNode` + full
  5-field decode) — the same reconciliation `WSC.P5_groundtruth_of_indexed`
  performs for P5, which costs `WSC.TS3` + `WSC.TS5`. -/
  p1 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → SameTx ctx ctx' →
    ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.globalLogicCred →
    WSC.NodeAcceptsGlobal hp.protocolParamsCS ctx' →
    cs ≠ adaSymbol →
    ¬ WSC.coveringIn hp.directoryNodeCS cs (WSC.dirPreState ctx) →
      Contain hp.progLogicCred cs tn ctx

  /-- **LEAF-P2 (exit via the seize validator).** *If the seize validator accepts,
  every policy is contained* — the seized one because the clawed delta is driven
  back to the base credential, every other one because the mini-ledger inputs are
  paired with byte-identical continuing base outputs.

  DISCHARGED BY, in two halves and NEITHER complete:
  * seized policy: `WSC.P2.P2b_bytecode` — a `Prop`, STILL-OPEN
    (`P2b_seized_delta_contained` is blocked on the two bridges of that file's
    §5, with machine-checked counterexamples showing `ptokenPairsContain` is not
    pointwise sound without `validTxOutValue` canonicity);
  * non-seized policies: `WSC.P2.P2a_bytecode` is PROVED (MODEL+AXIOM,
    `WSC.SeizeModel.seizeModel_faithful`, 13/13 golden differential incl. the
    rejecting vector), but "structure preserved ⟹ `Contain` for a non-seized
    policy" is an UNWRITTEN lemma — `WSC.seizeStructurePreserved` pairs inputs
    with outputs up to `dropCS seizedCS`, and turning that pairing into the
    aggregate per-slot inequality is the missing step.

  It also inherits ARCHITECTURE.md's L2.5: P2 does NOT claim the directory node
  the seize redeemer points at is authentic. -/
  p2 : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → SameTx ctx ctx' →
    ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.seizeLogicCred →
    WSC.NodeAcceptsSeize hp.protocolParamsCS ctx' →
    cs ≠ adaSymbol →
      Contain hp.progLogicCred cs tn ctx

  /-- **LEAF-NOPRE (`L-mint-needs-reg`, ARCHITECTURE.md §5.1).** *A policy cannot
  hold tokens outside the mini-ledger before it is registered.* Needed because the
  invariant quantifies over the GROWING registry: a `cs` registered by THIS
  transaction was not covered by `I L`, so something must rule out tokens of `cs`
  that predate its registration.

  DISCHARGED BY: nothing yet — STILL-OPEN. The route is exactly §5.1's
  `L-mint-needs-reg`: before registration every positive-mint arm of the issuance
  policy fails (arms 1-3 all require a directory NFT registration proof) and arm 4
  forbids positive mint, so no token of `cs` can be created; combined with
  `ts_genesis` and induction over the trace, `OutOfBase L cs tn = 0` holds until
  registration. That argument needs the FULL P4 (arms 1-3 included), which is the
  weakest leaf in the set. -/
  nopre : ∀ (L : Ledger) (ctx : ScriptContext) (L' : Ledger) (cs : CurrencySymbol)
      (tn : TokenName),
    WSC.Deployed hp → LedgerStep L ctx L' → HonestTx hp Shape ctx →
    ¬ RegisteredIn hp L cs →
    WSC.registeredIn hp.directoryNodeCS cs ctx.scriptContextTxInfo.txInfoOutputs →
      OutOfBase hp.progLogicCred cs tn L = 0 ∧ NonEscape hp.progLogicCred cs tn ctx

/-! # §7 Preservation

The branch analysis of ARCHITECTURE.md §5.2, proved from `LeafSet` and the
axioms. Nothing in this section is `blaster`-closed or `native_decide`d. -/

/-- Non-vacuity of the base prep — DISCHARGED, as a theorem, from the in-library
concrete witness (`WSC/Props/P3_Base.lean`). This is what makes
`WSC.LR_BUDGET_base` usable below. -/
theorem baseNonVacuous : WSC.BaseNonVacuous :=
  ⟨WSC.P3Witness.globalCred, WSC.P3Witness.seizeCred, WSC.P3Witness.ctx,
   WSC.P3Witness.ctx_valid, WSC.P3Witness.prop_accepts⟩

/-- **Non-vacuity of the minting prep at `K_mint = 900` — DISCHARGED, as a
theorem (task U2).**

`WSC.MintingNonVacuous` used to name the budget-600 `appliedMinting.prop`, whose
negation is machine-checked (`WSC.minting600_is_vacuous`); task U2 repointed it at
`appliedMinting900.prop`, the prep every P4/P4a theorem lives on, and this is the
witness that discharges it:

* the context is `WSC.P4Witness.ctx` — a hand-built, fully concrete `BurnOnly`
  minting transaction (`WSC/Props/P4_Minting.lean:457-476`);
* `WSC.P4Witness.ctx_valid : validMintingContext ctx = true`, by `native_decide`;
* acceptance is on the OPTIMIZED `prop` term the theorems quantify over, closed by
  `blaster` on the fully concrete goal — exactly the route
  `WSC.P3Witness.prop_accepts` takes for the base validator, and NOT the weaker
  `exec` route (`#prep_uplc` emits `prop` and `exec` as two separate terms with no
  proved equality, `PlutusCore/UPLC/PreProcess.lean:43-46`).

Corroboration, all already in the library: the real bytecode REJECTS this context
at 600 and ACCEPTS it at 800 and 900 (`P4Witness.exec_rejects_at_600`,
`exec_accepts_at_800`, `exec_accepts_at_900`), and the REAL off-chain golden
`programmableTokenMinting.mint-burnonly` does the same with measured K = 784
(`WSC.P4Golden`).

MEASURED COST of the `blaster` call: 0.6 s (task U2). -/
theorem mintingNonVacuous : WSC.MintingNonVacuous :=
  ⟨WSC.P4Witness.protocolParamsCS, WSC.P4Witness.mintingLogicHash, WSC.P4Witness.ctx,
   WSC.P4Witness.ctx_valid, by blaster⟩

/-- A `withPurpose`-built spending context of an on-chain transaction satisfies
CLAB's `validSpendingContext`: the purpose matches by construction and
`WSC.LR_CTX` (ADDENDUM E5, whose audit table maps every conjunct to a cited
Cardano ledger rule) supplies `validScriptContext`. -/
theorem validSpendingContext_of_onChain (ctx : ScriptContext) (r : Data)
    (o : TxOutRef) (d : Option Data)
    (h : WSC.OnChain (WSC.withPurpose ctx r (.SpendingScript o d))) :
    validSpendingContext (WSC.withPurpose ctx r (.SpendingScript o d)) = true := by
  have := WSC.LR_CTX _ h
  simpa [validSpendingContext, WSC.withPurpose] using this

/-- **P3, LIFTED TO THE LEDGER (the keystone, plumbed).** *Spending a
mini-ledger UTxO forces the global or the seize validator to run on the same
transaction.*

This is the one leaf whose full chain is available today, so the composition does
the plumbing itself instead of assuming it:
`WSC.LR_SPEND_RUNS_VALIDATOR` (the ledger runs the base script) →
`WSC.LR_BUDGET_base` at `K_base = 600`, its non-vacuity hypothesis discharged by
`baseNonVacuous` → `WSC.LR_CTX` for the precondition →
`WSC.P3_base_requires_global_or_seize`, a `by blaster` theorem over the REAL
compiled `programmableLogicBase` bytecode with no shape restriction.

SCOPE: `WithinBudget`'s base clause (600 CEK steps) is where E1 bites. -/
theorem p3_lifted (hp : WSC.HonestParams) (ctx : ScriptContext) (t : TxInInfo)
    (hdep : WSC.Deployed hp) (hoc : WSC.OnChain ctx) (hb : WithinBudget hp ctx)
    (ht : t ∈ ctx.scriptContextTxInfo.txInfoInputs)
    (hpc : WSC.payCred t.txInInfoResolved = hp.progLogicCred) :
    credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true ∨
    credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true := by
  obtain ⟨r, d, hoc', hacc⟩ := WSC.LR_SPEND_RUNS_VALIDATOR hp ctx t hdep hoc ht hpc
  have hsteps := hb.1 _ (sameTx_withPurpose ctx r (.SpendingScript t.txInInfoOutRef d))
  have hsucc :=
    (WSC.LR_BUDGET_base baseNonVacuous hp.globalLogicCred hp.seizeLogicCred _ hoc' hsteps).mp hacc
  have := WSC.P3_base_requires_global_or_seize hp.globalLogicCred hp.seizeLogicCred _
    (validSpendingContext_of_onChain ctx r t.txInInfoOutRef d hoc') hsucc
  simpa [WSC.withPurpose] using this

/-- **`covering_excludes_ledger_registration`** — the LEDGER-level half of
ADDENDUM E3's bridge, proved from `DIRWF_L` (below) rather than assumed. Stated
as a standalone lemma over the non-overlap hypothesis so the axiom appears in
exactly one place. -/
theorem covering_excludes_ledger_registration
    (hp : WSC.HonestParams) (L : Ledger) (ctx : ScriptContext) (L' : Ledger)
    (cs : CurrencySymbol)
    (hno : WSC.dirNoOverlap hp.directoryNodeCS (ledgerOuts L))
    (hstep : LedgerStep L ctx L')
    (hreg : RegisteredIn hp L cs) :
    ¬ WSC.coveringIn hp.directoryNodeCS cs (WSC.dirPreState ctx) := by
  intro hcov
  obtain ⟨hins, hrefs⟩ := lr_inputs_in_ledger L ctx L' hstep
  refine WSC.covering_excludes_registeredIn hno ?_ hreg
  refine WSC.coveringIn_mono (os := WSC.dirPreState ctx) (fun o ho => ?_) hcov
  simp only [WSC.dirPreState, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨t, ht, hEq⟩ | ⟨t, ht, hEq⟩
  · exact hEq ▸ List.mem_map_of_mem (f := UTxO.utxoOut) (hrefs t ht)
  · exact hEq ▸ List.mem_map_of_mem (f := UTxO.utxoOut) (hins t ht)

/-! ### §7.1 The RAW ↔ GROUND-TRUTH reconciliation of the exemption predicate
(task U2)

`LeafSet.p1` states the non-exemption premise in this file's GROUND-TRUTH
vocabulary — `¬ WSC.coveringIn` (`authenticDirNode` = `hasCurrencySymbol`, plus
the full 5-field `DirectorySetNode` decode). Every leaf that could discharge it
states it RAW, as `coveringNodeExists dirCS cs referenceInputs = false`
(`WSC/Props/P1_Transfer.lean:211-223`, and the four shaped P1 theorems of
`WSC/Props/Shaped/P1Shaped.lean` carry exactly that hypothesis): PCB's cheap
`hasCSH` shape check plus the 3-field prefix decode `dirNodeFields`.

§9.2 recorded closing that gap as an unwritten obligation "costing `WSC.TS3` +
`WSC.TS5`". This section CLOSES it, and it costs `WSC.TS3` ONLY — the `hasCSH` →
`authenticDirNode` half turns out to be an ordinary lemma (`hasCSH` returning
`some true` exhibits the policy as the value's second entry, which is enough for
`hasCurrencySymbol`), so `TS5` is not needed for this direction.

IMPORT-CYCLE NOTE, stated rather than hidden: `coveringNodeExists` is defined in
`WSC/Props/P1_Transfer.lean`, which imports `WSC.Honest`, so this file cannot
name it. `coveringRaw` below is that definition RE-STATED verbatim over the same
two `WSC.Model` primitives this file does import. The `rfl`-style bridge
`coveringRaw ≡ Model.coveringNodeExists` therefore belongs in a module downstream
of both; that is exactly the pattern `WSC/Props/Shaped/P6Bridge.lean` already
uses for the two independently-defined copies of `outSum`/`inSum`, and it adds no
trust. -/

/-- **The RAW exemption predicate**, verbatim re-statement of
`WSC.Model.coveringNodeExists` (`WSC/Props/P1_Transfer.lean:211-223`): some
reference input is `hasCSH`-authenticated for `dirCS` and its datum's 3-field
prefix decodes to an interval that STRICTLY covers `cs`.

Both walks of the transfer validator exempt a policy in exactly this one way
(transfer walk ProgrammableLogicBase.hs:891-908, mint walk :996-1016). -/
def coveringRaw (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match WSC.Model.dirNodeFields d with
            | some (k, n, _) =>
                decide (k < cs) && decide (cs < n) &&
                  (WSC.Model.hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || coveringRaw dirCS cs rest

/-- **Half 1 of the reconciliation: the cheap authentication implies the
ground-truth one.** `WSC.Model.hasCSH` (the mirror of `phasCSH`,
ProgrammableLogicBase.hs:754-757) only looks at the value's SECOND entry; when it
answers `some true` that entry's key IS `dirCS`, and membership is all
`WSC.authenticDirNode` (= `hasCurrencySymbol`) asks for.

This is why `WSC.TS5` is NOT needed here: TS5 is the converse direction
(ground-truth membership ⟹ the policy is the FIRST non-ada entry), which is what
a proof would need to run `hasCSH` forwards. -/
theorem authenticDirNode_of_hasCSH (dirCS : CurrencySymbol) (o : TxOut)
    (h : WSC.Model.hasCSH dirCS o.txOutValue = some true) :
    WSC.authenticDirNode dirCS o = true := by
  unfold WSC.Model.hasCSH at h
  match hv : o.txOutValue with
  | [] => rw [hv] at h; simp at h
  | x :: [] => rw [hv] at h; simp at h
  | x :: (Data.B cs', dv) :: rest =>
      rw [hv] at h
      simp only [Option.some.injEq, beq_iff_eq] at h
      subst h
      simp only [WSC.authenticDirNode, hv, hasCurrencySymbol, Bool.or_eq_true]
      exact Or.inr (Or.inl (by simp))
  | x :: (Data.Constr _ _, _) :: rest => rw [hv] at h; simp at h
  | x :: (Data.Map _, _) :: rest => rw [hv] at h; simp at h
  | x :: (Data.List _, _) :: rest => rw [hv] at h; simp at h
  | x :: (Data.I _, _) :: rest => rw [hv] at h; simp at h

/-- **Half 2 of the reconciliation: the full 5-field decode refines the 3-field
prefix decode.** If an output's inline datum decodes as a `DirectorySetNode` then
`WSC.Model.dirNodeFields` reads the SAME `key` and `next` off it.

Encoding fact this rests on (`WSC/Redeemer.lean:250-273`): the datum is a
`Data.List` of FIVE elements whose first two are `Data.B key`, `Data.B next`, and
`dirNodeFields` matches the `Data.List (B k :: B n :: tls :: _)` prefix. -/
theorem dirNodeFields_of_fromData (d : Data) (nd : WSC.DirectorySetNode)
    (h : (CardanoLedgerApi.IsData.Class.IsData.fromData d :
      Option WSC.DirectorySetNode) = some nd) :
    ∃ tls : Data, WSC.Model.dirNodeFields d = some (nd.key, nd.next, tls) := by
  simp only [CardanoLedgerApi.IsData.Class.IsData.fromData] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, rfl⟩
    · simp at h
  · simp at h

/-- Half 2, packaged for the use site: the same fact about an OUTPUT whose inline
datum is `d`. -/
theorem dirNodeFields_of_dirNodeDatum (o : TxOut) (nd : WSC.DirectorySetNode)
    (h : WSC.dirNodeDatum o = some nd) (d : Data)
    (hd : o.txOutDatum = .OutputDatum d) :
    ∃ tls : Data, WSC.Model.dirNodeFields d = some (nd.key, nd.next, tls) := by
  refine dirNodeFields_of_fromData d nd ?_
  simpa [WSC.dirNodeDatum, hd] using h

/-- **The reconciliation, list form.** Over a reference-input list whose
authentic directory nodes are known to carry decodable datums (that is `WSC.TS3`),
the RAW covering-node scan is SOUND for the ground-truth `coveringIn`. -/
theorem coveringIn_of_coveringRaw_aux (dirCS cs : CurrencySymbol) :
    ∀ (refs : List TxInInfo),
      (∀ t ∈ refs, WSC.authenticDirNode dirCS t.txInInfoResolved →
        (WSC.dirNodeDatum t.txInInfoResolved).isSome) →
      coveringRaw dirCS cs refs = true →
      WSC.coveringIn dirCS cs (refs.map (·.txInInfoResolved)) := by
  intro refs
  induction refs with
  | nil => intro _ h; simp [coveringRaw] at h
  | cons i rest ih =>
      intro hts h
      simp only [coveringRaw, Bool.or_eq_true] at h
      rcases h with hhd | hrest
      · -- the covering node is THIS reference input
        match hdat : i.txInInfoResolved.txOutDatum with
        | .OutputDatum d =>
            simp only [hdat] at hhd
            match hf : WSC.Model.dirNodeFields d with
            | some (k, n, tls) =>
                simp only [hf] at hhd
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hhd
                obtain ⟨⟨hk, hn⟩, hcsh⟩ := hhd
                have hauth := authenticDirNode_of_hasCSH dirCS _ hcsh
                obtain ⟨nd, hnd⟩ :=
                  Option.isSome_iff_exists.mp (hts i (List.mem_cons_self ..) hauth)
                obtain ⟨tls', hf'⟩ := dirNodeFields_of_dirNodeDatum _ nd hnd d hdat
                rw [hf] at hf'
                simp only [Option.some.injEq, Prod.mk.injEq] at hf'
                obtain ⟨hkey, hnext, -⟩ := hf'
                refine ⟨i.txInInfoResolved, by simp, hauth, k, n, ?_, ?_, hk, hn⟩
                · rw [WSC.dirNodeKey, hnd]; simp [hkey]
                · rw [WSC.dirNodeNext, hnd]; simp [hnext]
            | none => simp only [hf] at hhd; simp at hhd
        | .OutputDatumHash _ => simp only [hdat] at hhd; simp at hhd
        | .NoOutputDatum => simp only [hdat] at hhd; simp at hhd
      · -- …or in the tail
        have := ih (fun t ht => hts t (List.mem_cons_of_mem _ ht)) hrest
        exact WSC.coveringIn_mono
          (fun o ho => by
            simp only [List.map_cons, List.mem_cons]; exact Or.inr ho) this

/-- **THE RECONCILIATION (task U2).** For an on-chain transaction of the audited
deployment, the RAW covering-node scan the leaves carry implies the GROUND-TRUTH
`coveringIn` over the pre-state snapshot.

TRUST COST: `WSC.TS3` (authentic directory nodes among the reference inputs carry
a decodable inline datum) — a consequence of `WSC.DIRWF` conjunct (iii), same
discharge (U10). Nothing else. -/
theorem coveringIn_of_coveringRaw (hp : WSC.HonestParams) (ctx : ScriptContext)
    (cs : CurrencySymbol) (hdep : WSC.Deployed hp) (hoc : WSC.OnChain ctx)
    (h : coveringRaw hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = true) :
    WSC.coveringIn hp.directoryNodeCS cs (WSC.dirPreState ctx) := by
  refine WSC.coveringIn_mono (os := ctx.scriptContextTxInfo.txInfoReferenceInputs.map
    (·.txInInfoResolved)) (fun o ho => ?_) ?_
  · simp only [WSC.dirPreState, List.mem_append]; exact Or.inl ho
  · exact coveringIn_of_coveringRaw_aux _ _ _
      (fun t ht hauth => Option.isSome_iff_exists.mpr
        (by
          have := WSC.TS3 hp ctx hdep hoc t ht hauth
          exact Option.isSome_iff_exists.mp this))
      h

/-- **WHAT §7 AND ITEM 3 OF TASK U2 ASK FOR: the leaves' raw premise, supplied by
the PROVED bridge.** A policy registered in the pre-state ledger cannot be
exempted, and the exemption is unavailable in the RAW form the leaves state it —
no explicit `coveringNodeExists … = false` hypothesis is needed anywhere.

CHAIN: `DIRWF_L` (ledger-level interval non-overlap) →
`covering_excludes_ledger_registration` (proved above, via
`WSC.covering_excludes_registeredIn`) → this contraposition of
`coveringIn_of_coveringRaw` (via `WSC.TS3`).

So the ONLY directory assumptions behind the leaves' exemption hypothesis are
`DIRWF_L` conjunct-(iv)-analogue and `WSC.TS3`, both discharged by U10. -/
theorem coveringRaw_false_of_registered
    (hp : WSC.HonestParams) (L : Ledger) (ctx : ScriptContext) (L' : Ledger)
    (cs : CurrencySymbol)
    (hdep : WSC.Deployed hp) (hoc : WSC.OnChain ctx)
    (hno : WSC.dirNoOverlap hp.directoryNodeCS (ledgerOuts L))
    (hstep : LedgerStep L ctx L')
    (hreg : RegisteredIn hp L cs) :
    coveringRaw hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = false := by
  have hnocov := covering_excludes_ledger_registration hp L ctx L' cs hno hstep hreg
  by_cases hb : coveringRaw hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = true
  · exact absurd (coveringIn_of_coveringRaw hp ctx cs hdep hoc hb) hnocov
  · simpa using hb

/-- `NE` follows from `CONTAIN` once the out-of-base inputs are known to hold
nothing: conservation (`LR_BALANCE_SLOT`) turns the containment inequality into
`outOff ≤ 0`, and non-negativity of the outputs turns that into `outOff = 0`.

This is the arithmetic core of ARCHITECTURE.md §5.2's reduction, and it is where
`WSC.NONNEG` (ADDENDUM E6) is consumed. -/
theorem nonEscape_of_contain (hp : WSC.HonestParams) (ctx : ScriptContext)
    (cs : CurrencySymbol) (tn : TokenName)
    (hoc : WSC.OnChain ctx) (hcs : cs ≠ adaSymbol)
    (hin : inOff hp.progLogicCred cs tn ctx = 0)
    (hcon : Contain hp.progLogicCred cs tn ctx) :
    NonEscape hp.progLogicCred cs tn ctx := by
  have hbal := LR_BALANCE_SLOT ctx hp.progLogicCred cs tn hoc hcs
  have hnn := (WSC.NONNEG ctx hoc).2.2
  have hge : (0:Int) ≤ outOff hp.progLogicCred cs tn ctx :=
    sumOutsIf_nonneg _ cs tn _ (fun o ho => hnn o ho cs tn)
  exact int_escape_zero hbal hin hcon hge

/-- The out-of-base inputs of a transaction hold nothing of `(cs, tn)` when the
pre-state ledger holds nothing of it outside the mini-ledger. Uses
`lr_inputs_in_ledger` (the inputs came from `L`) and `NONNEG_L` (no negative
holding can hide a positive one). -/
theorem inOff_zero (hp : WSC.HonestParams) (L : Ledger) (ctx : ScriptContext)
    (L' : Ledger) (cs : CurrencySymbol) (tn : TokenName)
    (hnn : ∀ u ∈ L, (0:Int) ≤ valueOf cs tn u.utxoOut.txOutValue)
    (hstep : LedgerStep L ctx L')
    (hI : OutOfBase hp.progLogicCred cs tn L = 0) :
    inOff hp.progLogicCred cs tn ctx = 0 := by
  obtain ⟨hins, _⟩ := lr_inputs_in_ledger L ctx L' hstep
  refine sumInsIf_eq_zero _ cs tn _ (fun t ht hp' => ?_)
  have hmem : UTxO.mk t.txInInfoOutRef t.txInInfoResolved ∈ L.filter (offBase hp.progLogicCred) :=
    List.mem_filter.mpr ⟨hins t ht, by simpa [offBase, offBaseB] using hp'⟩
  exact sumHoldU_elim cs tn _
    (fun u hu => hnn u (List.mem_filter.mp hu).1) hI _ hmem

/-- **THE BRANCH ANALYSIS (ARCHITECTURE.md §5.2).** For a policy already
registered in the pre-state ledger, every in-scope transaction satisfies the
NON-ESCAPE obligation.

The four branches, and what closes each:

| branch | trigger | closed by |
|---|---|---|
| **B** entrance, `0 < mintOf cs tn` | `ts_minting_identity_L` + `WSC.LR_MINT_RUNS_POLICY` force the issuance policy to run | `LeafSet.p4`, then per arm: `Local` ⟹ `nonEscape_of_noEscape` directly; `DelegateTransfer` ⟹ `WSC.LR_WDRL_RUNS_VALIDATOR` ⟹ `LeafSet.p1`; `DelegateSeize` ⟹ `WSC.LR_WDRL_RUNS_VALIDATOR` ⟹ `LeafSet.p2`; `BurnOnly` ⟹ CONTRADICTION with `0 < mintOf` via `mintOf_nonpos_of_not_mintPos` |
| **C** exit, a mini-ledger input holds `cs` | `WSC.LR_SPEND_RUNS_VALIDATOR` ⟹ `p3_lifted` ⟹ global or seize in `wdrl` ⟹ `WSC.LR_WDRL_RUNS_VALIDATOR` | `LeafSet.p1` or `LeafSet.p2` |
| **A** neither | — | pure conservation: `inAtB = 0` and `mintOf ≤ 0`, so `Contain` holds because `outAtB ≥ 0` |

The `NonMember` exemption is closed WITHOUT any extra hypothesis: `LeafSet.p1`'s
`¬ coveringIn` premise is supplied by `covering_excludes_ledger_registration`,
i.e. by `DIRWF_L` + the new `WSC.covering_excludes_registeredIn` bridge lemma. That
is the pair ADDENDUM E3 requires, and the reason P5 does not appear as a `LeafSet`
field: P5's role in the composition is to make the exemption UNAVAILABLE to a
registered policy, and the bridge does that once the interval conjunct exists.

NON-CIRCULARITY (ARCHITECTURE.md Tier 5.3): branch B's delegate arms only witness
that the global/seize validator RAN; they never bound outputs themselves. Branch
C rests on `WSC.LR_SPEND_RUNS_VALIDATOR`, a ledger rule independent of every
P-theorem. Every context handed to a leaf is `WSC.withPurpose ctx _ _`, so
`SameTx` holds by `rfl` and the whole analysis lives on ONE shared `TxInfo`
(Tier 5.1). -/
theorem nonEscape_of_registered (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (leaves : LeafSet hp Shape)
    (L : Ledger) (ctx : ScriptContext) (L' : Ledger)
    (cs : CurrencySymbol) (tn : TokenName)
    (hdep : WSC.Deployed hp)
    (hno : WSC.dirNoOverlap hp.directoryNodeCS (ledgerOuts L))
    (htx : HonestTx hp Shape ctx) (hstep : LedgerStep L ctx L')
    (hreg : RegisteredIn hp L cs) (hcs : cs ≠ adaSymbol)
    (hin : inOff hp.progLogicCred cs tn ctx = 0) :
    NonEscape hp.progLogicCred cs tn ctx := by
  obtain ⟨hoc, hb, hsh⟩ := htx
  have hnocov := covering_excludes_ledger_registration hp L ctx L' cs hno hstep hreg
  have hOutNN := (WSC.NONNEG ctx hoc).2.2
  -- the two routes into `Contain` through a validator that ran on this transaction
  have viaGlobal : credentialInWithdrawals hp.globalLogicCred
      ctx.scriptContextTxInfo.txInfoWdrl = true → Contain hp.progLogicCred cs tn ctx := by
    intro hw
    obtain ⟨rg, hocg, haccg⟩ := (WSC.LR_WDRL_RUNS_VALIDATOR hp ctx hdep hoc).1 (by simpa using hw)
    exact leaves.p1 ctx (WSC.withPurpose ctx rg (ScriptInfo.RewardingScript hp.globalLogicCred))
      cs tn hdep hoc hsh rfl rfl haccg hcs hnocov
  have viaSeize : credentialInWithdrawals hp.seizeLogicCred
      ctx.scriptContextTxInfo.txInfoWdrl = true → Contain hp.progLogicCred cs tn ctx := by
    intro hw
    obtain ⟨rs, hocs, haccs⟩ := (WSC.LR_WDRL_RUNS_VALIDATOR hp ctx hdep hoc).2 (by simpa using hw)
    exact leaves.p2 ctx (WSC.withPurpose ctx rs (ScriptInfo.RewardingScript hp.seizeLogicCred))
      cs tn hdep hoc hsh rfl rfl haccs hcs
  by_cases hmint : (0:Int) < WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint
  · -- BRANCH B (entrance via a positive mint)
    have hhas : hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint = true := by
      refine hasCS_of_valueOf_ne_zero cs tn _ ?_
      intro h0
      exact absurd (h0 ▸ hmint : (0:Int) < 0) (by decide)
    obtain ⟨mlh, hmlh⟩ := ts_minting_identity_L hp L cs hdep hreg
    obtain ⟨r, hoc', hacc⟩ := WSC.LR_MINT_RUNS_POLICY hp ctx cs mlh hdep hoc hhas hmlh
    rcases leaves.p4 ctx (WSC.withPurpose ctx r (ScriptInfo.MintingScript cs)) cs mlh
        hdep hoc hsh rfl rfl hacc with hlocal | hglob | hseize | hburn
    · exact nonEscape_of_noEscape hp.progLogicCred cs tn _ hlocal
    · exact nonEscape_of_contain hp ctx cs tn hoc hcs hin (viaGlobal hglob)
    · exact nonEscape_of_contain hp ctx cs tn hoc hcs hin (viaSeize hseize)
    · exact absurd hmint (Int.not_lt.mpr (mintOf_nonpos_of_not_mintPos cs tn _ hburn))
  · -- `mintOf cs tn ≤ 0`
    have hmint' : WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint ≤ (0:Int) :=
      Int.not_lt.mp hmint
    by_cases hbi : ∃ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
        WSC.payCred t.txInInfoResolved = hp.progLogicCred
    · -- BRANCH C (exit: a mini-ledger UTxO is spent)
      obtain ⟨t, ht, hpc⟩ := hbi
      rcases p3_lifted hp ctx t hdep hoc hb ht hpc with hglob | hseize
      · exact nonEscape_of_contain hp ctx cs tn hoc hcs hin (viaGlobal hglob)
      · exact nonEscape_of_contain hp ctx cs tn hoc hcs hin (viaSeize hseize)
    · -- BRANCH A (no mini-ledger input at all, nothing minted): pure conservation
      have hinAtB : inAtB hp.progLogicCred cs tn ctx = 0 := by
        refine sumInsIf_eq_zero _ cs tn _ (fun t ht hp' => ?_)
        exact absurd ⟨t, ht, by simpa [atBaseB] using hp'⟩ hbi
      have hout : (0:Int) ≤ outAtB hp.progLogicCred cs tn ctx :=
        sumOutsIf_nonneg _ cs tn _ (fun o ho => hOutNN o ho cs tn)
      exact nonEscape_of_contain hp ctx cs tn hoc hcs hin
        (int_contain_trivial hinAtB hmint' hout)

/-- **PRESERVATION (ARCHITECTURE.md §5.2)** — *one in-scope transaction cannot
break the invariant.*

PROVED, unconditionally, from: the `LeafSet` hypotheses, the §4 ledger axioms, and
`WSC/Honest.lean`'s `NONNEG`, `LR_CTX`, `LR_MINT_RUNS_POLICY`,
`LR_WDRL_RUNS_VALIDATOR`, `LR_SPEND_RUNS_VALIDATOR`, `LR_BUDGET_base`.

The reduction: `lr_utxo_semantics` turns the goal into
`OutOfBase L − inOff + outOff = 0`; `I L` gives `OutOfBase L = 0`; `inOff_zero`
(non-negativity + inputs-came-from-`L`) gives `inOff = 0`; and
`nonEscape_of_registered` gives `outOff = 0`. The newly-registered case is the
`LeafSet.nopre` obligation. -/
theorem preservation (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (leaves : LeafSet hp Shape)
    (L : Ledger) (ctx : ScriptContext) (L' : Ledger)
    (hdep : WSC.Deployed hp)
    (hnn : ∀ u ∈ L, ∀ (cs : CurrencySymbol) (tn : TokenName),
      (0:Int) ≤ valueOf cs tn u.utxoOut.txOutValue)
    (hno : WSC.dirNoOverlap hp.directoryNodeCS (ledgerOuts L))
    (htx : HonestTx hp Shape ctx) (hstep : LedgerStep L ctx L')
    (hI : I hp L) : I hp L' := by
  intro cs tn hcs hreg'
  have hbal := lr_utxo_semantics L ctx L' hstep hp.progLogicCred cs tn
  by_cases hreg : RegisteredIn hp L cs
  · have hI0 := hI cs tn hcs hreg
    have hin := inOff_zero hp L ctx L' cs tn (fun u hu => hnn u hu cs tn) hstep hI0
    have hne := nonEscape_of_registered hp Shape leaves L ctx L' cs tn hdep hno htx hstep
      hreg hcs hin
    exact int_step_zero hbal hI0 hin hne
  · rcases lr_registration_source hp L ctx L' cs hstep hreg' with h | hnew
    · exact absurd h hreg
    · obtain ⟨hI0, hne⟩ := leaves.nopre L ctx L' cs tn hdep hstep htx hreg hnew
      have hin := inOff_zero hp L ctx L' cs tn (fun u hu => hnn u hu cs tn) hstep hI0
      simp only [NonEscape] at hne
      omega

/-! # §8 The reachable trace and the top claim -/

/-- Ledger states reachable by a trace of in-scope honest transactions from a
genesis state. `Shape` restricts every step (ADDENDUM E1 / task Z2): the trace
class is exactly as narrow as the narrowest leaf discharge. -/
inductive Reachable (hp : WSC.HonestParams) (Shape : ScriptContext → Prop) :
    Ledger → Prop
  | genesis {L : Ledger} (h : Genesis hp L) : Reachable hp Shape L
  | step {L L' : Ledger} {ctx : ScriptContext}
      (hR : Reachable hp Shape L) (hT : HonestTx hp Shape ctx)
      (hS : LedgerStep L ctx L') : Reachable hp Shape L'

/-- **§5.3 `ts_genesis`.** The genesis state of the audited deployment satisfies
the invariant. AUDIT / DISCHARGE: inspect the deployment transaction — the
directory holds only its two sentinels, no policy is registered, and no
programmable token exists at all. -/
axiom ts_genesis :
  ∀ (hp : WSC.HonestParams) (L : Ledger),
    WSC.Deployed hp → Genesis hp L → I hp L

/-- **ADDENDUM E6, LEDGER-WIDE form.** Every UTxO of a reachable state holds a
non-negative amount of every asset. `WSC/Honest.lean`'s `NONNEG` is explicitly
only the PER-TRANSACTION projection of this and does not imply it (see its SCOPE
NOTE); this is the restatement that note asks for.

WHY UNAVOIDABLE / LEDGER RULE: a UTxO cannot hold a negative quantity — the
ledger's `MultiAsset` values in the UTxO set are positive by construction. -/
axiom NONNEG_L :
  ∀ (hp : WSC.HonestParams) (Shape : ScriptContext → Prop) (L : Ledger),
    Reachable hp Shape L →
    ∀ u ∈ L, ∀ (cs : CurrencySymbol) (tn : TokenName),
      (0:Int) ≤ valueOf cs tn u.utxoOut.txOutValue

/-- **`DIRWF_L` — the LEDGER-level interval non-overlap, ESCAPE-CRITICAL.** The
authentic directory nodes of a reachable ledger state have pairwise
non-overlapping `(key, next)` intervals: no node's key lies strictly inside
another node's interval.

This is the ledger-level counterpart of `WSC.DirWF`'s conjunct (iv) (added by task
V4) and it is what `covering_excludes_ledger_registration` consumes. SAME
DISCHARGE: **U10** — formalize `mkDirectoryNodeMP` at UPLC, prove that an insert
preserves non-overlap (the insert splits one interval into two, so the property is
an invariant of the insert rule), and lift over the trace. Until then the top claim
is exactly as strong as this axiom.

WHY IT IS NOT DERIVABLE FROM `WSC.DIRWF`: `DirWF` is per-transaction and its
conjunct (iv) speaks about the snapshot ONE transaction shows. Lifting it to the
whole UTxO set is the "lift over history" half of U10, not a Lean derivation from
the per-transaction axiom. -/
axiom DIRWF_L :
  ∀ (hp : WSC.HonestParams) (Shape : ScriptContext → Prop) (L : Ledger),
    WSC.Deployed hp → Reachable hp Shape L →
      WSC.dirNoOverlap hp.directoryNodeCS (ledgerOuts L)

/-- # THE TOP CLAIM
*In an honest deployment, programmable tokens cannot exist outside the
mini-ledger (the `programmableLogicBase` payment credential).*

Formally: in every ledger state reachable from genesis by a trace of in-scope
honest transactions, every registered non-ada policy holds ZERO of every asset
slot at every UTxO whose payment credential is not `hp.progLogicCred`.

## THE COMPLETE HONEST SCOPE OF THIS THEOREM

1. **It is CONDITIONAL on `leaves : LeafSet hp Shape`.** That is the point: the
   theorem is a machine-checked REDUCTION of the claim to four named leaf
   obligations. §9 audits each one against the library. As of task V4 **none of
   the four is fully discharged**, so this theorem must never be quoted as "the
   claim is proved" — only as "the claim follows from exactly these four
   obligations, and here is where each one stands".
2. **BOUNDED TRANSACTIONS (ADDENDUM E1).** Every step carries `WithinBudget`: the
   published CEK step bounds `K_base = 600`, `K_mint = 900`, `K_global = 4400`
   (task U2 republished `K_global` from 1600; the minting clause is still 900 and
   is still too tight for P4's three non-burn arms — §10.5). Nothing here covers
   unboundedly large transactions. There is no `K_seize`.
3. **SHAPE RESTRICTIONS (task Z2).** Every step carries `Shape`. Instantiating a
   leaf with a shaped `by blaster` theorem forces `Shape` to be that shape's
   membership predicate — a severe restriction on list lengths, constructor tags
   and `Option`s — plus the SHAPE-BRIDGE obligation of §9.4.
4. **`DirWF` IS ASSUMED AND ESCAPE-CRITICAL.** The claim is exactly as strong as
   `DIRWF_L` (this file) and `WSC.DIRWF` (four conjuncts). The escape-critical
   ones are (i) insert-only, (iii) NFT-name = node-key datum binding and (iv)
   interval non-overlap. `U10` (`mkDirectoryNodeMP` at UPLC + lift over history)
   is what would discharge them.
5. **FAITHFULNESS AXIOMS.** Discharging `LeafSet.p1`/`LeafSet.p2` by the
   source-model route imports `WSC.Model.globalModel_faithful` and
   `WSC.SeizeModel.seizeModel_faithful` — whole-validator hand-transcription
   equivalences, evidenced (4/4 and 13/13 golden differential agreement, source
   line citations) but not proved.
6. **LEDGER AXIOMS.** §4 (`lr_utxo_semantics`, `lr_inputs_in_ledger`,
   `lr_registration_source`, `LR_BALANCE_SLOT`, `ts_minting_identity_L`),
   `ts_genesis`, `NONNEG_L`, `DIRWF_L`, and the `WSC/Honest.lean` set. Of these
   `LR_BALANCE_SLOT` is the only one that is a CONSEQUENCE of an existing axiom
   (`WSC.LR7` / `isBalanced`) rather than a primitive ledger fact, and task U2 wrote
   that derivation: `LR_BALANCE_SLOT_of_valueAlgebra` proves it from `WSC.LR7` plus
   two `CardanoLedgerApi`-only residues (`ValueAlgebra`, `LedgerCanon`). The axiom
   is retained only until those are instantiated — §9.5c.
7. **`cs ≠ adaSymbol`** is built into `I`; see `I`'s FINDING for why omitting it
   makes the invariant false.
8. **NOT COVERED AT ALL:** collateral inputs (PlutusV3 `TxInfo` has no collateral
   field — `WSC/Honest.lean`, §5.3 `lr_collateral_pubkey_only` "NOT
   EXPRESSIBLE"); per-holder ownership inside the mini-ledger (this is aggregate
   containment at the base PAYMENT credential — ARCHITECTURE.md Tier 3.3); and
   the P2′ obligation (a seized-policy mint bypassing the seize), which is
   DEFERRED. -/
theorem top_claim (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (leaves : LeafSet hp Shape) (hdep : WSC.Deployed hp) :
    ∀ (L : Ledger), Reachable hp Shape L → I hp L := by
  intro L hR
  induction hR with
  | genesis h => exact ts_genesis hp _ hdep h
  | step hR hT hS ih =>
      exact preservation hp Shape leaves _ _ _ hdep
        (NONNEG_L hp Shape _ hR) (DIRWF_L hp Shape _ hdep hR) hT hS ih

/-- The top claim, unfolded into the plain-English shape: no UTxO outside the
mini-ledger holds any registered programmable token. -/
theorem no_programmable_tokens_outside_mini_ledger
    (hp : WSC.HonestParams) (Shape : ScriptContext → Prop)
    (leaves : LeafSet hp Shape) (hdep : WSC.Deployed hp)
    (L : Ledger) (hR : Reachable hp Shape L)
    (cs : CurrencySymbol) (tn : TokenName)
    (hcs : cs ≠ adaSymbol) (hreg : RegisteredIn hp L cs) :
    ∀ u ∈ L, WSC.payCred u.utxoOut ≠ hp.progLogicCred →
      valueOf cs tn u.utxoOut.txOutValue = (0:Int) := by
  intro u hu hpc
  have hI := top_claim hp Shape leaves hdep L hR cs tn hcs hreg
  have hmem : u ∈ L.filter (offBase hp.progLogicCred) :=
    List.mem_filter.mpr ⟨hu, by simpa [offBase] using hpc⟩
  exact sumHoldU_elim cs tn _
    (fun v hv => NONNEG_L hp Shape L hR v (List.mem_filter.mp hv).1 cs tn) hI u hmem

/-! # §10 VOCABULARY BRIDGES AND THE LEAF INSTANTIATION (task U2)

§9.2 lists, for `LeafSet.p1`, four gaps between what
`WSC/Props/Shaped/P1Shaped.lean` proves and what this file's field asks for. Two
of them are VOCABULARY, and this section closes both, as theorems:

1. the sums: the shaped theorems conclude in `WSC.Model.outSum` / `WSC.Model.inSum`
   (`WSC/Model/Ground.lean:43-56`), this file's `Contain` is stated with
   `outAtB` / `inAtB` — §10.1;
2. the exemption predicate: the shaped theorems hypothesise
   `coveringNodeExists … = false` (raw), this file's field hypothesises
   `¬ WSC.coveringIn` (ground truth) — §7.1 above, applied in §10.2.

The mint term needs no bridge at all: `WSC.Model.mintSigned cs tn mint` is
*definitionally* `valueOf cs tn mint` (`WSC/Props/P1_Transfer.lean:192-193`, whose
own docstring says "Same as `WSC.mintOf`"), and `WSC.mintOf cs tn mint` is the same
body (`WSC/Spec.lean:45-46`). So `Contain`'s mint term and the shaped
conclusion's mint term are the same term.

The two gaps §10 does NOT close, and cannot from inside this file, are the ones
that are not about vocabulary: the SHAPE BRIDGE (§9.4) and a global budget bridge
at the shaped budget (`WSC.LR_BUDGET_global`'s named TODO). They are carried as
ONE explicit field in §10.2's structure so that a reader can see exactly what an
instantiation still owes. -/

/-! ## §10.1 The sum bridges — PROVED, ordinary list inductions

`WSC.Model.outSum base` and `sumOutsIf (atBaseB base)` are the same fold: the
model's guard is `WSC.payCred o == base`, and `atBaseB base o` unfolds to exactly
that (`atBaseB`, §2). The inductions below are therefore trivial, and that is the
point — the two task-independent transcriptions of ARCHITECTURE.md §3's
`outAtBase`/`inAtBase` agree on the nose, with no side condition. -/

theorem outSum_eq_sumOutsIf (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (os : List TxOut),
      WSC.Model.outSum base cs tn os = sumOutsIf (atBaseB base) cs tn os := by
  intro os
  induction os with
  | nil => rfl
  | cons o rest ih => simp only [WSC.Model.outSum, sumOutsIf, atBaseB, ih]

theorem inSum_eq_sumInsIf (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (ts : List TxInInfo),
      WSC.Model.inSum base cs tn ts = sumInsIf (atBaseB base) cs tn ts := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t rest ih => simp only [WSC.Model.inSum, sumInsIf, atBaseB, ih]

/-- `outAtB` (this file) = `Model.outSum` (the shaped leaves) at a transaction's
outputs. -/
theorem outAtB_eq_outSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) :
    outAtB base cs tn ctx =
      WSC.Model.outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs :=
  (outSum_eq_sumOutsIf base cs tn _).symm

/-- `inAtB` (this file) = `Model.inSum` (the shaped leaves) at a transaction's
inputs. -/
theorem inAtB_eq_inSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) :
    inAtB base cs tn ctx =
      WSC.Model.inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs :=
  (inSum_eq_sumInsIf base cs tn _).symm

/-- **`Contain`, in the shaped leaves' vocabulary.** The two statements are the
same proposition; this is the rewriting that lets a shaped theorem be quoted at a
`LeafSet` field without restating it. -/
theorem contain_iff_modelSums (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) :
    Contain base cs tn ctx ↔
      WSC.Model.outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
        ≥ WSC.Model.inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
          + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint := by
  rw [Contain, outAtB_eq_outSum, inAtB_eq_inSum]

/-! ## §10.2 `LeafSet.p1`, instantiated from a shaped global containment theorem

The `Shape` restriction is carried IN THE TYPE (the `Shape` parameter of
`ShapedGlobalContainment` is the same `Shape` the `LeafSet` and `HonestTx` carry),
so a reader cannot quote the conclusion without carrying the shape.

WHAT THE ONE FIELD PACKAGES, and why it is one field rather than several: the
shaped theorems' subject is `isSuccessful (appliedGlobalShapedT1.prop <scalars>)`,
while a leaf's trigger is `WSC.NodeAcceptsGlobal`. Getting from the former to the
latter needs BOTH (i) the SHAPE BRIDGE of §9.4 and (ii) `WSC.LR_BUDGET_global` at
the shaped prep's budget (4400 = `WSC.K_global`, whose non-vacuity IS
dischargeable at the shaped preps — `P1_T*_vacuity_probe` = `Falsified` plus the
concrete `P1ShapedWitness`). Neither exists yet, and neither is a vocabulary
question, so they are deliberately NOT hidden inside a definition here: they are
the reason this field is a hypothesis and not a theorem. -/

/-- **What a SHAPED global containment theorem supplies, transcribed into this
file's ledger vocabulary.** One field, deliberately: it is `P1Shaped`'s conclusion
with the prep/`NodeAccepts` boundary already crossed.

DISCHARGED BY, once §9.4's shape bridge and the 4400 budget bridge exist:
`WSC.P1_T1` / `WSC.P1_T2` / `WSC.P1_T6` / `WSC.P1_T7`
(`WSC/Props/Shaped/P1Shaped.lean`, `✅ Valid` at budget 4400 over SHAPES
T1/T2/T6/T7, `#print axioms` free of any `*_faithful` axiom), with
`Shape := fun ctx => ∃ scalars, ctx = p1ShapedCtx scalars ∨ ctx = p1ShapedMintCtx
scalars ∨ …`.

NOTE the hypothesis vocabulary: `coveringRaw` (§7.1), i.e. exactly what those
theorems carry, NOT the ground-truth `¬ WSC.coveringIn`. §7.1 is what closes the
difference, and it is applied in `leafP1_of_shapedGlobalContainment` below. -/
structure ShapedGlobalContainment (hp : WSC.HonestParams)
    (Shape : ScriptContext → Prop) : Prop where
  contain : ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    WSC.OnChain ctx → Shape ctx → SameTx ctx ctx' →
    ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.globalLogicCred →
    WSC.NodeAcceptsGlobal hp.protocolParamsCS ctx' →
    cs ≠ adaSymbol →
    coveringRaw hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
      WSC.Model.outSum hp.progLogicCred cs tn ctx.scriptContextTxInfo.txInfoOutputs
        ≥ WSC.Model.inSum hp.progLogicCred cs tn ctx.scriptContextTxInfo.txInfoInputs
          + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-- **`LeafSet.p1`, PROVED from a shaped global containment theorem** — the
instantiation §9.2 asked for, minus the two non-vocabulary obligations that are
now named as `ShapedGlobalContainment.contain`'s reason for existing.

Note what this theorem does with the exemption premise, which is item 3 of task
U2: the field's `¬ WSC.coveringIn` premise is converted into the leaves' raw
`coveringRaw … = false` by §7.1's `coveringIn_of_coveringRaw`, i.e. through
`WSC.TS3` — so no leaf has to carry a raw covering hypothesis into the
composition, and no new directory assumption enters. -/
theorem leafP1_of_shapedGlobalContainment (hp : WSC.HonestParams)
    (Shape : ScriptContext → Prop) (hgc : ShapedGlobalContainment hp Shape) :
    ∀ (ctx ctx' : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
      WSC.Deployed hp → WSC.OnChain ctx → Shape ctx → SameTx ctx ctx' →
      ctx'.scriptContextScriptInfo = ScriptInfo.RewardingScript hp.globalLogicCred →
      WSC.NodeAcceptsGlobal hp.protocolParamsCS ctx' →
      cs ≠ adaSymbol →
      ¬ WSC.coveringIn hp.directoryNodeCS cs (WSC.dirPreState ctx) →
        Contain hp.progLogicCred cs tn ctx := by
  intro ctx ctx' cs tn hdep hoc hsh hsame hsi hacc hcs hnocov
  have hraw : coveringRaw hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = false := by
    by_cases hb : coveringRaw hp.directoryNodeCS cs
        ctx.scriptContextTxInfo.txInfoReferenceInputs = true
    · exact absurd (coveringIn_of_coveringRaw hp ctx cs hdep hoc hb) hnocov
    · simpa using hb
  exact (contain_iff_modelSums _ _ _ _).mpr
    (hgc.contain ctx ctx' cs tn hoc hsh hsame hsi hacc hcs hraw)

/-! ## §10.3 `LeafSet.p4` — the CUSTODY-ARM vocabulary bridge, PROVED

The shaped P4 theorems (`WSC.P4_disjunction_at_L1`,
`WSC.P4_disjunction_at_DT1`, `WSC.P4_disjunction_at_DS1`,
`WSC.P4_burnonly_arm_shaped` / `WSC.P4_burn_only_shapedIdx`) conclude
`WSC/Spec.lean`'s FULL four-way disjunction
`LocalCustodyOk || DelegateTransferOk || DelegateSeizeOk || BurnOnlyOk`, one shape
at a time. `LeafSet.p4` asks for the WEAKER per-arm consequence the branch
analysis actually consumes. §10.3 proves that weakening — so `p4`'s vocabulary
gap is closed here, and what remains for `p4` is only shape coverage and budgets
(§10.5).

TWO honest side conditions, both explicit below rather than assumed:
* the shaped theorems quantify over a params datum `p : WSC.GlobalParams` read out
  of a reference input, so a leaf needs `p` to BE the deployment's parameters —
  the `hpar` hypothesis. Under honest deployment this is `WSC.TS1`/`WSC.TS2`
  (the params NFT is unique and its datum is the deployment's); it is passed in
  rather than assumed silently;
* arm 3 concludes `WSC.seizeScopedToNodeOf` — a `Rewarding seizeCred` entry in the
  REDEEMER MAP scoped to `cs`'s node — whereas `LeafSet.p4`'s third disjunct is
  `seizeCred ∈ txInfoWdrl`. That upgrade is `SeizeWdrlOfScoped`, isolated as its
  own named obligation because it is NOT a rewriting: it is a ledger fact
  (a redeemer-map entry for a rewarding purpose exists only if that reward account
  is withdrawn from). See its docstring for the audit note that the `LeafSet.p4`
  docstring's one-line claim ("`WSC.LR5`'s rewarding clause") is too quick. -/

/-- **The residual obligation of P4's `DelegateSeize` arm**: a `Rewarding
seizeCred` entry in the transaction's REDEEMER MAP, scoped to `cs`'s directory
node, implies `seizeCred` is in the WITHDRAWAL map.

WHY IT IS ISOLATED HERE (finding, task U2). `LeafSet.p4`'s docstring folds this
into the leaf with the remark "upgrading that to `seizeCred ∈ txInfoWdrl` is
`WSC.LR5`'s rewarding clause (`validScriptInfo`)". That is too quick:
`validScriptInfo` (`CardanoLedgerApi/V3/Contexts.lean:979-1002`) constrains the
purpose of the script *currently running*, and here the `Rewarding seizeCred`
entry belongs to a DIFFERENT script than the issuance policy that is running. The
fact is still a genuine ledger rule — the Conway UTXOW `scriptsNeeded` set is
built FROM the withdrawal map, so a redeemer entry for a rewarding purpose cannot
exist unless that reward account is withdrawn from — but it is a rule about the
redeemer map as a whole, not a consequence of `LR5` as stated.

DISCHARGE: strengthen `WSC.LR5` (or add an `LR_REDEEMER_PURPOSES_REAL` axiom) with
the "every redeemer-map purpose is a real purpose of this transaction" clause,
citing `Conway/TxInfo.hs` `transTxRedeemers` + the UTXOW `scriptsNeeded` rule. Not
done here: it is an axiom-base change in `WSC/Honest.lean` whose audit row does
not exist yet. -/
def SeizeWdrlOfScoped (hp : WSC.HonestParams) : Prop :=
  ∀ (ctx : ScriptContext) (cs : CurrencySymbol),
    WSC.OnChain ctx →
    WSC.seizeScopedToNodeOf hp.seizeLogicCred hp.directoryNodeCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs
      ctx.scriptContextTxInfo.txInfoRedeemers = true →
      credentialInWithdrawals hp.seizeLogicCred
        ctx.scriptContextTxInfo.txInfoWdrl = true

/-- The deployment's parameters, as the `GlobalParams` datum the validators read.
-/
def paramsOf (hp : WSC.HonestParams) : WSC.GlobalParams :=
  { directoryNodeCS := hp.directoryNodeCS
  , progLogicCred := hp.progLogicCred
  , globalLogicCred := hp.globalLogicCred
  , seizeLogicCred := hp.seizeLogicCred }

/-- **`LeafSet.p4`'s disjunction, PROVED from `WSC/Spec.lean`'s four-way custody
disjunction** — the vocabulary bridge for the entrance leaf.

Arm by arm: `Local` ⟹ its third conjunct is the ground-truth no-escape scan;
`DelegateTransfer` ⟹ its third conjunct is `globalLogicCred ∈ wdrl`;
`DelegateSeize` ⟹ its third conjunct plus `SeizeWdrlOfScoped`;
`BurnOnly` ⟹ its second conjunct is `!mintPos cs`. Nothing else in the four
predicates is used, which is exactly why `LeafSet.p4` is stated in the weak
form. -/
theorem p4_disjuncts_of_custody (hp : WSC.HonestParams) (mlh : ScriptHash)
    (cs : CurrencySymbol) (ctx : ScriptContext)
    (hsw : SeizeWdrlOfScoped hp) (hoc : WSC.OnChain ctx)
    (h : (WSC.LocalCustodyOk mlh (paramsOf hp) cs ctx ||
          WSC.DelegateTransferOk mlh (paramsOf hp) cs ctx ||
          WSC.DelegateSeizeOk mlh (paramsOf hp) cs ctx ||
          WSC.BurnOnlyOk mlh cs ctx) = true) :
    WSC.noEscape hp.progLogicCred cs ctx.scriptContextTxInfo.txInfoOutputs = true
    ∨ credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
    ∨ credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl = true
    ∨ WSC.mintPos cs ctx.scriptContextTxInfo.txInfoMint = false := by
  simp only [Bool.or_eq_true] at h
  rcases h with ((hL | hDT) | hDS) | hB
  · simp only [WSC.LocalCustodyOk, Bool.and_eq_true] at hL
    exact Or.inl hL.2
  · simp only [WSC.DelegateTransferOk, Bool.and_eq_true] at hDT
    exact Or.inr (Or.inl hDT.2)
  · simp only [WSC.DelegateSeizeOk, Bool.and_eq_true] at hDS
    exact Or.inr (Or.inr (Or.inl (hsw ctx cs hoc hDS.2)))
  · simp only [WSC.BurnOnlyOk, Bool.and_eq_true, Bool.not_eq_true'] at hB
    exact Or.inr (Or.inr (Or.inr hB.2))

/-! ## §10.5 What each field still owes AFTER §10.1-§10.4

**`LeafSet.p1`** — owes exactly two things, both named in `ShapedGlobalContainment`:
the SHAPE BRIDGE (§9.4) and `WSC.LR_BUDGET_global` instantiated at
`K_global = 4400` over a shaped prep (its named TODO in `WSC/Honest.lean`).
Vocabulary: CLOSED (§10.1, §7.1). `Shape` must be
"`ctx` is an instance of T1, T2, T6 or T7", and — new since task U2 —
`WithinBudget`'s global clause no longer excludes those transactions, because
`WSC.K_global` was republished at 4400.

**`LeafSet.p4`** — vocabulary CLOSED (§10.3), and one ledger obligation isolated
(`SeizeWdrlOfScoped`). Still owes: (a) SHAPE COVERAGE — the four arms are proved
at four PAIRWISE DISJOINT shapes (L1 @2500 K=1681, DT1 @2500 K=1257, DS1 @2500
K=1466, M1/M2 @900 K=784), so the field's `Shape` must be their disjunction and
there is no single theorem over a symbolic redeemer tag
(`WSC/SHAPING-RESULTS.md` §7); (b) a MINTING BUDGET BRIDGE AT 2500 — task U2
repointed `WSC.LR_BUDGET_minting` from the vacuous 600 prep to `appliedMinting900`
and DISCHARGED its non-vacuity, but 900 does not cover K = 1,257/1,466/1,681, so
the three non-burn arms need a bridge at the 2500 prep and `WithinBudget`'s
`K_mint` clause raised to match; (c) the SHAPE BRIDGE.

**`LeafSet.p2`.** `WSC/Props/Shaped/P2Shaped.lean` proves BOTH conjuncts over
SHAPE S1 at budget 3800 (witnesses K = 3004 / 3328). Missing: (a) the seize budget
bridge does not exist at all (`WSC.LR_BUDGET_seize` names the budget-600 prep and
there is deliberately no `K_seize`), so `WithinBudget` has no seize clause and the
route through §4's note (`LR_SEIZE_HALTS`) is the only one; (b) the shape bridge;
(c) a vocabulary reconciliation this task did not write, because P2Shaped's
conclusion is stated over SHAPE S1's scalars rather than over a `ScriptContext`'s
`txInfoOutputs`/`txInfoInputs`.

**`LeafSet.nopre`.** UNCHANGED — STILL-OPEN, and it is not a vocabulary problem.
It needs the FULL `LeafSet.p4` disjunction over a symbolic redeemer plus trace
induction (ARCHITECTURE.md §5.1 `L-mint-needs-reg`); no shaped theorem addresses
it. Nothing in this task moves it. -/

/-! # §9 DISCHARGE STATUS — what the library actually supplies, per hypothesis

Vocabulary (as `WSC/STATUS.md` §1): `PROVED-UNSHAPED` = a `by blaster` theorem over
the real bytecode quantified over `ScriptContext`, at a published budget, with a
non-vacuity witness; `PROVED-SHAPED(scope)` = the same but quantified over the
scalar leaves of a named SHAPE (BOTH bounds binding); `MODEL+AXIOM` = proved about a
source-cited transcription plus ONE `<model>_faithful` axiom; `STILL-OPEN` = not
proved anywhere.

## §9.1 The composition itself

| Item | Status |
|---|---|
| `covering_excludes_registeredIn` + `covering_node_excludes_registration` (`WSC/Honest.lean`) | **PROVED** — ADDENDUM E3's bridge, now a theorem; conjunct (iv) added to `DirWF` |
| `covering_excludes_ledger_registration` (this file) | **PROVED** from `DIRWF_L` |
| `mintOf_nonpos_of_not_mintPos`, `nonEscape_of_noEscape`, `valueOf_zero_of_not_hasCS`, the sum lemmas | **PROVED**, ordinary Lean |
| `baseNonVacuous` (`WSC.BaseNonVacuous`) | **PROVED** from `WSC.P3Witness` |
| `mintingNonVacuous` (`WSC.MintingNonVacuous`) | **PROVED** (task U2) from `WSC.P4Witness` + `blaster` on the concrete accept goal at `appliedMinting900.prop` |
| `WSC.GlobalNonVacuous` / `WSC.SeizeNonVacuous` | **STILL-OPEN** — see `WSC/Honest.lean`; global is dischargeable only at a SHAPED prep, seize at no affordable budget |
| `authenticDirNode_of_hasCSH`, `dirNodeFields_of_fromData`, `coveringIn_of_coveringRaw` (§7.1) | **PROVED** (task U2) — the raw↔ground-truth reconciliation of the exemption predicate, at a cost of `WSC.TS3` only |
| `coveringRaw_false_of_registered` (§7.1) | **PROVED** — registered ⟹ the leaves' RAW exemption is unavailable |
| `outSum_eq_sumOutsIf`, `inSum_eq_sumInsIf`, `contain_iff_modelSums` (§10.1) | **PROVED** — the sum vocabulary bridges |
| `leafP1_of_shapedGlobalContainment` (§10.2) | **PROVED** from `ShapedGlobalContainment` (which packages the shape bridge + the 4400 budget bridge) |
| `p4_disjuncts_of_custody` (§10.3) | **PROVED** from `WSC/Spec.lean`'s four-way disjunction + `SeizeWdrlOfScoped` |
| `merge_not_additive_without_canonicity` (§3.5) | **PROVED** (`native_decide`) — the counterexample that makes `CanonV` mandatory |
| `valueOf_withoutLovelace`, `sumInsIf_split`, `sumOutsIf_split`, `isBalanced_nonAda_eq` (§3.5b) | **PROVED**, ordinary Lean |
| `LR_BALANCE_SLOT_of_valueAlgebra` (§4) | **PROVED** from `WSC.LR7` + `ValueAlgebra` + `LedgerCanon` — the axiom's derivation, modulo two named `CardanoLedgerApi`-only residues |
| `p3_lifted` (P3 → "global or seize ran") | **PROVED** from `WSC.P3_base_requires_global_or_seize` (**PROVED-UNSHAPED**, K=600) + `LR_SPEND_RUNS_VALIDATOR` + `LR_BUDGET_base` + `LR_CTX` |
| `nonEscape_of_registered`, `preservation`, `top_claim` | **PROVED** from `LeafSet` + the axioms |

## §9.2 The four leaf hypotheses

**`LeafSet.p4` — STILL-OPEN.** The four-way disjunction over a fully symbolic
context is `Undetermined` after 3,208 s of Z3 (`WSC/Props/P4_Minting.lean`).
What exists: `WSC.P4a_shaped_mint_runs_minting_logic` and
`WSC.P4_burnonly_arm_shaped` / `WSC.P4_burn_only_shapedIdx` — **PROVED-SHAPED**
(SHAPE M1 / M2, K=900), i.e. ARM 4 ONLY. Arms 1-3 need K ≥ 1,257 / 1,681 and no
shape has been written for them; since shaped `#prep_uplc` is essentially
budget-independent (1.2 s at 1,700) this is unwritten work, not a wall.
ALSO REQUIRED even for arm 4: the minting budget bridge (§9.5) and the SHAPE
BRIDGE (§9.4).
*What V1/V2/V3 would discharge*: a shaped `Local`-arm theorem plus shaped
`DelegateTransfer`/`DelegateSeize` arms at K≈1,300/1,700 would let `p4` be
instantiated at `Shape :=` that shape's predicate — a one-line change here.

**`LeafSet.p1` — STILL-OPEN (and MODEL+AXIOM even when it lands).** P1 is
NOT-REACHABLE-AT-UPLC (containment-carrying accepts cost 3,262 / 3,726 CEK steps;
preps extrapolate to years). `WSC.Model.P1_bytecode` is the intended source, and it
is `WSC.Model.P1_model` + `WSC.Model.globalModel_faithful`; but `P1_model` is
itself a `Prop`, unproved — its links `L1_1a_pathA_sound`, `L1_1b_pathB_sound`,
`L1_2`…`L1_6` are all stated-not-proved. Only Path C
(`WSC.Model.pathC_sound`) and `accum_lookup` are proved.
ALSO REQUIRED: the raw↔ground-truth reconciliation of the exemption predicate
(`coveringNodeExists` vs `coveringIn`), which costs `WSC.TS3` + `WSC.TS5`, exactly
as `WSC.P5_groundtruth_of_indexed` does it for P5.
P6 is folded in: the SIGNED `Contain` already carries Member self-penalization, and
the self-penalization CORE is **PROVED** on the model
(`WSC.Model.mintWalk_sublist`, `mintWalk_member_retains`).

**UPDATE (task V1 landed at CLAB `bdbbb33`, after this file was written).**
`WSC/Props/Shaped/P1Shaped.lean` proves P1 in the SIGNED form
**at UPLC, `✅ Valid` at budget 4400, over SHAPES T1/T2/T6/T7, with NO faithfulness
axiom** (`#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]`). That
is the strongest available source for `LeafSet.p1` and it is a one-line
instantiation once FOUR gaps are closed, each of which is named here rather than
glossed:

1. **`Shape`** must be instantiated as "`ctx = p1ShapedCtx …` / `p1ShapedMintCtx …`
   for some scalars" (T1/T2/T6/T7). Only 1 of the 3 containment dispatch paths
   (Path A) and no input-side aggregation are covered — Blaster defect D6 blocks
   T3/T4/T5.
2. **The budget bound is 4400, not 1600 — FIXED BY TASK U2.** `WithinBudget`'s
   global clause used to be TOO TIGHT to admit the transactions P1_T1/T2/T6/T7 talk
   about (their witnesses cost 2,603 / 3,572 / 3,150 / 3,572 CEK steps).
   `WSC.K_global` is now **4400**, with its non-vacuity witness named in its
   docstring (`WSC.P1ShapedWitness.exec_accepts_unshaped` at 4400 on the UNSHAPED
   bytecode, plus the bracketing `K_T1_is_2603`), and `WSC.K_global_nonmember = 1600`
   is retained as the separate P5/covering-node sub-bound. So this gap is CLOSED.
3. **SHAPE BRIDGE** (§9.4): their conclusion is about
   `appliedGlobalShapedT2.prop <scalars>`; this field's trigger is
   `NodeAcceptsGlobal`, so both the shape bridge and a repointed
   `WSC.LR_BUDGET_global` (§9.5) are needed.
4. **Vocabulary — CLOSED BY TASK U2 (§10.1, §7.1).** They conclude in
   `WSC.Model.outSum`/`inSum`/`mintSigned` with the exemption stated as
   `Model.coveringNodeExists … = false` (raw `hasCSH` + 3-field `dirNodeFields`);
   this field speaks `outAtB`/`inAtB`/`WSC.mintOf` with `¬ WSC.coveringIn`
   (ground-truth `authenticDirNode` + full 5-field decode). Both bridges are now
   theorems: `outSum_eq_sumOutsIf` / `inSum_eq_sumInsIf` / `contain_iff_modelSums`
   (§10.1, trivial list inductions — the two transcriptions agree on the nose), and
   `coveringIn_of_coveringRaw` (§7.1). The reconciliation costs `WSC.TS3` ONLY, not
   `TS3 + TS5` as this list previously estimated: the `hasCSH ⟹ authenticDirNode`
   half is an ordinary lemma (`authenticDirNode_of_hasCSH`).
   `WSC.Model.mintSigned` needs NO bridge — it is definitionally `WSC.mintOf`.
   What remains for `p1` is items 1 and 3 only, packaged as the single field of
   `ShapedGlobalContainment` (§10.2).

**`LeafSet.p2` — STILL-OPEN in half, MODEL+AXIOM in the other.**
Seized policy: `WSC.P2.P2b_bytecode` is a `Prop` — STILL-OPEN (blocked on the two
bridges of `WSC/Props/P2_Seize.lean` §5, with machine-checked counterexamples
showing `ptokenPairsContain` is not pointwise sound without `validTxOutValue`).
Non-seized policies: `WSC.P2.P2a_bytecode` is **PROVED (MODEL+AXIOM,
`WSC.SeizeModel.seizeModel_faithful`, 13/13 golden differential incl. the rejecting
vector, and NOT budget-bounded)**, but the step "structure preserved ⟹ `Contain`
for a non-seized policy" is an UNWRITTEN lemma.
ALSO REQUIRED: `LR_SEIZE_HALTS` (§4's note).

**`LeafSet.nopre` — STILL-OPEN.** ARCHITECTURE.md §5.1's `L-mint-needs-reg`. The
route: before registration every positive-mint arm of the issuance policy fails
(arms 1-3 need a directory NFT proof, arm 4 forbids positive mint), so no token of
`cs` can exist; with `ts_genesis` and trace induction this gives
`OutOfBase L cs tn = 0`. It therefore depends on the FULL `LeafSet.p4`, arms 1-3
included — this is the weakest link in the set and the one nobody has started.

## §9.3 The axioms this file adds, and why each is not avoidable here

`LedgerStep`, `Genesis` (declared, not defined) · `lr_utxo_semantics` ·
`lr_inputs_in_ledger` · `lr_registration_source` · `LR_BALANCE_SLOT` ·
`ts_minting_identity_L` · `ts_genesis` · `NONNEG_L` · `DIRWF_L`.

All nine need the `Ledger` type, which is exactly why `WSC/Honest.lean` records
`ts_genesis` and `lr_utxo_semantics` as "belongs in `Composition.lean`" rather than
inventing them. Discharges: `ts_genesis` and `Genesis` — deployment audit;
`DIRWF_L` — **U10**; `ts_minting_identity_L` — deployment audit / U10;
`LR_BALANCE_SLOT` — a CLAB lemma (§9.5); the rest — trusting the Cardano ledger.

## §9.4 SHAPE BRIDGE — an obligation created by the shaped-context route

A shaped theorem such as `WSC.P5_shaped_indexed` quantifies over the scalar leaves
of `globalShapedCtx …` and speaks about `appliedGlobalShaped1600.prop <those
leaves>`. A `LeafSet` field speaks about a `ScriptContext` and (after §9.5b, at the
prep it names) about `globalProp pcs ctx`. Bridging the two needs

    isSuccessful (appliedXShaped.prop args) ↔ isSuccessful (appliedX.prop (shapedCtx args))

i.e. that prepping the SAME bytecode at the SAME budget with a partially
instantiated input agrees with prepping it symbolically and then instantiating. It
is expected to be true and it is NOT proved anywhere in the library. Any claim of
the form "the composition is discharged by the shaped leaves" must carry it.
(`WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped` is empirical evidence for one
concrete instance, not the general statement.)

## §9.5 THE THREE HYGIENE REPAIRS — STATUS AFTER TASK U2

**§9.5a MINTING BRIDGE — REPAIRED.** `WSC.LR_BUDGET_minting` and
`WSC.MintingNonVacuous` used to be stated over `appliedMinting.prop` — the
budget-600 prep, whose non-vacuity is MACHINE-CHECKED FALSE
(`WSC/Props/P4_Minting.lean` `minting600_is_vacuous`; the cheapest accepting run
costs 784 steps) — while `K_mint = 900` and every P4 theorem lives on
`appliedMinting900`. Both are now pointed at `appliedMinting900.prop`, and the
non-vacuity hypothesis is DISCHARGED as the theorem `mintingNonVacuous` (§7). The
bridge is therefore USABLE for the first time. It still does not cover P4's three
non-burn arms (K = 1,257 / 1,466 / 1,681 > 900) — §10.5.

**§9.5b GLOBAL BRIDGE — REPAIRED IN SHAPE, STILL NOT INSTANTIABLE.**
`WSC.LR_BUDGET_global` used to name `appliedGlobal.prop` (budget 600, its own
probe `Valid` for "vacuous") while quoting `K_global`. Repointing it at ONE prep
cannot work, because the global theorems live at THREE budgets (1600 for P5, 3300
for P6/SHAPE G6, 4400 for P1's four shapes) and `K_global` is now 4400. It is
therefore **PREP-PARAMETRIC**: it takes the prepped term and its budget as
arguments, with a `WSC.GlobalPreppedAt globalProp K` side condition discharged by
inspection of the `#prep_uplc` line at each use site. That removes the mismatch by
construction. What it does NOT do is make the bridge instantiable at the shaped
preps: that needs the SHAPE BRIDGE (§9.4), and the named TODO is recorded in
`WSC.LR_BUDGET_global`'s docstring. `WSC.GlobalNonVacuous` is likewise parametric
and remains UNDISCHARGED at every unshaped prep — at 1600 the symbolic certificate
did not return in 87 minutes, and `exec` acceptance does not transfer to `prop`
(two separate terms, `PlutusCore/UPLC/PreProcess.lean:43-46`).
COST OF THE REPAIR, stated: ONE new abstract declaration, `WSC.GlobalPreppedAt`.

**§9.5c `LR_BALANCE_SLOT` — DERIVED, axiom retained pending two residues.**
`LR_BALANCE_SLOT_of_valueAlgebra` (§4) proves the axiom's exact statement from
`WSC.LR7` plus `ValueAlgebra` (§3.5, three `valueOf`/`merge` facts) and
`LedgerCanon` (§4, canonicity of a real transaction's values). Neither residue
mentions a validator, a budget or `OnChain`-beyond-LR1/LR2/LR3; both are
`CardanoLedgerApi`-only. The axiom is retained ONLY because the residues are
uninstantiated, and its docstring says how to delete it.
WHY THE RESIDUE IS NOT A ONE-LINER, and this is the finding: `valueOf` is **NOT**
additive over `merge` — `merge_not_additive_without_canonicity` (§3.5) is a
`native_decide` counterexample on two 1-entry/2-entry values — so the derivation
must carry the `CanonV` sortedness predicate and `merge` must be shown to preserve
it (because `valueSpent` folds `merge` over every input). CLAB supplies NO lemma
relating `valueOf` to `merge`/`withoutLovelace`/`valueSpent`/`valueProduced`; the
analogous development exists one layer down for PCB's CIP-153 `ValueRep`
(`PlutusCore/Value/Algebra.lean` `unionInner_lookup` :561-660,
`unionOuter_lookup` :809-910, `unionInner_sortedFrom` :493-561,
`unionOuter_sortedFrom` :746-809 — ~330 lines) and is the template, but is not
reusable directly because `merge`/`valueOf` on `List (Data × Data)` and
`unionOuter`/`lookupCoin` on `ValueRep` are different functions.

## §9.6 Two findings this file records in code

* `I`'s docstring: the invariant is FALSE without `cs ≠ adaSymbol`, because the
  directory HEAD SENTINEL is keyed `""` = `adaSymbol`, so `RegisteredIn hp L ""`
  holds in every live deployment.
* `WSC.dirPreState`'s docstring (`WSC/Honest.lean`): the interval non-overlap
  conjunct must be stated over the PRE-STATE snapshot. Over `dirCandidates` (which
  includes the outputs) it is FALSE for every directory INSERT, since the insert
  produces a node keyed `cs` while the SPENT node it splits still shows
  `key < cs < next`. -/

/-! ## §9.7 AXIOM AUDIT — printed at build time so the trust base cannot drift

Read the build log. Expected:

* the §3 lemmas: the standard Lean axioms only (`propext`, `Classical.choice`,
  `Quot.sound`) — no `sorry`, no `WSC/Honest.lean` axiom.
* `covering_excludes_ledger_registration`: adds `LedgerStep`,
  `lr_inputs_in_ledger` and nothing else.
* `p3_lifted`: adds `WSC.OnChain`, `WSC.Deployed`, `WSC.LR_SPEND_RUNS_VALIDATOR`,
  `WSC.LR_BUDGET_base`, `WSC.LR_CTX`, `WSC.NodeAcceptsBase`, `WSC.nodeStepsBase`
  — and **`sorryAx`**, because `WSC.P3_base_requires_global_or_seize` is closed by
  `blaster`, which discharges a `Valid` goal via `admit`
  (`WSC/SPIKE-FINDINGS.md`; the `sorry` warnings on blaster-proved theorems are
  expected and whitelisted). Every theorem below that consumes P3 inherits it.
  This is the standing property of the whole library, not something introduced
  here, but it must be stated wherever a composed result is quoted.
* `preservation` / `top_claim`: the union of the above with the §4/§8 axioms and
  `WSC.NONNEG`, `WSC.LR_MINT_RUNS_POLICY`, `WSC.LR_WDRL_RUNS_VALIDATOR`. NO
  `<model>_faithful` axiom appears — the source-model route enters only when a
  `LeafSet` field is instantiated.

TASK U2 CHANGES TO THE CENSUS, before/after:

* **NO axiom was added to `top_claim`'s list and none was removed.** The
  hygiene repairs are all inside axioms `top_claim` does not reach
  (`LR_BUDGET_minting`, `LR_BUDGET_global`, the `*NonVacuous` predicates), or are
  new theorems.
* `WSC.GlobalPreppedAt` is a NEW abstract declaration in `WSC/Honest.lean`
  (§9.5b). It does NOT appear in `top_claim`'s list, because nothing in §7 uses the
  global budget bridge.
* `mintingNonVacuous` (§7) adds `Lean.ofReduceBool` / `Lean.trustCompiler`
  (`native_decide` on `P4Witness.ctx_valid`) and `sorryAx` (`blaster`'s `admit`) —
  the same three `baseNonVacuous` already contributes, so `top_claim`'s list is
  unchanged. `mintingNonVacuous` is not reached by `top_claim` at all.
* the §7.1 reconciliation theorems add `WSC.TS3` (plus `WSC.Deployed`/`WSC.OnChain`)
  — visible in `coveringIn_of_coveringRaw`'s own census below, and NOT in
  `top_claim`'s, because §7 discharges the exemption premise through
  `covering_excludes_ledger_registration` / `DIRWF_L` instead.
* `LR_BALANCE_SLOT_of_valueAlgebra` depends on `WSC.LR7` (and `WSC.OnChain`) and
  NOT on `LR_BALANCE_SLOT` — that is the point of it.

MEASURED at this revision, `top_claim` depends on exactly:

    propext, sorryAx, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler,
    Quot.sound,
    WSC.Deployed, WSC.OnChain,
    WSC.LR_BUDGET_base, WSC.LR_CTX, WSC.LR_MINT_RUNS_POLICY,
    WSC.LR_SPEND_RUNS_VALIDATOR, WSC.LR_WDRL_RUNS_VALIDATOR, WSC.NONNEG,
    WSC.NodeAcceptsBase, WSC.NodeAcceptsGlobal, WSC.NodeAcceptsMinting,
    WSC.NodeAcceptsSeize, WSC.mlhPolicyId,
    WSC.nodeStepsBase, WSC.nodeStepsGlobal, WSC.nodeStepsMinting,
    WSC.Composition.{DIRWF_L, Genesis, LR_BALANCE_SLOT, LedgerStep, NONNEG_L,
      lr_inputs_in_ledger, lr_registration_source, lr_utxo_semantics, ts_genesis,
      ts_minting_identity_L}

Three observations that belong in any published summary:
* `sorryAx` is `blaster`'s `admit` inside `WSC.P3_base_requires_global_or_seize`,
  reached through `p3_lifted`;
* `Lean.ofReduceBool` / `Lean.trustCompiler` are the `native_decide` compiler-trust
  axioms, reached through `baseNonVacuous` (the concrete accepting witness's
  `ctx_valid`);
* `WSC.DIRWF` and `WSC.TS_MINTING_IDENTITY` do NOT appear: the composition uses
  their LEDGER-level counterparts `DIRWF_L` and `ts_minting_identity_L`. Both sets
  have the same discharge (U10 / deployment audit), and `WSC.DIRWF` is what makes
  the per-transaction bridge `WSC.covering_node_excludes_registration` available to
  the leaf proofs. -/
#print axioms WSC.Composition.mintOf_nonpos_of_not_mintPos
#print axioms WSC.Composition.nonEscape_of_noEscape
#print axioms WSC.Composition.sumHoldU_elim
#print axioms WSC.covering_node_excludes_registration
#print axioms WSC.Composition.covering_excludes_ledger_registration
#print axioms WSC.Composition.baseNonVacuous
#print axioms WSC.Composition.mintingNonVacuous
#print axioms WSC.Composition.authenticDirNode_of_hasCSH
#print axioms WSC.Composition.dirNodeFields_of_fromData
#print axioms WSC.Composition.coveringIn_of_coveringRaw
#print axioms WSC.Composition.coveringRaw_false_of_registered
#print axioms WSC.Composition.merge_not_additive_without_canonicity
#print axioms WSC.Composition.valueOf_withoutLovelace
#print axioms WSC.Composition.isBalanced_nonAda_eq
#print axioms WSC.Composition.LR_BALANCE_SLOT_of_valueAlgebra
#print axioms WSC.Composition.outSum_eq_sumOutsIf
#print axioms WSC.Composition.contain_iff_modelSums
#print axioms WSC.Composition.leafP1_of_shapedGlobalContainment
#print axioms WSC.Composition.p4_disjuncts_of_custody
#print axioms WSC.Composition.p3_lifted
#print axioms WSC.Composition.nonEscape_of_registered
#print axioms WSC.Composition.preservation
#print axioms WSC.Composition.top_claim
#print axioms WSC.Composition.no_programmable_tokens_outside_mini_ledger

end WSC.Composition

