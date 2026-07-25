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
   CEK step bounds `K_base = 600`, `K_mint = 900`, `K_global = 1600`
   (`WSC/Honest.lean`). No result here covers unboundedly large transactions.
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

namespace WSC.Composition

open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo ScriptHash TxInInfo TxOutRef
                          hasCurrencySymbol valueOf credentialInWithdrawals
                          validSpendingContext validScriptContext)
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

STATUS, honestly: this is the per-slot PROJECTION of `WSC/Honest.lean`'s `LR7`
(`isBalanced ctx`, `CardanoLedgerApi/V3/Contexts.lean:1185-1189`, whose non-ada
conjunct is `merge (withoutLovelace (valueSpent ctx)) txInfoMint ==
withoutLovelace (valueProduced ctx)`). Deriving it from `LR7` is a mechanical but
UNWRITTEN CLAB lemma (`valueOf` distributes over `merge`, `valueSpent`/
`valueProduced` split along the payment-credential filter). It is therefore
stated here as an axiom and listed in §9 as `CLAB-LEMMA-PENDING`, not claimed as
proved. -/
axiom LR_BALANCE_SLOT :
  ∀ (ctx : ScriptContext) (base : Credential) (cs : CurrencySymbol) (tn : TokenName),
    WSC.OnChain ctx → cs ≠ adaSymbol →
      inAtB base cs tn ctx + inOff base cs tn ctx
        + WSC.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint
      = outAtB base cs tn ctx + outOff base cs tn ctx

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
`WSC/Honest.lean` (`K_base = 600`, `K_mint = 900`, `K_global = 1600`), whichever
purpose it is invoked under.

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
* for MINTING, `WSC.LR_BUDGET_minting` names `appliedMinting.prop` — the budget-600
  prep whose non-vacuity is MACHINE-CHECKED FALSE (`WSC/Props/P4_Minting.lean`
  `minting600_is_vacuous`), while the theorems live on `appliedMinting900`. So the
  bridge cannot be applied at all until that axiom is repointed (§9.5, a one-line
  repair in `WSC/Honest.lean`);
* for GLOBAL, `WSC.LR_BUDGET_global` names `appliedGlobal.prop` (budget 600,
  probe-Valid vacuous) while P5 lives on `appliedGlobalShaped1600`;
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
concrete witness (`WSC/Props/P3_Base.lean`). This is the only one of the four
`*NonVacuous` obligations of `WSC/Honest.lean` that is dischargeable today, and it
is what makes `WSC.LR_BUDGET_base` usable below. -/
theorem baseNonVacuous : WSC.BaseNonVacuous :=
  ⟨WSC.P3Witness.globalCred, WSC.P3Witness.seizeCred, WSC.P3Witness.ctx,
   WSC.P3Witness.ctx_valid, WSC.P3Witness.prop_accepts⟩

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
   published CEK step bounds `K_base = 600`, `K_mint = 900`, `K_global = 1600`.
   Nothing here covers unboundedly large transactions. There is no `K_seize`.
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
   `LR_BALANCE_SLOT` is the only one that is a MECHANICAL CONSEQUENCE of an
   existing axiom (`WSC.LR7` / `isBalanced`) rather than a primitive ledger fact:
   the derivation is unwritten (§9.5).
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
| `baseNonVacuous` (`WSC.BaseNonVacuous`) | **PROVED** from `WSC.P3Witness` — the only one of the four `*NonVacuous` obligations dischargeable today |
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
2. **The budget bound is 4400, not `WSC.K_global = 1600`.** `WithinBudget`'s global
   clause as written is TOO TIGHT to admit the transactions P1_T1/T2/T6/T7 talk
   about (their witnesses cost 2,603 / 3,572 / 3,150 / 3,572 CEK steps). `K_global`
   must be republished at ≥ 4400 with its own non-vacuity witness before the
   composition can consume them.
3. **SHAPE BRIDGE** (§9.4): their conclusion is about
   `appliedGlobalShapedT2.prop <scalars>`; this field's trigger is
   `NodeAcceptsGlobal`, so both the shape bridge and a repointed
   `WSC.LR_BUDGET_global` (§9.5) are needed.
4. **Vocabulary**: they conclude in `WSC.Model.outSum`/`inSum`/`mintSigned` with the
   exemption stated as `Model.coveringNodeExists … = false` (raw `hasCSH` +
   2-field `dirNodeFields`); this field speaks `outAtB`/`inAtB`/`WSC.mintOf` with
   `¬ WSC.coveringIn` (ground-truth `authenticDirNode` + full 5-field decode). Two
   small bridges: `outSum ≡ sumOutsIf (atBaseB …)` (a list induction) and the
   raw↔ground-truth node reconciliation (`WSC.TS3` + `WSC.TS5`, as
   `WSC.P5_groundtruth_of_indexed` does it for P5).

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
leaves>`. A `LeafSet` field speaks about a `ScriptContext` and (after §9.5) about
`appliedGlobal1600.prop pcs ctx`. Bridging the two needs

    isSuccessful (appliedXShaped.prop args) ↔ isSuccessful (appliedX.prop (shapedCtx args))

i.e. that prepping the SAME bytecode at the SAME budget with a partially
instantiated input agrees with prepping it symbolically and then instantiating. It
is expected to be true and it is NOT proved anywhere in the library. Any claim of
the form "the composition is discharged by the shaped leaves" must carry it.
(`WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped` is empirical evidence for one
concrete instance, not the general statement.)

## §9.5 TWO REPAIRS THIS FILE DOES NOT MAKE (reported, not patched)

1. **`WSC.LR_BUDGET_minting` / `WSC.MintingNonVacuous` name the wrong prep.** Both
   are stated over `appliedMinting.prop` — the budget-600 prep, whose non-vacuity
   is MACHINE-CHECKED FALSE (`WSC/Props/P4_Minting.lean` `minting600_is_vacuous`;
   the cheapest accepting run costs 784 steps) — while `K_mint = 900` and every P4
   theorem lives on `appliedMinting900` / `appliedMintShaped900`. As written the
   axiom cannot be applied to anything, so the minting budget bridge does not
   exist yet. Repair: repoint both to `appliedMinting900` (one line each). The same
   mismatch holds for `WSC.LR_BUDGET_global` / `WSC.GlobalNonVacuous`
   (`appliedGlobal.prop`, budget 600, probe-Valid vacuous) versus
   `appliedGlobal1600` / `appliedGlobalShaped1600`. This is why §6 puts every leaf
   trigger at `NodeAccepts*` and does the budget plumbing ONLY for the base
   validator, where the bridge genuinely closes.
2. **`LR_BALANCE_SLOT` should be a theorem, not an axiom.** It is the per-slot
   projection of `WSC.LR7` (`isBalanced`,
   `CardanoLedgerApi/V3/Contexts.lean:1185-1189`). Deriving it needs `valueOf`
   distributing over `V2.merge` and `valueSpent`/`valueProduced` splitting along
   the payment-credential filter — mechanical CLAB work, unwritten. Listed as
   CLAB-LEMMA-PENDING.

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
#print axioms WSC.Composition.p3_lifted
#print axioms WSC.Composition.nonEscape_of_registered
#print axioms WSC.Composition.preservation
#print axioms WSC.Composition.top_claim
#print axioms WSC.Composition.no_programmable_tokens_outside_mini_ledger

end WSC.Composition

