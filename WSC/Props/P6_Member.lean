-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Props/P6_Member.lean — P6 (Member self-penalization) on the source model of
the global transfer validator (task Z4 step 3).

P6 in plain English: *if a policy is classified `Member` during a transfer, its
newly minted amount is ADDED to the amount that must remain inside the
mini-ledger — never subtracted.  Claiming Member can only make the containment
obligation harder to satisfy, so the claim is self-penalizing and cannot be
abused.*

The formal core of that sentence is a statement about
`pcheckMintLogicAndGetProgrammableValue` (`ProgrammableLogicBase.hs:976-1026`),
and it is PROVED below in two parts:

* `mintWalk_sublist` — the programmable mint value the walk returns is an
  ORDER-PRESERVING SUBLIST of `txInfoMint`.  Every entry is carried over
  BYTE-FOR-BYTE (same currency-symbol key `Data`, same token-map `Data`, hence
  the same ledger-truth quantities, which the attacker cannot inflate); the walk
  can only DROP entries, and it has no arithmetic on quantities at all — so no
  quantity can be negated, halved, or otherwise turned into a subtraction.
* `mintWalk_member_retains` — a `Member` proof retains its entry, and it does so
  without touching a directory node: no index, no datum decode, no
  authentication, no transfer-logic invocation (the §11.3 deletion, source
  comment :966-969).  So a Member claim is free to make but strictly enlarges the
  requirement.

The remaining link from "the entry is in the programmable mint value" to
"`outAtBase ≥ mintPos`" is the `csPairsUnion`/`filterPositiveCurrencyPairs`/
containment chain shared with P1; its status is recorded in
`WSC/Props/P1_Transfer.lean`'s OBLIGATION STATUS block.
-/
import WSC.Props.P1_Transfer

namespace WSC.Model

open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext TxInInfo valueOf)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-! ## L6.1 — the mint walk only ever DROPS entries -/

/-- **L6.1 (verbatim-or-dropped).**  Every successful run of the mint lockstep
walk returns the accumulator, reversed, followed by an ORDER-PRESERVING SUBLIST
of the transaction's mint entries.  Two consequences, both load-bearing for P6:

1. every retained entry is byte-identical to the ledger's own mint entry
   (`Sublist` is on the raw `(Data × Data)` pairs), so its quantities are
   ledger truth — the redeemer cannot inflate them;
2. the walk contains no quantity arithmetic whatsoever, so a classification can
   only REMOVE a policy from the requirement, never flip its sign. -/
theorem mintWalk_sublist (dirCS : CurrencySymbol) (refs : List TxInInfo) :
    ∀ (mint : CsPairs) (proofs : List MintProof) (acc res : CsPairs),
      mintWalk dirCS refs proofs mint acc = some res →
      ∃ sub : CsPairs, sub.Sublist mint ∧ res = acc.reverse ++ sub := by
  intro mint
  induction mint with
  | nil =>
      intro proofs acc res h
      cases proofs with
      | nil =>
          simp only [mintWalk, Option.some.injEq] at h
          exact ⟨[], List.Sublist.refl _, by simp [← h]⟩
      | cons p ps => simp only [mintWalk] at h; exact absurd h (by simp)
  | cons e rest ih =>
      intro proofs acc res h
      obtain ⟨csD, tnsD⟩ := e
      cases proofs with
      | nil => simp only [mintWalk] at h; exact absurd h (by simp)
      | cons p ps =>
          cases csD with
          | B currCS =>
              cases p with
              | Member =>
                  simp only [mintWalk] at h
                  obtain ⟨sub, hsub, hres⟩ := ih ps ((Data.B currCS, tnsD) :: acc) res h
                  refine ⟨(Data.B currCS, tnsD) :: sub, hsub.cons₂ _, ?_⟩
                  simpa using hres
              | NonMember nodeIdx =>
                  simp only [mintWalk] at h
                  cases hn : dirNodeAt nodeIdx refs with
                  | none => simp only [hn] at h; exact absurd h (by simp)
                  | some t =>
                      obtain ⟨nodeVal, nodeKey, nodeNext, _⟩ := t
                      simp only [hn] at h
                      cases hc : hasCSH dirCS nodeVal with
                      | none => simp only [hc] at h; exact absurd h (by simp)
                      | some authentic =>
                          simp only [hc] at h
                          by_cases hok :
                              (decide (nodeKey < currCS) && decide (currCS < nodeNext)
                                && authentic) = true
                          · rw [if_pos hok] at h
                            obtain ⟨sub, hsub, hres⟩ := ih ps acc res h
                            exact ⟨sub, hsub.cons _, hres⟩
                          · rw [if_neg hok] at h; exact absurd h (by simp)
          | _ => simp only [mintWalk] at h; exact absurd h (by simp)

/-- **L6.1 (top-level form).**  The programmable mint value the validator merges
into the expected output value is an order-preserving sublist of `txInfoMint`. -/
theorem mintWalk_result_sublist (dirCS : CurrencySymbol) (refs : List TxInInfo)
    (proofs : List MintProof) (mint : CsPairs) (res : CsPairs)
    (h : mintWalk dirCS refs proofs mint [] = some res) :
    res.Sublist mint := by
  obtain ⟨sub, hsub, hres⟩ := mintWalk_sublist dirCS refs mint proofs [] res h
  simpa [hres] using hsub

/-- **L6.2 (Member retains, and pays nothing for it).**  When the head mint entry
is classified `Member`, that entry appears — verbatim — as the head of the
programmable mint value.  The proof consumes no directory node, which is exactly
why the claim is FREE to make and therefore has to be self-penalizing to be safe.
-/
theorem mintWalk_member_retains (dirCS : CurrencySymbol) (refs : List TxInInfo)
    (ps : List MintProof) (csD tnsD : Data) (rest : CsPairs) (res : CsPairs)
    (h : mintWalk dirCS refs (.Member :: ps) ((csD, tnsD) :: rest) [] = some res) :
    ∃ tail : CsPairs, res = (csD, tnsD) :: tail ∧ tail.Sublist rest := by
  cases csD with
  | B currCS =>
      simp only [mintWalk] at h
      obtain ⟨sub, hsub, hres⟩ :=
        mintWalk_sublist dirCS refs rest ps [(Data.B currCS, tnsD)] res h
      exact ⟨sub, by simpa using hres, hsub⟩
  | _ => simp only [mintWalk] at h; exact absurd h (by simp)

/-! ## P6 — the statement, and what remains

`mintWalk_result_sublist` + `mintWalk_member_retains` establish the
SELF-PENALIZATION content of P6 outright: the Member arm adds the ledger-truth
mint entry to the programmable mint value and the walk can do nothing else with
it.  The step from there to the ARCHITECTURE.md §3-P6 inequality
`outAtBase base cs tn ≥ mintPos cs tn` needs the two shared links recorded in
`WSC/Props/P1_Transfer.lean` (`L1_2_union_adds`, `L1_6_filter_preserves_positive`)
plus L1.1, so P6's inequality form is stated there as `P6_model`. -/

end WSC.Model
