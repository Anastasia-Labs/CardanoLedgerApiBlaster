/-
WSC/Props/P1_Transfer.lean — P1 (containment) on the source model of the global
transfer validator (task Z4 step 3), plus the ONE faithfulness axiom that
connects the model to the production bytecode (step 4).

READ THE "OBLIGATION STATUS" BLOCK AT THE BOTTOM before citing anything from
this file.  Some links in P1's chain are PROVED here; the rest are recorded as
explicit `Prop` definitions with their status, exactly as `WSC/Props/P4_Minting.lean`
and `WSC/Props/P5_NonMember.lean` record their un-discharged bytecode
obligations.  Nothing is claimed that is not machine-checked.

WHY A MODEL AT ALL (ADDENDUM E2/E10, `WSC/STATUS.md` §1 P1 row).  P1 is
unreachable at UPLC: the containment-carrying accepting runs cost 3,262 and 3,726
CEK steps, symbolic `#prep_uplc` at 3,300 never completes, and at the affordable
budget 1,600 every bytecode obligation over a fully symbolic `Data`
ScriptContext comes back Undetermined even with 3,300 s of Z3
(`WSC/Props/P5_NonMember.lean`).  ARCHITECTURE.md §2 B3 is the sanctioned
fallback, with **one** explicit `_faithful` axiom and golden cross-checks — which
is what this file ships.
-/
import WSC.Model.Ground
import WSC.Prep.Global1600
import WSC.Model.GlobalGoldens
import WSC.Honest

namespace WSC.Model

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext TxInInfo valueOf validTxOutValue)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.Value (ValueRep valueSorted lookupCoin lookupDataOuter lookupData
                       unValueData unionValue valueContains
                       unValueData_lookup unValueData_normalized valueNormalized_sorted
                       lookupCoin_unionValue unionValue_sorted valueContains_iff)

/-! ## L1.1 — CONTAINMENT SOUNDNESS

ARCHITECTURE.md Tier 3.1 (binding): `poutputsContainExpectedValueAtCred` has
THREE dispatch paths and each must INDEPENDENTLY imply the aggregate per-asset
containment, because the source comment at `ProgrammableLogicBase.hs:560`
asserting their equivalence is not a theorem.  The three sub-results below are
therefore stated and proved (or recorded) separately. -/

/-! ### L1.1c — Path C, the builtin `valueContains` path (:619-647)

This is the general path, and the one the whole CIP-153 builtin apparatus was
built for: it is discharged entirely through PROVED lemmas of
`PlutusCore/Value/Algebra.lean` (`lookupCoin_unionValue`, `unionValue_sorted`,
`valueContains_iff`, `unValueData_lookup`, `unValueData_normalized`), so the
containment arithmetic bottoms out in the REAL builtin denotations the CEK
machine runs — not in an invented abstraction. -/

/-- The accumulation `accumulateOutputsAtCred` (:628-643) computes, slot by slot,
exactly the ground-truth sum of the base outputs' quantities — and preserves
sortedness, so the algebra lemmas chain over the iterated unions. -/
theorem accum_lookup (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    ∀ (outs : List TxOut) (acc outV : ValueRep),
      valueSorted acc = true →
      accumOutputsAtCred base acc outs = some outV →
      valueSorted outV = true ∧
      lookupCoin cs tn outV = lookupCoin cs tn acc + outSumLk base cs tn outs := by
  intro outs
  induction outs with
  | nil =>
      intro acc outV hs h
      simp only [accumOutputsAtCred, Option.some.injEq] at h
      subst h
      exact ⟨hs, by simp [outSumLk]⟩
  | cons o rest ih =>
      intro acc outV hs h
      simp only [accumOutputsAtCred] at h
      by_cases hb : (WSC.payCred o == base) = true
      · rw [if_pos hb] at h
        cases hv : unVD o.txOutValue with
        | none => simp only [hv] at h; exact absurd h (by simp)
        | some v =>
            simp only [hv] at h
            cases hu : unionValue acc v with
            | none => simp only [hu] at h; exact absurd h (by simp)
            | some acc' =>
                simp only [hu] at h
                have hvs : valueSorted v = true :=
                  valueNormalized_sorted (unValueData_normalized hv)
                have hsl : lookupCoin cs tn acc' = lookupCoin cs tn acc + lookupCoin cs tn v :=
                  lookupCoin_unionValue hs hvs hu cs tn
                have hacc' : valueSorted acc' = true := unionValue_sorted hs hvs hu
                have hlk : lookupCoin cs tn v = lookupDataOuter cs tn o.txOutValue := by
                  have := unValueData_lookup hv cs tn
                  simpa [lookupData] using this
                obtain ⟨h1, h2⟩ := ih acc' outV hacc' h
                refine ⟨h1, ?_⟩
                rw [h2, hsl, hlk]
                simp only [outSumLk, if_pos hb]
                exact Int.add_assoc _ _ _
      · rw [if_neg hb] at h
        obtain ⟨h1, h2⟩ := ih acc outV hs h
        refine ⟨h1, ?_⟩
        rw [h2]
        simp only [outSumLk, if_neg hb]
        simp

/-- **L1.1c (Path C is containment-sound).**  If the builtin `valueContains` path
accepts, then for EVERY asset slot the expected quantity is at most the sum of
that asset at the mini-ledger base outputs — the ground-truth aggregate. -/
theorem pathC_sound (base : Credential) (outs : List TxOut) (expected : CsPairs)
    (h : checkByBuiltinContains base outs expected = some true) :
    ∀ (cs : CurrencySymbol) (tn : TokenName),
      lookupDataOuter cs tn expected ≤ outSumLk base cs tn outs := by
  intro cs tn
  simp only [checkByBuiltinContains] at h
  cases hz : unVD ([] : Value) with
  | none => simp only [hz] at h; exact absurd h (by simp)
  | some z =>
      simp only [hz] at h
      cases ha : accumOutputsAtCred base z outs with
      | none => simp only [ha] at h; exact absurd h (by simp)
      | some outV =>
          simp only [ha] at h
          cases he : unVD expected with
          | none => simp only [he] at h; exact absurd h (by simp)
          | some expV =>
              simp only [he] at h
              have hzs : valueSorted z = true :=
                valueNormalized_sorted (unValueData_normalized hz)
              have hes : valueSorted expV = true :=
                valueNormalized_sorted (unValueData_normalized he)
              obtain ⟨_, hout⟩ := accum_lookup base cs tn outs z outV hzs ha
              obtain ⟨_, _, hcon⟩ := (valueContains_iff hes).mp h
              have hz0 : lookupCoin cs tn z = 0 := by
                have : z = [] := by
                  simpa [unVD, unValueData, PlutusCore.Value.unValueDataCurrencies,
                         Option.some.injEq] using hz.symm
                simp [this, lookupCoin]
              have hexp : lookupCoin cs tn expV = lookupDataOuter cs tn expected := by
                have := unValueData_lookup he cs tn
                simpa [lookupData] using this
              have := hcon cs tn
              rw [hexp, hout, hz0] at this
              simpa using this

/-! ### L1.1a / L1.1b — Paths A and B

Path A (single-asset accumulate-scan, :604-618) and Path B (wholesale `Data`
equality, :648-674) both depend on LEDGER CANONICITY of the output values —
`validTxOutValue` (`CardanoLedgerApi/V1/Contexts.lean:769-784`), which
`validRewardingContext` asserts via `validOutputs`
(`CardanoLedgerApi/V3/Contexts.lean:1073`):

* Path A's `passetQtyInValue` (:570-603) is a SORTED early-exit lookup
  (`cs #< currencySymbol ⟹ 0`), so it equals the ground-truth linear lookup only
  on a currency-sorted value; on an unsorted value it under-reports, and the
  theorem would be false without the hypothesis.
* Path B compares the output value with its FIRST entry dropped
  (`ptail # (pasMap # txOutValueData)`, :667) against the expected map, so it
  needs ada-first to conclude anything about a non-ada asset, and it needs
  non-negativity of the OTHER base outputs to lift one output's contribution to
  the aggregate sum.

Both are stated below as `Prop` definitions with their status recorded; neither is
proved in this session (see OBLIGATION STATUS). -/

/-- **L1.1a (Path A is containment-sound)** — STATED, NOT PROVED (see OBLIGATION
STATUS §A).  Hypotheses are exactly the ledger canonicity `validRewardingContext`
already gives. -/
def L1_1a_pathA_sound : Prop :=
  ∀ (base : Credential) (outs : List TxOut) (cs : CurrencySymbol) (tn : TokenName)
    (q : Integer),
    (∀ o ∈ outs, validTxOutValue o.txOutValue = true) →
    hasAtLeastAsset base q cs tn 0 outs = some true →
    q ≤ outSumLk base cs tn outs

/-- **L1.1b (Path B is containment-sound)** — STATED, NOT PROVED (see OBLIGATION
STATUS §A). -/
def L1_1b_pathB_sound : Prop :=
  ∀ (base : Credential) (outs : List TxOut) (expected : CsPairs)
    (cs : CurrencySymbol) (tn : TokenName),
    cs ≠ ByteString.mk "" →
    (∀ o ∈ outs, validTxOutValue o.txOutValue = true) →
    checkWholesaleThenBuiltin base outs expected outs = some true →
    lookupDataOuter cs tn expected ≤ outSumLk base cs tn outs


/-! ## Ground-truth mint quantities (ARCHITECTURE.md §3) -/

/-- Signed minted quantity of `(cs, tn)` — ground truth, `txInfoMint` lookup.
(Same as `WSC.mintOf`; restated here so the P1 statement reads in one
vocabulary.) -/
def mintSigned (cs : CurrencySymbol) (tn : TokenName) (mint : MintValue) : Integer :=
  valueOf cs tn mint

/-- Positive part of the minted quantity (ARCHITECTURE.md §3 `mintPos`). -/
def mintPosOf (cs : CurrencySymbol) (tn : TokenName) (mint : MintValue) : Integer :=
  let m := mintSigned cs tn mint
  if m > 0 then m else 0

/-! ## The escape hypothesis: no covering directory node for `cs`

Both lockstep walks exempt a policy in exactly one way: by exhibiting a
reference input that is `phasCSH`-authenticated for `directoryNodeCS` and whose
datum's `(key, next)` interval STRICTLY covers the symbol
(transfer walk :891-908, mint walk :996-1016).  So the hypothesis that turns
"registered" into "cannot be exempted" is precisely the negation of that. -/

/-- Some reference input is a `phasCSH`-authenticated directory node whose
`(key, next)` interval strictly covers `cs`.  Ground truth: a pure function of
`txInfoReferenceInputs` and their datums. -/
def coveringNodeExists (dirCS : CurrencySymbol) (cs : CurrencySymbol) :
    List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeFields d with
            | some (k, n, _) =>
                decide (k < cs) && decide (cs < n) &&
                  (hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || coveringNodeExists dirCS cs rest

/-- **⚠️ SUPERSEDED (task U3 audit, 2026-07-25) — the finding below WAS acted on;
this `Prop` is kept only as the historical record of the gap.**

WHAT CHANGED. Task V4 added the missing INTERVAL conjunct as `DirWF`'s **fourth**
conjunct (`WSC/Honest.lean`, ADDENDUM E4), and the bridge that consumes it is now
a PROVED THEOREM, not an obligation:

* `WSC.covering_node_excludes_registration` (`WSC/Honest.lean:1337`) —
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` only, i.e. it is
  a kernel-checked consequence of the strengthened `DirWF`;
* `WSC.Composition.covering_excludes_ledger_registration`
  (`WSC/Composition.lean:1105`) — the ledger-level half, from `DIRWF_L`;
* `WSC.Composition.coveringRaw_false_of_registered` (task U2, §7.1) — closes the
  gap in the exact RAW vocabulary the theorems below use
  (`Model.coveringNodeExists`), at a cost of `WSC.TS3` and the two ledger axioms
  `LedgerStep` / `lr_inputs_in_ledger`, and NOT `WSC.TS5`.

WHAT REMAINS TRUE. `DirWF`/`DIRWF_L` are still AXIOMS (escape-critical; U10 —
`mkDirectoryNodeMP` at UPLC — is what would discharge them), and the theorems
below still carry `coveringNodeExists … = false` as an EXPLICIT hypothesis. So
the trust surface is unchanged in size; what changed is that discharging it is
now a proved implication from the axiom base instead of a missing conjunct.

ORIGINAL FINDING (historical). `WSC/Honest.lean`'s `DirWF` (ADDENDUM E4) had
three conjuncts — insert-only, key-uniqueness, NFT-name/datum binding — but did
NOT state the INTERVAL-PARTITION property that ARCHITECTURE.md §5.3's
`directory_partition` row describes ("(key,next) intervals partition the key
space; hence an authentic node with `key < cs < next` witnesses `cs ∉ keys`").
Key-uniqueness alone does not forbid a covering node for a registered `cs` — the
two nodes have DIFFERENT keys. -/
def DirWF_partition_conjunct_missing : Prop :=
  ∀ (dirCS cs : CurrencySymbol) (refs : List TxInInfo),
    -- what U10 must supply, and Honest.lean's `DirWF` currently does not:
    (∃ i ∈ refs, i.txInInfoResolved.txOutDatum matches (.OutputDatum _) ∧
       (match i.txInInfoResolved.txOutDatum with
        | .OutputDatum d => (dirNodeFields d).map (fun t => t.1) = some cs
        | _ => False)) →
    coveringNodeExists dirCS cs refs = false

/-! ## The remaining links of P1's chain (STATED, status recorded below) -/

/-- **L1.2** — `pcurrencyPairsUnionFast` (:200-241) adds slot-wise. -/
def L1_2_union_adds : Prop :=
  ∀ (a b u : CsPairs) (cs : CurrencySymbol) (tn : TokenName),
    csPairsUnion a b = some u →
    lookupDataOuter cs tn u = lookupDataOuter cs tn a + lookupDataOuter cs tn b

/-- **L1.3** — `pvalueFromCred` (:392-484) counts EVERY base input: the
three-phase hybrid accumulation agrees, slot by slot, with the ground-truth sum
over inputs at the base credential, and it ERRORS rather than skipping an input
whose owner witness is missing. -/
def L1_3_valueFromCred_counts_all_base_inputs : Prop :=
  ∀ (base : Credential) (sigs : List CardanoLedgerApi.V3.PubKeyHash)
    (wdrl : CardanoLedgerApi.V3.Withdrawals) (inputs : List TxInInfo)
    (total : CsPairs) (cs : CurrencySymbol) (tn : TokenName),
    cs ≠ ByteString.mk "" →
    valueFromCred base sigs wdrl inputs = some total →
    lookupDataOuter cs tn total = inSum base cs tn inputs

/-- **L1.4** — a policy with no covering node survives the transfer walk with its
token map intact (the contrapositive of P5, ADDENDUM E3). -/
def L1_4_registered_survives_transfer_walk : Prop :=
  ∀ (dirCS : CurrencySymbol) (refs : List TxInInfo) (wdrl : CardanoLedgerApi.V3.Withdrawals)
    (proofs wdrlIdxs : List Integer) (total total' : CsPairs) (cached : Data)
    (cs : CurrencySymbol) (tn : TokenName),
    coveringNodeExists dirCS cs refs = false →
    transferWalk dirCS refs wdrl proofs wdrlIdxs total [] cached = some total' →
    lookupDataOuter cs tn total' = lookupDataOuter cs tn total

/-- **L1.5** — a policy with no covering node keeps its mint entry through the
mint walk (P6's positional-classification link: no covering node ⟹ the only
admissible proof is `Member`, and `mintWalk_member_retains` then retains the
entry verbatim). -/
def L1_5_registered_keeps_mint_entry : Prop :=
  ∀ (dirCS : CurrencySymbol) (refs : List TxInInfo) (proofs : List MintProof)
    (mint mv : CsPairs) (cs : CurrencySymbol) (tn : TokenName),
    coveringNodeExists dirCS cs refs = false →
    mintWalk dirCS refs proofs mint [] = some mv →
    lookupDataOuter cs tn mv = lookupDataOuter cs tn mint

/-- **L1.6** — `pfilterPositiveCurrencyPairs` (:257-298) never LOWERS a slot's
requirement: it maps a slot to itself when positive and to `0` otherwise, so it is
pointwise `≥` the unfiltered value. -/
def L1_6_filter_preserves_positive : Prop :=
  ∀ (u e : CsPairs) (cs : CurrencySymbol) (tn : TokenName),
    filterPosCsPairs u = some e →
    lookupDataOuter cs tn u ≤ lookupDataOuter cs tn e

/-! ## P1 and P6 at the MODEL level -/

/-- Every reference input carrying the protocol-params NFT policy (as `phasCSH`
sees it) has a datum naming exactly `dirCS` and `base`.  A ∀-scan, so it
RESTRICTS the transaction and cannot smuggle in the postcondition; under honest
deployment the params NFT is unique (TS1/TS2/TS5) so exactly one reference input
satisfies the guard.  Same idiom as `WSC.paramsView` (`WSC/Spec.lean:216-226`),
but through `hasCSH` — the check the global actually performs (:832). -/
def paramsPinned (ppCS dirCS : CurrencySymbol) (base : Credential) :
    List TxInInfo → Bool
  | [] => true
  | i :: rest =>
      (match hasCSH ppCS i.txInInfoResolved.txOutValue with
       | some true =>
           (match i.txInInfoResolved.txOutDatum with
            | .OutputDatum d => paramsFields d == some (dirCS, base)
            | _ => false)
       | _ => true)
      && paramsPinned ppCS dirCS base rest


/-- **P1 (model level).**  *When the global validator accepts a transfer, no
registered programmable token can leave or vanish from the mini-ledger.*

Formally: for every asset slot of a policy that cannot be exempted (no covering
directory node), the amount at mini-ledger outputs is at least the amount that
came from mini-ledger inputs plus the SIGNED minted amount.

**FINDING — why SIGNED and not `mintPos`.**  ARCHITECTURE.md §3-P1 states the
inequality with `mintPos` (the positive part).  That form is REFUTED by any
transaction that burns a registered asset out of a mini-ledger input: with
`inSum = 5` and `mintSigned = -3` the validator's expected value is
`5 + (-3) = 2` (`pcurrencyPairsUnionFast` then `pfilterPositiveCurrencyPairs`,
:1235-1251), so `outSum = 2 < 5 = inSum + mintPos`.  The SIGNED form below is the
one that is true, and it is also the one ARCHITECTURE.md §5.2's Preservation
reduction actually consumes ("`B_out(cs) ≥ B_in(cs) + mint(cs)`").  Where they
differ the signed form is weaker, and where the escape risk lives — positive mint
— the two coincide (`P1_model_mintPos_form` below). -/
def P1_model (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName) : Prop :=
  globalModel ppCS ctx = true →
  cs ≠ ByteString.mk "" →
  paramsPinned ppCS dirCS base ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
  coveringNodeExists dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, validTxOutValue o.txOutValue = true) →
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
      + mintSigned cs tn ctx.scriptContextTxInfo.txInfoMint

/-- **P6 (model level, inequality form).**  A `Member` classification puts the
minted amount on the REQUIREMENT side: whatever is minted must still be at the
mini-ledger outputs.  (The self-penalization CORE — that the walk carries the
ledger-truth entry over verbatim and can only drop, never negate — is PROVED in
`WSC/Props/P6_Member.lean`.) -/
def P6_model (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName) : Prop :=
  globalModel ppCS ctx = true →
  cs ≠ ByteString.mk "" →
  paramsPinned ppCS dirCS base ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
  coveringNodeExists dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, validTxOutValue o.txOutValue = true) →
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ mintPosOf cs tn ctx.scriptContextTxInfo.txInfoMint

/-! ## The ONE faithfulness axiom (task Z4 step 4) -/

/-- **`globalModel_faithful` — the single trust delta of the B3 route.**

STATEMENT: the model of `WSC/Model/GlobalModel.lean` accepts exactly when the
prepped production bytecode of `programmableLogicGlobal` accepts.

**EVIDENCE FOR IT.**
1. *Line-by-line transcription with citations.*  Every clause of the model cites
   the Plutarch line it mirrors, in
   `src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs`
   (validator :1176-1274; `pvalueFromCred` :392-484; the transfer lockstep walk
   :859-942; the mint lockstep walk :976-1026; the three containment dispatch
   paths :563-699; helpers :129-341, :754-757, :824-838).  The four modelling
   deviations are enumerated as D-M1…D-M4 in that file's header; all four are in
   the "model rejects at least as much as the bytecode" direction except D-M3,
   which is called out explicitly.
2. *The CIP-153 builtins are not modelled at all* — the model calls
   PlutusCoreBlaster's own denotations (`PlutusCore/Value/Basic.lean`,
   branch `cip153-value-builtins` @ 9f9ca8c), i.e. the very functions the CEK
   machine executes.  So `punValueData`/`punionValue`/`pvalueContains`/
   `pvalueData`/`pinsertCoin` carry ZERO transcription risk.
3. *4/4 differential agreement with the real bytecode*
   (`WSC/Model/GlobalGoldens.lean`): the model's verdict equals the verdict the
   production script produced at PV11 on all four global goldens — the three
   accepting ones (`transfer-member-single-policy` K=3,262,
   `transfer-nonmember-covering-node` K=1,554,
   `transfer-mixed-many-policies` K=3,726) and, crucially, the REJECTING
   `transfer-containment-violation-REJECT` (a genuine containment violation:
   `outAtBase 2 < 5 inAtBase`).  Between them the four vectors exercise the
   positive-proof branch, the negative-proof branch, the single-asset dispatch
   and the multi-asset dispatch.
4. *The redeemer mirror is gated* against off-chain-produced CBOR
   (`WSC/Goldens/RedeemerGate.lean`, ADDENDUM E8), so `decodeRedeemer` is not a
   guess about `makeIsDataIndexed` tags.

**WHAT WOULD DISCHARGE IT.**  A `by blaster` proof of
`globalModel ppCS ctx = true ↔ isSuccessful (appliedGlobal.prop ppCS ctx)` over
`WSC/Prep/Global1600.lean` — measured out of reach today (`WSC/STATUS.md` §1) —
or the shaped-context route (fixed list spines + concrete redeemer indices) with a
per-shape budget.  Either would delete this axiom outright.

**RISK.**  This is the ONLY unverified step between the P1/P6 statements and the
production bytecode, and it is a WHOLE-VALIDATOR equivalence: a transcription
error the four goldens do not exercise would silently weaken every theorem that
depends on it.  Concretely un-exercised by the goldens: the `PStakingPtr` and
`PNothing` staking-credential error arms (:441), the `unionValue` OVERFLOW error
path, the wholesale-equality fast path taken on a MULTI-output transaction, and
`paramsRefIdx`/proof-index values that are negative.  Any published claim must
carry this caveat verbatim. -/
axiom globalModel_faithful :
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext),
    globalModel ppCS ctx = true ↔
      PlutusCore.UPLC.Utils.isSuccessful (appliedGlobal1600.prop ppCS ctx)

/-! ## Explicit BYTECODE-level statements (the dependency made visible) -/

/-- **P1 at the bytecode level.**  Identical to `P1_model` with the model's
accept replaced by an accepting run of the real prepped bytecode.  The ONLY extra
assumption relative to `P1_model` is `globalModel_faithful`; the composition below
is what makes that visible rather than implicit. -/
def P1_bytecode (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName) : Prop :=
  PlutusCore.UPLC.Utils.isSuccessful (appliedGlobal1600.prop ppCS ctx) →
  cs ≠ ByteString.mk "" →
  paramsPinned ppCS dirCS base ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
  coveringNodeExists dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, validTxOutValue o.txOutValue = true) →
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
      + mintSigned cs tn ctx.scriptContextTxInfo.txInfoMint

/-- Transport of P1 from the model to the production bytecode.  PROVED — the
axiom is the only ingredient, so the dependency is explicit in the term. -/
theorem P1_bytecode_of_P1_model (ppCS : CurrencySymbol) (ctx : ScriptContext)
    (base : Credential) (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName)
    (h : P1_model ppCS ctx base dirCS cs tn) :
    P1_bytecode ppCS ctx base dirCS cs tn := by
  intro hacc hcs hp hcov hcanon
  exact h ((globalModel_faithful ppCS ctx).mpr hacc) hcs hp hcov hcanon

/-- **P6 at the bytecode level.** -/
def P6_bytecode (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName) : Prop :=
  PlutusCore.UPLC.Utils.isSuccessful (appliedGlobal1600.prop ppCS ctx) →
  cs ≠ ByteString.mk "" →
  paramsPinned ppCS dirCS base ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
  coveringNodeExists dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, validTxOutValue o.txOutValue = true) →
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ mintPosOf cs tn ctx.scriptContextTxInfo.txInfoMint

theorem P6_bytecode_of_P6_model (ppCS : CurrencySymbol) (ctx : ScriptContext)
    (base : Credential) (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName)
    (h : P6_model ppCS ctx base dirCS cs tn) :
    P6_bytecode ppCS ctx base dirCS cs tn := by
  intro hacc hcs hp hcov hcanon
  exact h ((globalModel_faithful ppCS ctx).mpr hacc) hcs hp hcov hcanon

/-! ## Controls (ARCHITECTURE.md Tier 0.2 / 0.3, ADDENDUM E9)

* **Model-level POSITIVE witness**: `WSC.Model.Goldens.model_is_non_vacuous` —
  the model accepts a real off-chain-produced golden, so the
  `globalModel … = true → POST` statements are not vacuous.
* **NEGATIVE control / tightness**: `WSC.Model.Goldens.model_matches_bytecode_containment_violation`
  — the model REJECTS the golden that violates exactly P1's conclusion
  (`outAtBase 2 < 5 = inAtBase`).  Together with the three accepting vectors this
  pins the accept/reject axis from both sides at the model level.
* **Anti-tautology**: every quantity in `P1_model`/`P6_model` is `outSum`/`inSum`/
  `mintSigned`/`mintPosOf`, i.e. CLAB `valueOf` over `ScriptContext` fields.  No
  postcondition mentions `expectedProgrammableOutputValue`,
  `totalProgTokenValue`, or any other validator accumulator (ARCHITECTURE.md D3 /
  Tier 0.1). -/

/-- The negative control, restated locally so it is visible next to the theorem it
guards: the model rejects the containment-violating golden. -/
theorem P1_negative_control_model_rejects_violation :
    WSC.Model.Goldens.modelVerdict
      WSC.Goldens.programmableLogicGlobal_transfer_containment_violation_REJECT
      = some false :=
  WSC.Model.Goldens.model_matches_bytecode_containment_violation

/-! ## OBLIGATION STATUS (read before citing anything above)

**PROVED in this session, no `sorry`, no `blaster`, no `native_decide`:**

| # | Result | Where |
|---|---|---|
| L1.1c | Path C (builtin `valueContains`) is containment-sound: accept ⟹ ∀ slot, expected ≤ Σ base outputs | `pathC_sound` |
| — | `accumulateOutputsAtCred` computes the ground-truth per-slot sum and preserves sortedness | `accum_lookup` |
| — | `lookupDataOuter` ≡ CLAB `valueOf` on shape-well-formed values; the two output sums agree | `WSC/Model/Ground.lean` |
| L6.1 | the mint walk returns an order-preserving SUBLIST of `txInfoMint` (verbatim entries, drops only, no arithmetic) | `WSC/Props/P6_Member.lean` `mintWalk_sublist` |
| L6.2 | a `Member` proof retains its entry, touching no directory node | `WSC/Props/P6_Member.lean` `mintWalk_member_retains` |
| — | `pisScriptInvokedEntries`'s two-per-iteration unrolling ≡ the one-step walk | `WSC/Model/GlobalModel.lean` |
| — | model verdict = real bytecode verdict on **4/4** global goldens incl. the rejecting containment violation | `WSC/Model/GlobalGoldens.lean` (`native_decide`) |

**STATED, NOT PROVED (§A).**  `L1_1a_pathA_sound`, `L1_1b_pathB_sound`,
`L1_2_union_adds`, `L1_3_valueFromCred_counts_all_base_inputs`,
`L1_4_registered_survives_transfer_walk`, `L1_5_registered_keeps_mint_entry`,
`L1_6_filter_preserves_positive`, and therefore `P1_model` / `P6_model`
themselves.  They are `Prop` DEFINITIONS, not axioms: nothing in this library
consumes them, so no theorem here is stronger than what is listed above.  Effort
estimate and shape for each: Paths A/B need the ledger-canonicity toolkit
(sorted-early-exit lookup ≡ linear lookup; ada-first; per-output non-negativity —
all derivable from CLAB's `validTxOutValue`, none of them derived yet); L1.2 needs a
`unionOuter_lookup`-style sorted-merge induction (PlutusCoreBlaster's proof of the
analogous builtin lemma is ~100 lines, and `pcurrencyPairsUnionFast` is the same
shape); L1.3 is the three-phase hybrid and is the largest single item; L1.4/L1.5
are lockstep-walk inductions of the shape the E2 spike closed in 2.9 s (row A3).

**ASSUMED (§B).**  `globalModel_faithful` — one axiom, docstring above, with its
evidence, its discharge route and its residual risk.

**NOT AVAILABLE FROM `WSC/Honest.lean` (§C).**  The interval-partition conjunct of
`DirWF` (see `DirWF_partition_conjunct_missing`).  Until U10 adds it, the
`coveringNodeExists … = false` hypothesis of `P1_model`/`P6_model` is carried
explicitly and is exactly as strong as P5's `DirWF` dependency. -/

end WSC.Model
