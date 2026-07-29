-- ⛔ AXIOM RETRACTED (task R1). `seizeModel_faithful` is FALSE at main 2306678 and has been DELETED, together with `P2a_bytecode`, `P2b_bytecode` and `P2b_model_implies_bytecode` — machine-checked refutations in WSC/Model/SeizeModelRefuted.lean. What survives here is TRUE OF THE MODEL and is NOT a statement about production. P2 against production: WSC/Props/Shaped/P2ShapedR.lean.
/-
WSC/Props/P2_Seize.lean — **P2 (seize)** via the SOURCE-MODEL route (B3).

PLAIN ENGLISH.  When the seize (clawback) validator accepts, it only ever moves
the ONE policy being seized: every mini-ledger input it consumes has a
corresponding continuing output at the same address with the same datum and
reference script, differing at most in the seized policy; and the seized amount
plus any seize-time mint of that policy stays inside the mini-ledger.  So a
seizure relocates the seized tokens within the mini-ledger and cannot touch
anything else.

HOW TO READ THIS FILE (the honest summary, first, before any theorem):

* **Conjunct 1 — structure preservation: PROVEN, unconditionally, in Lean's
  kernel.**  `P2a_seizeModel_preserves_structure` is an ordinary Lean proof (no
  `blaster`, hence no `admit`, hence no `sorry`) about
  `WSC.SeizeModel.seizeModel`.  It carries NO well-formedness side conditions.
* **Conjunct 2 — containment of the seized delta: NOT PROVEN.**  It is stated
  precisely (`P2b_seized_delta_contained`), the hypothesis-free half of its
  reduction ladder is proven (§4), the exact two missing bridges are named (§5),
  and it is **verified concretely** on both accepting seize goldens and
  **refuted** on the rejecting one by `native_decide` (§6).  What is missing is
  the general proof, not confidence in the statement.
* **There is NO bytecode-level result in this file any more.**  §7 used to
  compose conjunct 1 with the fidelity axiom
  `WSC.SeizeModel.seizeModel_faithful`; that axiom is FALSE of the post-#112
  bytecode and both it and everything it carried were DELETED at task R1
  (`WSC/Model/SeizeModelRefuted.lean` refutes it by computation).  **Everything
  below is a statement about `WSC.SeizeModel.seizeModel`, not about
  production.**  P2 against production is
  `WSC/Props/Shaped/P2ShapedR.lean` — both conjuncts, at UPLC, no model, no
  faithfulness axiom, bounded by budget 3800 and SHAPE S1R.

WHY THE SOURCE-MODEL ROUTE AT ALL — a premise that has since EXPIRED.  When this
file was written P2 was measured out of reach at UPLC; shaped contexts (task Z6,
re-cut at N5) broke that wall, and `WSC/Props/Shaped/P2ShapedR.lean` now proves
both conjuncts against the compiled program.  The paragraph below is kept as the
record of why the model was built:
cheapest accepting seize run 2,570 CEK steps; `#prep_uplc` at 2,000 unfinished
in 77 min and at 9,000 unfinished in 62 min; the budgets whose prep DOES
complete (600, 1,000) have vacuity probes returning `Valid` for "no accepting
context exists"; and task Y1 showed the binding wall is Z3 SEARCH over a fully
symbolic `Data` context, not prep (`WSC/goldens/K-MEASUREMENTS.md` §5.1/§5.2,
`WSC/STATUS.md` P2 row).

D3 (TAUTOLOGY RISK) COMPLIANCE.  ARCHITECTURE.md's hard gate is that no P2
postcondition may mention the validator's own `expectedValue` /
`deltaAccumulator`.  Conjunct 1's postcondition is `WSC.Spec`'s
`seizeStructurePreserved`, a function of `txInfoInputs` and `txInfoOutputs`
only.  Conjunct 2's is `valueOf`-sums over base inputs / base outputs plus
`mintOf` — ledger ground truth.  The three `Option`-valued projections used in
the hypotheses (`seizedPolicyOf`, `pairedOutputsOf`, `progLogicCredDataOf`) only
NAME ledger data: a redeemer index used to index `txInfoReferenceInputs` /
`txInfoOutputs`, and two `Data` fields of a reference input's datum.
-/
import WSC.Model.SeizeModel
import WSC.Model.SeizeDiff
import WSC.Spec

namespace WSC.P2

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext TxInInfo TxOut valueOf)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open WSC.SeizeModel
open WSC.Goldens

/-! ## 1. `Credential` encoding injectivity

The validator compares credentials as `Data` (WSC/Model/SeizeModel.lean §3), so
the model does too.  This is the one lemma that reads such a comparison back as a
comparison of the `Credential` the theorem is parameterized by. -/

theorem toData_credential_beq (c d : Credential) :
    ((IsData.toData c : Data) == IsData.toData d) = (c == d) := by
  cases c <;> cases d <;>
    simp [IsData.toData, CardanoLedgerApi.IsData.Class.mkDataConstr, BEq.beq,
          PlutusCore.Data.eqData, PlutusCore.Data.eqDataConstr, PlutusCore.Data.eqDataList,
          CardanoLedgerApi.V1.Credential.beqCredential]

/-! ## 2. Lemma A — the per-pair value obligation

`pvalueEqualsDeltaCurrencySymbol` returning a delta at all forces every policy
other than the seized one (Ada included) to be byte-identical across the pair.
`WSC.dropCS` (WSC/Spec.lean:320-323) is the ground-truth "value with the seized
policy's entry deleted". -/

/-- Leftover-side obligation: `remainingProgCSDelta` succeeds only when the
leftover currency list holds nothing but the seized policy — the two `perror`s at
ProgrammableLogicBase.hs:1767 / :1768. -/
theorem remainingProgCSDelta_dropCS {neg : Bool} {cs : CurrencySymbol} :
    ∀ {v : Value} {t : Tokens}, remainingProgCSDelta neg cs v = some t →
      WSC.dropCS cs v = [] := by
  intro v t h
  match v with
  | [] => simp [WSC.dropCS]
  | (Data.B c, m) :: rest =>
      by_cases hc : c == cs
      · match rest with
        | [] => simp [WSC.dropCS, hc]
        | _ :: _ => simp [remainingProgCSDelta, hc] at h
      · simp [remainingProgCSDelta, hc] at h
  | (Data.I _, _) :: _ => simp [remainingProgCSDelta] at h
  | (Data.Constr _ _, _) :: _ => simp [remainingProgCSDelta] at h
  | (Data.List _, _) :: _ => simp [remainingProgCSDelta] at h
  | (Data.Map _, _) :: _ => simp [remainingProgCSDelta] at h

/-- **LEMMA A (walk form).**  If `goOuter` succeeds, the two values agree
everywhere outside the seized policy.

Each case is one branch of `goOuter` (ProgrammableLogicBase.hs:1784-1823) and the
proof is that branch's own reason:
* equal CS and IS the seized policy (:1793-1797) — the remaining currency lists
  are forced `Data`-equal, and both heads are deleted by `dropCS`;
* equal CS and NOT the seized policy (:1799) — the entries are forced equal, the
  tails agree by induction;
* CS differ (:1806-1817) — the side holding the smaller CS must hold the seized
  policy, so `dropCS` deletes its head and induction applies;
* either side exhausted (:1819 / :1822) — `remainingProgCSDelta_dropCS`;
* every remaining case is a `perror` branch, refuted by the `some d`
  hypothesis. -/
theorem valueDeltaGo_dropCS (cs : CurrencySymbol) :
    ∀ (iv ov : Value) (acc : Tokens) (d : Tokens),
      valueDeltaGo cs iv ov acc = some d → WSC.dropCS cs iv = WSC.dropCS cs ov := by
  intro iv ov acc
  fun_induction valueDeltaGo cs iv ov acc
  case case1 outs acc r hr => intro d hd; simp [WSC.dropCS, remainingProgCSDelta_dropCS hr]
  case case3 ki vi irest acc r hr => intro d hd; simp [WSC.dropCS, remainingProgCSDelta_dropCS hr]
  all_goals (intro d hd; simp_all [WSC.dropCS])

/-- **LEMMA A.**  `pvalueEqualsDeltaCurrencySymbol` succeeding on a pair implies
the pair's values are equal outside the seized policy.  (The extra
`pcurrencyListHasCS` gate at :1827-1830 only strengthens the hypothesis.) -/
theorem valueDelta_dropCS {cs : CurrencySymbol} {iv ov : Value} {d : Tokens}
    (h : valueDelta cs iv ov = some d) : WSC.dropCS cs iv = WSC.dropCS cs ov := by
  unfold valueDelta at h
  match hc : currencyListHasCS cs iv with
  | some true => rw [hc] at h; exact valueDeltaGo_dropCS cs iv ov [] d h
  | some false => rw [hc] at h; simp at h
  | none => rw [hc] at h; simp at h

/-! ## 3. Lemma B + conjunct 1 — the input/output walk -/

/-- **LEMMA B.**  Every accepting run of the mini-ledger walk establishes
`WSC.seizeStructurePreserved`: each base-credential input is paired, in order,
with a continuing output that preserves the full address (staking credential
included), the datum and the reference script, and differs at most in the seized
policy; non-base inputs consume no output.

The three field equalities come straight from the validator's own conjunction
(:1460-1463) and the value clause from Lemma A; the `[] => none` case is
`phead`-of-empty at :1450, which is exactly `seizeStructurePreserved`'s `[] =>
false`. -/
theorem seizeWalk_preserves (cs : CurrencySymbol) (base : Credential) :
    ∀ (ins : List TxInInfo) (outs : List TxOut) (acc : Tokens)
      (res : List TxOut) (acc2 : Tokens),
      seizeWalk cs (IsData.toData base) ins outs acc = some (res, acc2) →
      WSC.seizeStructurePreserved base cs ins outs = true := by
  intro ins outs acc
  fun_induction seizeWalk cs (IsData.toData base) ins outs acc with
  | case1 outs acc => intro res acc2 _; simp [WSC.seizeStructurePreserved]
  | case2 i rest acc inp hb => intro res acc2 h; simp [seizeWalk, hb] at h
  | case3 i rest acc inp hb o os hf r hv r1 hu ih =>
      intro res acc2 h
      have hd := valueDelta_dropCS hv
      simp only [Bool.and_eq_true] at hf
      have hb' : (IsData.toData (WSC.payCred i.txInInfoResolved) : Data)
                   = IsData.toData base := by simpa using hb
      simp only [WSC.seizeStructurePreserved, WSC.inAtBase, WSC.outAtBase,
                 ← toData_credential_beq, WSC.pairPreserved]
      simp [hb', hf.1.1, hf.1.2, hf.2, hd, ih res acc2 h]
      exact ⟨⟨⟨by simpa using hf.1.1, by simpa using hf.1.2⟩, by simpa using hf.2⟩, hd⟩
  | case4 i rest acc inp hb o os hf r hv hu => intro res acc2 h; simp [seizeWalk, hb, hv, hu] at h
  | case5 i rest acc inp hb o os hf hv => intro res acc2 h; simp [seizeWalk, hb, hv] at h
  | case6 i rest acc inp hb o os hf => intro res acc2 h; simp [seizeWalk, hb, hf] at h
  | case7 i rest outs acc inp hb ih =>
      intro res acc2 h
      have hb' : ¬((IsData.toData (WSC.payCred i.txInInfoResolved) : Data)
                     = IsData.toData base) := by simpa using hb
      simp only [WSC.seizeStructurePreserved, WSC.inAtBase, WSC.outAtBase,
                 ← toData_credential_beq]
      simp [hb', ih res acc2 h]

/-- Unfold the model down to its mini-ledger walk: an accepting run pins the
seized policy, the paired-output cursor and the base credential to the values the
projections compute, and its walk succeeded. -/
theorem seizeRun_gives_walk {ppCS : CurrencySymbol} {ctx : ScriptContext}
    {seizedCS : CurrencySymbol} {paired : List TxOut} {baseData : Data}
    (hacc : seizeModel ppCS ctx = true)
    (hcs : seizedPolicyOf ctx = some seizedCS)
    (hout : pairedOutputsOf ctx = some paired)
    (hbase : progLogicCredDataOf ppCS ctx = some baseData) :
    ∃ res acc',
      seizeWalk seizedCS baseData ctx.scriptContextTxInfo.txInfoInputs paired []
        = some (res, acc') := by
  unfold seizeModel seizeRun at hacc
  unfold seizedPolicyOf at hcs
  unfold pairedOutputsOf at hout
  unfold progLogicCredDataOf at hbase
  match hf : seizeFieldsOf ctx.scriptContextRedeemer with
  | none => simp only [hf] at hacc; simp at hacc
  | some f =>
      simp only [hf] at hacc hcs hout hbase
      match hp : paramsAtRefIdx ppCS ctx.scriptContextTxInfo.txInfoReferenceInputs f.paramsIdx with
      | none => simp only [hp] at hacc; simp at hacc
      | some (dirCS, bd) =>
          simp only [hp] at hacc hbase
          match hn : headM (dropL f.dirIdx ctx.scriptContextTxInfo.txInfoReferenceInputs) with
          | none => simp only [hn] at hacc; simp at hacc
          | some dirNode =>
              simp only [hn] at hacc hcs
              match hk : nodeKeyAndIssuer dirNode.txInInfoResolved.txOutDatum with
              | none => simp only [hk] at hacc; simp at hacc
              | some (key, issuerData) =>
                  simp only [hk] at hacc hcs
                  match hm : tokensForCS key ctx.scriptContextTxInfo.txInfoMint with
                  | none => simp only [hm] at hacc; simp at hacc
                  | some minted =>
                      simp only [hm] at hacc
                      simp only [Option.some.injEq] at hcs hout hbase
                      subst hcs; subst hout; subst hbase
                      unfold processThirdPartyTransfer at hacc
                      match hw : seizeWalk key bd ctx.scriptContextTxInfo.txInfoInputs
                                   (dropL f.outStart ctx.scriptContextTxInfo.txInfoOutputs) [] with
                      | none => simp only [hw] at hacc; simp at hacc
                      | some (res, acc') => exact ⟨res, acc', rfl⟩

/-! ### CONJUNCT 1 -/

/-- **P2 (a) — STRUCTURE PRESERVATION, PROVEN.**

*Every accepting seize relocates only the seized policy: walking the
transaction's inputs in order, each input at the mini-ledger base credential is
paired with the next continuing output, and that pair has the same address
(staking credential included), the same datum, the same reference script, and
identical holdings of EVERY policy other than the seized one — Ada included.
Inputs outside the mini-ledger consume no output.*

No well-formedness hypothesis is needed.  The three `Option` hypotheses only NAME
ledger data (the seized policy = the `key` of the directory node the redeemer
points at; the paired-output cursor = `txInfoOutputs` from the redeemer's
`outputsStartIdx`; the base credential = field 1 of the authenticated
protocol-params datum).

SCOPE: this is a theorem about `WSC.SeizeModel.seizeModel` **and about nothing
else**.  The §7 transport to the bytecode was RETRACTED at task R1 (its axiom is
false), so this statement no longer implies anything about production; the
production statement is `WSC.P2a_R_structure`
(`WSC/Props/Shaped/P2ShapedR.lean`). -/
theorem P2a_seizeModel_preserves_structure
    (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol) (paired : List TxOut)
    (hacc : seizeModel ppCS ctx = true)
    (hcs : seizedPolicyOf ctx = some seizedCS)
    (hout : pairedOutputsOf ctx = some paired)
    (hbase : progLogicCredDataOf ppCS ctx = some (IsData.toData base)) :
    WSC.seizeStructurePreserved base seizedCS
      ctx.scriptContextTxInfo.txInfoInputs paired = true := by
  obtain ⟨res, acc', hw⟩ := seizeRun_gives_walk hacc hcs hout hbase
  exact seizeWalk_preserves seizedCS base _ _ _ _ _ hw

/-! ## 4. Conjunct 2 — statement, ground-truth vocabulary, and the ladder -/

/-- Aggregate holding of `(cs, tn)` across the outputs that sit at the
mini-ledger base credential.  Ground truth: `WSC.outAtBase` + CLAB `valueOf`. -/
def sumOutAtBase (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if WSC.outAtBase base o then valueOf cs tn o.txOutValue else 0)
      + sumOutAtBase base cs tn rest

/-- Aggregate holding of `(cs, tn)` across the inputs spent from the mini-ledger
base credential. -/
def sumInAtBase (base : Credential) (cs : CurrencySymbol) (tn : TokenName) :
    List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if WSC.inAtBase base i then valueOf cs tn i.txInInfoResolved.txOutValue else 0)
      + sumInAtBase base cs tn rest

/-- **P2 (b) — CONTAINMENT OF THE SEIZED DELTA (STATEMENT ONLY — see §5).**

*The seized amount plus any seize-time mint of the seized policy stays inside the
mini-ledger: for every token name, the total held at base outputs is at least the
total held at base inputs plus the (SIGNED) net mint of that asset.*

The mint is signed, not `mintPos`: a legitimate burn of the seized policy lowers
the requirement (ARCHITECTURE.md §3-P2 note).

WHY THIS IS THE RIGHT `≥` AND NOT `=`.  The validator's containment check only
bounds the RESIDUAL base outputs (those after the paired ones —
ProgrammableLogicBase.hs:1504-1506), and outputs BEFORE the redeemer's
`outputsStartIdx` are not visited at all; both slack sources can only ADD to the
base side, so the ledger-ground-truth consequence is an inequality. -/
def P2b_seized_delta_contained : Prop :=
  ∀ (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol),
    seizeModel ppCS ctx = true →
    seizedPolicyOf ctx = some seizedCS →
    progLogicCredDataOf ppCS ctx = some (IsData.toData base) →
    ∀ tn : TokenName,
      sumOutAtBase base seizedCS tn ctx.scriptContextTxInfo.txInfoOutputs
        ≥ sumInAtBase base seizedCS tn ctx.scriptContextTxInfo.txInfoInputs
          + WSC.mintOf seizedCS tn ctx.scriptContextTxInfo.txInfoMint

/-! ### The hypothesis-free half of the ladder

The quantity the validator manipulates is a token-pair list; the ground-truth
quantity is a signed sum.  `tokSum` is the bridge, and it is ADDITIVE over the
validator's three token-list combinators with NO sortedness or duplicate-freeness
hypothesis.  That is the half of the ladder that closes; §5 says what does not. -/

/-- Total signed quantity recorded for token name `tn` in a token-pair list
(summing every matching entry — deliberately NOT first-match, so the lemmas below
need no duplicate-freeness hypothesis). -/
def tokSum (tn : TokenName) : Tokens → Integer
  | [] => 0
  | (Data.B n, Data.I q) :: rest => (if n == tn then q else 0) + tokSum tn rest
  | _ :: rest => tokSum tn rest

/-! ### CANONICITY — the ledger rule, and the bridge lemma **B1**, PROVED

The two theorems at the end of this section are the machine-checked witnesses on
which the library once rested a much stronger claim than they support.  They show
that `tokensContain` is unsound over ARBITRARY `List (Data × Data)`.  They do NOT
show anything about the values a ledger delivers, because **neither witness is a
value any ledger can produce**: CLAB's own `[LEDGER-RULE]` predicate
`validTxOutValue` (CardanoLedgerApi/V1/Contexts.lean:787-802) requires ada first,
STRICTLY ASCENDING currency symbols and token names, and EVERY quantity `> 0`,
and it is a conjunct of the `validRewardingContext` hypothesis every shaped P2
theorem already carries (`validRewardingContext` → `validScriptContext` →
`validTxInfo` → `validInputs` / `validOutputs` → `validTxOutValue`, V3/Contexts
:1645, :1696, :1821-1826, :1849, :1867).

So B1 is a THEOREM, not a gap, and this section proves it.  The proof also
identifies WHICH conjunct of canonicity is load-bearing, and the answer is
narrower than "canonicity": **only non-negativity of the `actual` list**.
Sortedness and duplicate-freeness are not used anywhere in `tokensContain_sound`;
what makes the two witnesses counterexamples is the NEGATIVE quantity each of
them carries in `actual`.

Everything here is ordinary Lean — no `blaster`, no `native_decide`, no axiom. -/

/-- `omega` does not fire on goals whose type is spelled
`PlutusCore.Integer.Integer` (the `abbrev` for `Int`), so the three arithmetic
steps below are isolated over plain `Int` and applied by name.  Same
tactic-plumbing detail as `WSC/Composition.lean` §3's `Int` helpers. -/
theorem int_le_add_left {a b : Int} (h : 0 ≤ a) : b ≤ a + b := by omega
theorem int_add_le_left {a b : Int} (h : a ≤ 0) : a + b ≤ b := by omega
theorem int_add_le_add {a b c d : Int} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by omega

/-- One entry of a token list records no NEGATIVE quantity.  Entries whose value
is not a `Data.I` record nothing at all, and `tokSum` skips them. -/
def nonnegP : Data × Data → Bool
  | (_, Data.I q) => decide (0 ≤ q)
  | _ => true

/-- No entry of the list records a negative quantity. -/
def tokensNonneg : Tokens → Bool
  | [] => true
  | p :: rest => nonnegP p && tokensNonneg rest

/-- **LEDGER CANONICITY OF ONE POLICY'S TOKEN LIST**, stated exactly as CLAB
states it.  `validTxOutValue` admits a policy's token map only in the form
`(Data.B tn, Data.I n) :: tokens` with `n > 0` and
`validTxOutValue.validTokens tokens tn` — strictly ascending names, every
quantity `> 0` (CardanoLedgerApi/V1/Contexts.lean:787-792).  The empty list is
admitted too, because that is what `tokensForCS` returns for an ABSENT policy.
The tail predicate is CLAB's own function, re-used rather than transcribed, so
this definition cannot drift from the ledger rule. -/
def canonTokens : Tokens → Bool
  | [] => true
  | (Data.B tn, Data.I q) :: rest =>
      decide (0 < q) && CardanoLedgerApi.V1.Contexts.validTxOutValue.validTokens rest tn
  | _ => false

theorem tokSum_cons_B_I (tn n : TokenName) (q : Integer) (rest : Tokens) :
    tokSum tn ((Data.B n, Data.I q) :: rest)
      = (if n == tn then q else 0) + tokSum tn rest := rfl

/-- Prepending a non-negative entry can only raise a `tokSum`. -/
theorem tokSum_cons_le (tn : TokenName) (p : Data × Data) (rest : Tokens)
    (h : nonnegP p = true) : tokSum tn rest ≤ tokSum tn (p :: rest) := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;>
    first
      | exact Int.le_refl _
      | (rename_i n q
         have hq : (0:Integer) ≤ q := by simpa [nonnegP] using h
         rw [tokSum_cons_B_I]
         split
         exact int_le_add_left hq
         exact int_le_add_left (Int.le_refl 0))

/-- Prepending a non-positive entry can only lower a `tokSum`. -/
theorem tokSum_cons_ge (tn : TokenName) (k : Data) (q : Integer) (rest : Tokens)
    (h : 0 ≥ q) : tokSum tn ((k, Data.I q) :: rest) ≤ tokSum tn rest := by
  cases k <;>
    first
      | exact Int.le_refl _
      | (rw [tokSum_cons_B_I]
         split
         exact int_add_le_left h
         exact int_add_le_left (Int.le_refl 0))

theorem tokSum_nonneg (tn : TokenName) :
    ∀ (l : Tokens), tokensNonneg l = true → 0 ≤ tokSum tn l := by
  intro l
  induction l with
  | nil => intro _; exact Int.le_refl 0
  | cons p rest ih =>
      intro h
      simp only [tokensNonneg, Bool.and_eq_true] at h
      exact Int.le_trans (ih h.2) (tokSum_cons_le tn p rest h.1)

/-- **B1 — `tokensContain` IS POINTWISE SOUND, and the only hypothesis it needs
is that the ACTUAL list records no negative quantity.**

*If `ptokenPairsContain actualTokens requiredTokens` returns `True` and no entry
of `actualTokens` carries a negative quantity, then for EVERY token name the
actual total is at least the required total.*

This is the obligation §5 used to name as missing.  It is proved here by the
merge-walk induction `tokensContain` itself performs
(ProgrammableLogicBase.hs:1381-1411), one case per branch:

* required exhausted (:1410) — the required total is 0 and the actual total is
  `≥ 0`; **this is the case, and the only case, that consumes non-negativity**;
* actual exhausted (:1407) — the branch is taken only when `0 ≥ requiredQty`, so
  the required total is `≤ 0` and the actual total is 0;
* equal names (:1399-1400) — the branch tests `actualQty ≥ requiredQty` and the
  tails are handled by the induction hypothesis;
* actual name smaller (:1402-1403) — the actual head is DROPPED; its quantity is
  `≥ 0`, so dropping it can only lower the actual side, and the induction
  hypothesis already bounds the lowered side;
* actual name larger (:1404) — the branch is taken only when `0 ≥ requiredQty`;
* every other branch is a `perror`, refuted by the `some true` hypothesis.

SORTEDNESS IS NOT USED.  Neither is duplicate-freeness.  That is worth stating
because the two counterexamples below were read, for several revisions, as
showing that both were needed. -/
theorem tokensContain_sound :
    ∀ (actual required : Tokens),
      tokensNonneg actual = true →
      tokensContain actual required = some true →
      ∀ tn : TokenName, tokSum tn required ≤ tokSum tn actual := by
  intro actual required
  fun_induction tokensContain actual required with
  | case1 x => intro hn _ tn; exact tokSum_nonneg tn x hn
  | case2 kr rrest aq h ih =>
      intro hn hc tn
      exact Int.le_trans (tokSum_cons_ge tn kr aq rrest h) (ih hn hc tn)
  | case3 kr rrest aq h => intro _ hc _; simp at hc
  | case4 rrest aq arest na nb hbeq aq1 hge ih =>
      intro hn hc tn
      simp only [tokensNonneg, Bool.and_eq_true] at hn
      have ihh := ih hn.2 hc tn
      have hnab : na = nb := by simpa using hbeq
      subst hnab
      rw [tokSum_cons_B_I, tokSum_cons_B_I]
      by_cases hEq : (na == tn) = true
      · rw [if_pos hEq, if_pos hEq]; exact int_add_le_add hge ihh
      · rw [if_neg hEq, if_neg hEq]; exact int_add_le_add (Int.le_refl 0) ihh
  | case5 rrest aq arest na nb hbeq aq1 hge => intro _ hc _; simp at hc
  | case6 rrest aq va arest na nb hbeq hva => intro _ hc _; simp at hc
  | case7 rrest aq va arest na nb hne hlt ih =>
      intro hn hc tn
      simp only [tokensNonneg, Bool.and_eq_true] at hn
      exact Int.le_trans (ih hn.2 hc tn) (tokSum_cons_le tn (Data.B na, va) arest hn.1)
  | case8 rrest aq va arest na nb hne hnlt hle ih =>
      intro hn hc tn
      exact Int.le_trans (tokSum_cons_ge tn (Data.B nb) aq rrest hle) (ih hn hc tn)
  | case9 rrest aq va arest na nb hne hnlt hgt => intro _ hc _; simp at hc
  | case10 kr rrest aq ka va arest hk => intro _ hc _; simp at hc
  | case11 actual kr vr rrest hvr => intro _ hc _; simp at hc

/-- Canonicity implies the non-negativity B1 consumes. -/
theorem validTokens_nonneg :
    ∀ (ts : Tokens) (prev : ByteString),
      CardanoLedgerApi.V1.Contexts.validTxOutValue.validTokens ts prev = true →
        tokensNonneg ts = true := by
  intro ts
  induction ts with
  | nil => intro _ _; rfl
  | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      cases a <;> cases b <;> intro prev h <;>
        simp [CardanoLedgerApi.V1.Contexts.validTxOutValue.validTokens] at h
      rename_i n q
      simp only [tokensNonneg, nonnegP, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Int.le_of_lt h.1.2, ih n h.2⟩

theorem canonTokens_nonneg (ts : Tokens) (h : canonTokens ts = true) :
    tokensNonneg ts = true := by
  match ts with
  | [] => rfl
  | (Data.B tn, Data.I q) :: rest =>
      simp only [canonTokens, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [tokensNonneg, nonnegP, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Int.le_of_lt h.1, validTokens_nonneg rest tn h.2⟩
  | (Data.B _, Data.Constr _ _) :: _ | (Data.B _, Data.Map _) :: _
  | (Data.B _, Data.List _) :: _ | (Data.B _, Data.B _) :: _
  | (Data.Constr _ _, _) :: _ | (Data.Map _, _) :: _
  | (Data.List _, _) :: _ | (Data.I _, _) :: _ => simp [canonTokens] at h

/-- **B1, in the form the ladder quotes it: `tokensContain` IS SOUND UNDER
LEDGER CANONICITY.** -/
theorem tokensContain_sound_of_canon (actual required : Tokens)
    (ha : canonTokens actual = true)
    (h : tokensContain actual required = some true) :
    ∀ tn : TokenName, tokSum tn required ≤ tokSum tn actual :=
  tokensContain_sound actual required (canonTokens_nonneg actual ha) h

theorem tokensForCS_nil (cs : CurrencySymbol) :
    tokensForCS cs ([] : Value) = some [] := rfl

theorem tokensForCS_nonneg_go (cs : CurrencySymbol) :
    ∀ (v : Value) (prev : ByteString) (ts : Tokens),
      CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol v prev = true →
      tokensForCS cs v = some ts → tokensNonneg ts = true := by
  intro v
  induction v with
  | nil =>
      intro _ ts _ hf
      simp only [tokensForCS_nil, Option.some.injEq] at hf
      subst hf; rfl
  | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      cases a <;> cases b <;> intro prev ts hv hf <;>
        try simp [CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol] at hv
      rename_i c toks
      cases toks with
      | nil => simp [CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol] at hv
      | cons q toks' =>
          obtain ⟨ka, va⟩ := q
          cases ka <;> cases va <;>
            try simp [CardanoLedgerApi.V1.Contexts.validTxOutValue.validCurrencySymbol] at hv
          rename_i tn n
          simp only [tokensForCS] at hf
          by_cases hc : (c == cs) = true
          · rw [if_pos hc, Option.some.injEq] at hf
            subst hf
            simp only [tokensNonneg, nonnegP, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨Int.le_of_lt hv.1.1.2, validTokens_nonneg toks' tn hv.1.2⟩
          · rw [if_neg hc] at hf
            by_cases hlt : cs < c
            · rw [if_pos hlt, Option.some.injEq] at hf; subst hf; rfl
            · rw [if_neg hlt] at hf; exact ih c ts hv.2 hf

/-- **THE LEDGER SUPPLIES WHAT B1 NEEDS.**  Every token list the validator's
`ptokensForCurrencySymbol` (ProgrammableLogicBase.hs:1345-1364) can extract from
a `validTxOutValue`-canonical `Value` satisfies `tokensNonneg`.  Since
`validRewardingContext` forces `validTxOutValue` on every resolved input value
and every output value, this is available at every use site inside a shaped P2
theorem, and it needs no new assumption. -/
theorem tokensForCS_nonneg (cs : CurrencySymbol) (v : Value) (ts : Tokens)
    (hv : CardanoLedgerApi.V1.Contexts.validTxOutValue v = true)
    (hf : tokensForCS cs v = some ts) : tokensNonneg ts = true := by
  unfold CardanoLedgerApi.V1.Contexts.validTxOutValue at hv
  split at hv
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [tokensForCS] at hf
    by_cases hc : ((ByteString.mk "") == cs) = true
    · rw [if_pos hc, Option.some.injEq] at hf
      subst hf
      simp only [tokensNonneg, nonnegP, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Int.le_of_lt hv.1, trivial⟩
    · rw [if_neg hc] at hf
      by_cases hlt : cs < (ByteString.mk "")
      · rw [if_pos hlt, Option.some.injEq] at hf; subst hf; rfl
      · rw [if_neg hlt] at hf
        exact tokensForCS_nonneg_go cs _ _ ts hv.2 hf
  · simp at hv

/-- **THE TWO WITNESSES ARE LEDGER-IMPOSSIBLE, machine-checked.**  Each token
list the theorems below use as `actual` FAILS `canonTokens`, i.e. fails the
`validTxOutValue` shape the ledger imposes on every `TxOut` value; so does the
second one's `required`.  This is the fact that bounds what those theorems show.
`[(x,50)]` is included to make the point sharp: it IS canonical, and the first
counterexample is therefore caused by `actual` alone. -/
theorem counterexample_witnesses_are_not_canonical :
    canonTokens [(Data.B (ByteString.mk "x"), Data.I 100),
                 (Data.B (ByteString.mk "x"), Data.I (-100))] = false ∧
    canonTokens [(Data.B (ByteString.mk "x"), Data.I 50)] = true ∧
    canonTokens [(Data.B (ByteString.mk "x"), Data.I (-5)),
                 (Data.B (ByteString.mk "z"), Data.I 10)] = false ∧
    canonTokens [(Data.B (ByteString.mk "z"), Data.I 10),
                 (Data.B (ByteString.mk "x"), Data.I (-3))] = false := by
  native_decide

/-- **WHAT `tokensContain` DOES WITHOUT CANONICITY (1/2) — a duplicate token name
and a negative quantity.**  A TRUE Lean fact about `List (Data × Data)`, and
nothing more.

`actual = [(x,100),(x,-100)]`, `required = [(x,50)]`: the helper matches the first
pair (`100 ≥ 50`, ProgrammableLogicBase.hs:1400), the required list is then
exhausted and it returns `True` (:1410) — while the actual per-name total is 0,
which does not cover 50.

**THIS IS NOT A COUNTEREXAMPLE TO ANYTHING THE LIBRARY CLAIMS**, and for two
independent reasons.  (a) `actual` is not a value any ledger can produce: it
repeats a token name, which `validTxOutValue`'s `prev_tn < tn` forbids, and it
carries `-100`, which its `n > 0` forbids —
`counterexample_witnesses_are_not_canonical` checks both.  (b) Under the ONE
hypothesis the ledger does supply, `tokensContain_sound` is a theorem.  The witness
therefore delimits the PROOF's hypothesis, not the system's behaviour; the
containment conjunct is not "false in general" in any sense that reaches a
transaction. -/
theorem tokensContain_needs_canonicity_dup :
    tokensContain [(Data.B (ByteString.mk "x"), Data.I 100),
                   (Data.B (ByteString.mk "x"), Data.I (-100))]
                  [(Data.B (ByteString.mk "x"), Data.I 50)] = some true ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "x"), Data.I 100),
       (Data.B (ByteString.mk "x"), Data.I (-100))] = 0 ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "x"), Data.I 50)] = 50 := by
  native_decide

/-- **WHAT `tokensContain` DOES WITHOUT CANONICITY (2/2) — an unsorted required
list and negative quantities on both sides.**  Again a TRUE Lean fact about
`List (Data × Data)`, and nothing more.

`actual = [(x,-5),(z,10)]`, `required = [(z,10),(x,-3)]` with `x < z`: the helper
skips the `x` entry of `actual` because `x < z` (:1402-1403), matches `z`, then
faces an exhausted `actual` with a NEGATIVE requirement, which :1407 accepts —
yet `-5 ≥ -3` is false.

`actual` here is SORTED and duplicate-free; what it violates is `validTxOutValue`'s
`n > 0`.  `required` violates both `prev_tn < tn` and `n > 0`.  Once more, the
one hypothesis `tokensContain_sound` needs — non-negativity of `actual` — is
exactly what this witness breaks, and exactly what the ledger guarantees. -/
theorem tokensContain_needs_canonicity_unsorted :
    tokensContain [(Data.B (ByteString.mk "x"), Data.I (-5)),
                   (Data.B (ByteString.mk "z"), Data.I 10)]
                  [(Data.B (ByteString.mk "z"), Data.I 10),
                   (Data.B (ByteString.mk "x"), Data.I (-3))] = some true ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "x"), Data.I (-5)),
       (Data.B (ByteString.mk "z"), Data.I 10)] = -5 ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "z"), Data.I 10),
       (Data.B (ByteString.mk "x"), Data.I (-3))] = -3 := by
  native_decide

/-! ## 5. WHAT IS STILL MISSING FOR CONJUNCT 2 — one obligation, not two

`P2b_seized_delta_contained` reduces, via §4's additivity, to two obligations.
**(B1) IS NOW DISCHARGED** — `tokensContain_sound` / `tokensContain_sound_of_canon`
above — and only (B2) remains.

**(B1) `tokensContain` is pointwise sound.  PROVED (§4b).**  The earlier text
here said this was "FALSE without a duplicate-freeness/sortedness hypothesis on
both lists" and cited the two witnesses below.  **That was an error, and it
understated what the library had.**  The witnesses are values no ledger can
build: `validTxOutValue` (CardanoLedgerApi/V1/Contexts.lean:787-802 — ada first,
strictly ascending currency symbols, strictly ascending token names, every
quantity `> 0`) is a conjunct of `validRewardingContext`, which every shaped P2
theorem already assumes, and the `ScriptContext` is built BY THE LEDGER from the
transaction — the user-controlled parts are datums and redeemers, not the values
in resolved inputs and outputs.  Under that rule `tokensContain` is sound, and
the proof needs only ONE of its conjuncts (non-negativity of `actual`; not
sortedness, not duplicate-freeness).  `tokensForCS_nonneg` shows the ledger rule
delivers exactly that at the point of use.

**(B2) canonicity must be propagated through the walk.  STILL OPEN.**
`validTxOutValue` bounds the values the ledger hands over; it says nothing about
the INTERMEDIATE token lists the validator computes.  One must still show that
`ptokensForCurrencySymbol`, `ptokenPairsUnionFast`, `psubtractTokens` and
`pnegateTokens` deliver a `tokensNonneg` (in fact, canonical) list to the
`tokensContain` call at `checkBalanceInvariant`
(ProgrammableLogicBase.hs:1504-1506) — note `psubtractTokens` and `pnegateTokens`
manifestly do NOT preserve non-negativity in general, which is why this is a real
obligation and not a formality — and then that the delta accumulator equals
`Σ_pairs (in − out)` on the seized policy (that last step is §4's additivity plus
a `seizeWalk` induction, and is the easy part).

**(B2) IS NOT ATTEMPTED HERE** — a time-boxed decision, recorded so the gap is
visible.  Nothing above assumes it: conjunct 1 does not use it at all, and
conjunct 2 is a `Prop` definition, not a theorem.  §6 is the concrete evidence
that stands in for the missing general proof today, and
`WSC/Props/Shaped/P2ShapedR.lean` / `P2ShapedR2.lean` prove conjunct 2 against
the compiled bytecode over a bounded shape class, where the whole ladder — B1,
B2 and the accumulator step — is discharged by symbolic execution rather than by
this reduction. -/

/-! ## 6. Controls

Four controls, as ARCHITECTURE.md's Tier-0 gates require:
a **model-level positive witness** (the real accepting golden), a **negative
control** (the model does not accept everything), a **tightness stanza** (each
hypothesis of conjunct 1 is load-bearing), and a **concrete check of conjunct 2**
on the goldens (positive on the accepting ones, refuted on the rejecting one). -/

/-- The seize goldens' base credential, decoded from the params datum field the
validator actually reads. -/
def goldenBase : Option Credential :=
  match Diff.ctxOf Terms.programmableSeize_seize_1_input_ctx with
  | none => none
  | some c =>
      match progLogicCredDataOf Diff.ppCS c with
      | none => none
      | some d => IsData.fromData d

/-- Concrete evaluation of conjunct 1's postcondition on a golden. -/
def structureVerdict (d : Data) : Option Bool :=
  match Diff.ctxOf d with
  | none => none
  | some c =>
      match seizedPolicyOf c, pairedOutputsOf c, goldenBase with
      | some cs, some paired, some base =>
          some (WSC.seizeStructurePreserved base cs c.scriptContextTxInfo.txInfoInputs paired)
      | _, _, _ => none

/-- Concrete evaluation of conjunct 2's inequality on a golden, for every token
name that occurs under the seized policy anywhere in the transaction. -/
def containmentVerdict (d : Data) : Option Bool :=
  match Diff.ctxOf d with
  | none => none
  | some c =>
      match seizedPolicyOf c, goldenBase with
      | some cs, some base =>
          let tx := c.scriptContextTxInfo
          let rec names : List (Data × Data) → List TokenName
            | [] => []
            | (Data.B tn, _) :: rest => tn :: names rest
            | _ :: rest => names rest
          let rec collectOut : List TxOut → List TokenName
            | [] => []
            | o :: rest =>
                (match tokensForCS cs o.txOutValue with
                 | some ts => names ts
                 | none => []) ++ collectOut rest
          let rec collectIn : List TxInInfo → List TokenName
            | [] => []
            | i :: rest =>
                (match tokensForCS cs i.txInInfoResolved.txOutValue with
                 | some ts => names ts
                 | none => []) ++ collectIn rest
          let tns :=
            collectIn tx.txInfoInputs ++ collectOut tx.txInfoOutputs ++
              (match tokensForCS cs tx.txInfoMint with
               | some ts => names ts
               | none => [])
          let rec check : List TokenName → Bool
            | [] => true
            | tn :: rest =>
                decide (sumOutAtBase base cs tn tx.txInfoOutputs
                          ≥ sumInAtBase base cs tn tx.txInfoInputs
                            + WSC.mintOf cs tn tx.txInfoMint)
                && check rest
          some (check tns)
      | _, _ => none

/-- **MODEL-LEVEL POSITIVE WITNESS + concrete conjunct 2.**  On BOTH accepting
seize goldens — real transactions the off-chain suite builds and the Haskell
ledger accepts (`WSC/goldens/MANIFEST.md`; and, per
`WSC/Model/SeizeDiff.lean`, accepted by the production bytecode and by the model)
— conjunct 1's postcondition holds, and so does conjunct 2's inequality for every
token name occurring under the seized policy.

So `P2a_seizeModel_preserves_structure` is NON-VACUOUS on real transactions, and
`P2b_seized_delta_contained` is CONFIRMED on them even though its general proof
is missing (§5). -/
theorem accepting_goldens_satisfy_both_conjuncts :
    structureVerdict Terms.programmableSeize_seize_1_input_ctx = some true ∧
    containmentVerdict Terms.programmableSeize_seize_1_input_ctx = some true ∧
    structureVerdict Terms.programmableSeize_seize_2_inputs_partial_with_noise_ctx
      = some true ∧
    containmentVerdict Terms.programmableSeize_seize_2_inputs_partial_with_noise_ctx
      = some true := by
  native_decide

/-- **NEGATIVE CONTROL — the model does not accept everything, and conjunct 2 is
not a tautology.**  On the rejecting seize golden (the `seize-1-input`
transaction with its residual seized-tokens output deleted) the model REJECTS —
and conjunct 2's inequality is FALSE on that very transaction.  So conjunct 2 has
real content: it is refutable, and the transaction that refutes it is precisely
one the validator rejects.

SCOPE OF THIS CONTROL, stated because the same care is owed here as in §4b:
deleting an output from a balanced transaction unbalances it, so this golden is
one of the three that fail `validRewardingContext` on `isBalanced`
(`WSC/Goldens/Audit.lean`'s `verdicts_are_exactly_as_tabulated` /
`remaining_failures_are_tamper_intrinsic`).  It therefore witnesses "the
postcondition is refutable at all", which is what a tautology check needs, and
NOT "an accepted, ledger-legal transaction can refute it".  The refutability of
the postcondition over LEDGER-LEGAL contexts is established separately and
symbolically, by `WSC.P2b_R_tightness` and `WSC.P2b_R_negative_control`
(`WSC/Props/Shaped/P2ShapedR.lean`), both of which carry `validRewardingContext`
as a hypothesis and both of which return `✅ Expected Falsified`. -/
theorem rejecting_golden_is_the_negative_control :
    Diff.modelVerdict Terms.programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx
      = some false ∧
    containmentVerdict
        Terms.programmableSeize_seize_1_input_missing_residual_output_REJECT_ctx
      = some false := by
  native_decide

/-- **TIGHTNESS.**  Each `Option` hypothesis of conjunct 1 is load-bearing rather
than decorative: on the accepting golden all three projections are `some`, and
they resolve to genuinely different data (the seized policy is NOT the params
policy, and the base credential is a script credential).  Were any projection
`none` the theorem's hypotheses would be unsatisfiable and it would be vacuous
for that context. -/
theorem projections_are_satisfiable :
    (match Diff.ctxOf Terms.programmableSeize_seize_1_input_ctx with
     | some c => (seizedPolicyOf c).isSome && (pairedOutputsOf c).isSome
                   && (progLogicCredDataOf Diff.ppCS c).isSome
     | none => false) = true ∧
    goldenBase.isSome = true ∧
    (match Diff.ctxOf Terms.programmableSeize_seize_1_input_ctx with
     | some c => (seizedPolicyOf c == some Diff.ppCS)
     | none => true) = false := by
  native_decide

/-! ## 7. Composition to the deployed bytecode — **RETRACTED at task R1**

Three declarations stood here and are DELETED:

    theorem P2a_bytecode …                -- P2(a) about the production bytecode
    def     P2b_bytecode : Prop           -- P2(b) about the production bytecode
    theorem P2b_model_implies_bytecode …

All three were `P2a_seizeModel_preserves_structure` / `P2b_seized_delta_contained`
transported across `WSC.SeizeModel.seizeModel_faithful`.  **That axiom is FALSE
of the post-#112 bytecode** and was deleted at task R1;
`WSC/Model/SeizeModelRefuted.lean` settles it by computation on two contexts
differing in ONE lovelace leaf (`seize_model_and_bytecode_DISAGREE`), and
`no_faithful_bridge` there refutes the axiom's proposition outright, so no axiom
of that shape may be re-added.  PR #112 deleted the hand-rolled sorted lockstep
walk this model transcribes and replaced it with a CIP-153 builtin value delta,
legalising an ADA TOP-UP on the continuing output that `seizeModel` still
forbids.

**THE COST, STATED PLAINLY.**  The library loses its only UNBOUNDED
(non-shape-limited, non-budget-limited) statement about the seize path.  That
loss is real and is not repaired here.  It was already recorded as a loss at task
N5; task R1 only stops the false axiom from being the thing that carries it.

**WHAT REPLACES IT.**  `WSC/Props/Shaped/P2ShapedR.lean` proves BOTH conjuncts of
P2 against the real compiled `programmableSeize`, at budget 3800 over SHAPE S1R,
citing no model and no faithfulness axiom (`#print axioms` there lists only
`propext, sorryAx, Classical.choice, Quot.sound`).  It is bounded twice — budget
AND shape — where the deleted route was bounded not at all; that is a genuine
trade, and it is the honest one, because the unbounded route's bridge is false
and the shaped route's is a theorem.

**WHAT SURVIVES IN THIS FILE, and in which category.**
* `P2a_seizeModel_preserves_structure` — a TRUE LEAN THEOREM about `seizeModel`,
  kernel-checked, `[propext, Classical.choice, Quot.sound]`, no `sorry`.  It is
  true; it is simply not about the bytecode any more, because the bridge that
  made it so is gone.  Do not quote it as a property of production.
* `sumOutAtBase` / `sumInAtBase`, `tokSum`, `goldenBase` — SPECIFICATION
  VOCABULARY, consumed by the live UPLC theorems in
  `WSC/Props/Shaped/P2ShapedR.lean`.
* `tokensContain_needs_canonicity_dup` /
  `tokensContain_needs_canonicity_unsorted` — TRUE LEAN FACTS about arbitrary
  `List (Data × Data)`.  They were formerly described here as "the reason P2's
  containment conjunct is shape-dependent"; **that description was wrong**.  Both
  witnesses fail `validTxOutValue` — machine-checked by
  `counterexample_witnesses_are_not_canonical` — so neither is a statement about
  any value a ledger can deliver, and under the ledger rule `tokensContain` is
  sound (`tokensContain_sound`, §4b).  What they show is that the ledger
  precondition is LOAD-BEARING for the proof, not that the property is
  shape-dependent: `WSC/Props/Shaped/P2ShapedR2.lean` proves P2b over a shape
  whose values carry two token names apiece.
* §4b's `tokensContain_sound` / `tokensContain_sound_of_canon` /
  `tokensForCS_nonneg` — obligation **B1**, now PROVED in the kernel, no
  `blaster`, no `native_decide`, no axiom.
* `P2b_seized_delta_contained` — still an open `Prop`, as before: obligation
  **B2** (canonicity propagated through the validator's own token-list
  combinators) is what remains. -/

/-! ## 8. AXIOM AUDIT

Printed at build time so the trust base of each result is visible in the build
log and cannot drift silently.  Expected:

* `P2a_seizeModel_preserves_structure` — the standard Lean axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).  **No** `sorry`, no
  `seizeModel_faithful`, no `WSC/Honest.lean` axiom.
* `P2a_bytecode` — **gone** (task R1).  It was the same plus
  `WSC.SeizeModel.seizeModel_faithful`, and that axiom is false; with it deleted
  no result in this file reaches any project axiom at all.
* the golden theorems — additionally `Lean.ofReduceBool` (the `native_decide`
  compiler-trust axiom), as everywhere else in this library
  (`WSC/Goldens/*.lean`). -/
#print axioms WSC.P2.P2a_seizeModel_preserves_structure
#print axioms WSC.P2.accepting_goldens_satisfy_both_conjuncts
#print axioms WSC.P2.rejecting_golden_is_the_negative_control
#print axioms WSC.SeizeModel.Diff.all_13_model_agrees_with_bytecode
#print axioms WSC.SeizeModel.Diff.all_3_model_agrees_with_recorded_ledger_verdict

end WSC.P2
