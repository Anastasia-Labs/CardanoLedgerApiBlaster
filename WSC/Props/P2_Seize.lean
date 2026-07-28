-- ⛔ REFUTED AT PR #112: `seizeModel_faithful` is FALSE at main 2306678 — machine-checked counterexample in WSC/Model/SeizeModelRefuted.lean. The 13/13 differential test still passes but no golden covers the change. Results bridged by that axiom are INVALID for production.
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
* **The bytecode-level result** (§7) is conjunct 1 composed with the ONE
  fidelity axiom `WSC.SeizeModel.seizeModel_faithful`.  That axiom is the whole
  trust delta of this route: read its docstring (`WSC/Model/SeizeModel.lean` §7)
  and the 13/13 differential evidence (`WSC/Model/SeizeDiff.lean`) before
  quoting the composed theorem.

WHY THE SOURCE-MODEL ROUTE AT ALL.  P2 is measured out of reach at UPLC:
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

SCOPE: this is a theorem about `WSC.SeizeModel.seizeModel`.  For the bytecode
statement see §7 — it adds `seizeModel_faithful`. -/
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

/-- **FINDING (B1a) — machine-checked counterexample: `ptokenPairsContain` is NOT
pointwise sound when the "actual" list has DUPLICATE token names.**

`actual = [(x,100),(x,-100)]`, `required = [(x,50)]`: the helper matches the first
pair (`100 ≥ 50`, ProgrammableLogicBase.hs:1400), the required list is then
exhausted and it returns `True` (:1410) — while the actual per-name total is 0,
which does not cover 50.

This is not a defect of the deployed system: on chain every `Value` is
`validTxOutValue`-canonical (CardanoLedgerApi/V1/Contexts.lean:769-789), which
forbids duplicate names.  It IS the precise reason conjunct 2 cannot be proven
without carrying that ledger rule as a hypothesis, and it is why the containment
half of P2 is harder than the structural half. -/
theorem tokensContain_unsound_with_duplicate_names :
    tokensContain [(Data.B (ByteString.mk "x"), Data.I 100),
                   (Data.B (ByteString.mk "x"), Data.I (-100))]
                  [(Data.B (ByteString.mk "x"), Data.I 50)] = some true ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "x"), Data.I 100),
       (Data.B (ByteString.mk "x"), Data.I (-100))] = 0 ∧
    tokSum (ByteString.mk "x")
      [(Data.B (ByteString.mk "x"), Data.I 50)] = 50 := by
  native_decide

/-- **FINDING (B1b) — machine-checked counterexample: duplicate-freeness alone is
not enough; the lists must be SORTED by token name.**

`actual = [(x,-5),(z,10)]`, `required = [(z,10),(x,-3)]` with `x < z`: the helper
skips the `x` entry of `actual` because `x < z` (:1402-1403), matches `z`, then
faces an exhausted `actual` with a NEGATIVE requirement, which :1407 accepts —
yet `-5 ≥ -3` is false.  Again sortedness is a ledger rule on chain
(`validTxOutValue` clause 3), so this bounds the PROOF, not the system. -/
theorem tokensContain_unsound_when_unsorted :
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

/-! ## 5. WHAT IS MISSING FOR CONJUNCT 2 — stated, not hidden

`P2b_seized_delta_contained` reduces, via §4's additivity, to TWO further
obligations, and NEITHER is discharged in this file:

**(B1) `tokensContain` is pointwise sound — only under canonicity.**
`tokensContain actual required = true → ∀ tn, tokSum tn actual ≥ tokSum tn required`
is **FALSE** without a duplicate-freeness/sortedness hypothesis on both lists.
Counterexample found while developing this ladder (a real finding about the
helper, recorded here rather than papered over):
`actual = [(x,100),(x,-100)]`, `required = [(x,50)]`.  `ptokenPairsContain`
matches the first pair (`100 ≥ 50`), then the required list is exhausted and it
returns `True` (ProgrammableLogicBase.hs:1410) — while `tokSum x actual = 0 <
50`.  A second counterexample breaks it with duplicate-free but UNSORTED lists:
`actual = [(x,-5),(z,10)]`, `required = [(z,10),(x,-3)]` with `x < z` — accepted,
yet `-5 ≥ -3` is false.  So the ladder genuinely needs the values to be
CS-sorted and token-name-sorted, which on chain they are: it is the ledger rule
`validTxOutValue` (CardanoLedgerApi/V1/Contexts.lean:769-789, a conjunct of
`validRewardingContext`).  This is exactly the load-bearing precondition
ARCHITECTURE.md §3-P2 flags ("`validTxOutValue` on every value — load-bearing
since the seize walk assumes well-formed sorted values").

**(B2) sortedness must be propagated through the walk.**
Even given `validTxOutValue` on every input and output value, one must show that
`ptokensForCurrencySymbol`, `ptokenPairsUnionFast`, `psubtractTokens` and
`pnegateTokens` all PRESERVE token-name sortedness, so that (B1) applies to the
lists that `checkBalanceInvariant` actually compares, and then that the delta
accumulator equals `Σ_pairs (in − out)` on the seized policy (this last step is
§4's additivity plus a `seizeWalk` induction, and is the easy part).

NEITHER (B1) NOR (B2) IS ATTEMPTED HERE — a time-boxed decision, recorded so the
gap is visible.  Nothing above assumes them: conjunct 1 does not use them at
all, and conjunct 2 is a `Prop` definition, not a theorem.  §6 is the concrete
evidence that stands in for the missing general proof today. -/

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
one the validator rejects. -/
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

/-! ## 7. Composition — from the model to the deployed bytecode

The dependency is deliberately made explicit as a theorem so it cannot be lost:
P2(a) about the bytecode = P2(a) about the model + `seizeModel_faithful`. -/

/-- **P2 (a) ABOUT THE PRODUCTION BYTECODE** (structure preservation).

*If the deployed `programmableSeize` script accepts a transaction (at ANY step
count — this statement is not budget-bounded, unlike every other row of
`WSC/STATUS.md`), then that transaction relocates only the seized policy: every
mini-ledger input is paired with a continuing output at the same address with the
same datum and reference script, differing at most in the seized policy.*

DEPENDENCIES, IN FULL: `P2a_seizeModel_preserves_structure` (kernel-checked, no
`sorry`) and `WSC.SeizeModel.seizeModel_faithful` (the ONE unproven bridge —
`WSC/Model/SeizeModel.lean` §7; evidence: clause-by-clause transcription with
line citations, and 13/13 golden differential agreement including the rejecting
seize golden, `WSC/Model/SeizeDiff.lean`).  No `WSC/Honest.lean` axiom is used:
in particular no `LR_BUDGET_seize` (there is none) and no `DirWF` — the seized
policy is taken from whatever node the redeemer points at, and P2 does not claim
that node is authentic.  The claim "the node is authentic" is a separate
obligation (ARCHITECTURE.md's L2.5) that lives with `DirWF`. -/
theorem P2a_bytecode
    (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol) (paired : List TxOut)
    (hacc : seizeAcceptsUnbounded ppCS ctx)
    (hcs : seizedPolicyOf ctx = some seizedCS)
    (hout : pairedOutputsOf ctx = some paired)
    (hbase : progLogicCredDataOf ppCS ctx = some (IsData.toData base)) :
    WSC.seizeStructurePreserved base seizedCS
      ctx.scriptContextTxInfo.txInfoInputs paired = true :=
  P2a_seizeModel_preserves_structure ppCS base ctx seizedCS paired
    ((seizeModel_faithful ppCS ctx).mpr hacc) hcs hout hbase

/-- The same composition for conjunct 2, kept as a `Prop` so the shape of the
remaining work is explicit: discharging `P2b_seized_delta_contained` (§5) would
immediately give the bytecode statement by the same one-line composition. -/
def P2b_bytecode : Prop :=
  ∀ (ppCS : CurrencySymbol) (base : Credential) (ctx : ScriptContext)
    (seizedCS : CurrencySymbol),
    seizeAcceptsUnbounded ppCS ctx →
    seizedPolicyOf ctx = some seizedCS →
    progLogicCredDataOf ppCS ctx = some (IsData.toData base) →
    ∀ tn : TokenName,
      sumOutAtBase base seizedCS tn ctx.scriptContextTxInfo.txInfoOutputs
        ≥ sumInAtBase base seizedCS tn ctx.scriptContextTxInfo.txInfoInputs
          + WSC.mintOf seizedCS tn ctx.scriptContextTxInfo.txInfoMint

theorem P2b_model_implies_bytecode :
    P2b_seized_delta_contained → P2b_bytecode := by
  intro h ppCS base ctx seizedCS hacc hcs hbase tn
  exact h ppCS base ctx seizedCS ((seizeModel_faithful ppCS ctx).mpr hacc) hcs hbase tn

/-! ## 8. AXIOM AUDIT

Printed at build time so the trust base of each result is visible in the build
log and cannot drift silently.  Expected:

* `P2a_seizeModel_preserves_structure` — the standard Lean axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).  **No** `sorry`, no
  `seizeModel_faithful`, no `WSC/Honest.lean` axiom.
* `P2a_bytecode` — the same plus `WSC.SeizeModel.seizeModel_faithful`, and
  nothing else.  That single extra name IS the trust delta of the source-model
  route.
* the golden theorems — additionally `Lean.ofReduceBool` (the `native_decide`
  compiler-trust axiom), as everywhere else in this library
  (`WSC/Goldens/*.lean`). -/
#print axioms WSC.P2.P2a_seizeModel_preserves_structure
#print axioms WSC.P2.P2a_bytecode
#print axioms WSC.P2.P2b_model_implies_bytecode
#print axioms WSC.P2.accepting_goldens_satisfy_both_conjuncts
#print axioms WSC.P2.rejecting_golden_is_the_negative_control
#print axioms WSC.SeizeModel.Diff.all_13_model_agrees_with_bytecode
#print axioms WSC.SeizeModel.Diff.all_3_model_agrees_with_recorded_ledger_verdict

end WSC.P2
