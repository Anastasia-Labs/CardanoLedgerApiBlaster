/-
WSC/Props/P5_NonMember.lean — P5, the ESCAPE-CRITICAL property
(arch §3-P5, ADDENDUM E3, unit U6).

PLAIN ENGLISH (ADDENDUM E3 wording is binding — the postcondition is the
covering-node witness, NOT `¬ IsRegistered`):

> If the global (transfer) validator accepts a transaction in which some policy
> was classified `NonMember` — i.e. claimed exempt from the containment
> requirement — then the transaction really does reference an authentic
> directory node whose key interval strictly covers that policy
> (`key < cs` and `cs < next`). Because the directory is a sorted,
> unique-keyed, sentinel-bounded partition of the key space (the DirWF
> assumption, ADDENDUM E4), such a covering node can only exist when the policy
> is genuinely unregistered. **You cannot buy a containment exemption for a
> registered programmable token.**

══════════════════════════════════════════════════════════════════════════════
OBLIGATION STATUS (READ FIRST) — **P5 IS NOT PROVED IN THIS MODULE.**
══════════════════════════════════════════════════════════════════════════════
Measured on 2026-07-25 (task Y1), 32-core box, `lake build`, `maxHeartbeats 0`,
against the real bytecode prepped at budget 1600 (WSC/Prep/Global1600.lean):

| obligation | invocation | outcome |
|---|---|---|
| P5 indexed (the bytecode obligation) + negative control + tightness, in one module | `theorem … := by blaster` ×2 and `#blaster … [P5_tightness]` | **killed at 5241 s ≈ 87 min, NO verdict** (not `Valid`, not `Undetermined`, no cex) |
| mandatory vacuity probe of the 1600 prep | `#blaster (gen-cex: 1) (solve-result: 1)` in its own module | **killed at 5241 s ≈ 87 min, NO verdict** |
| same vacuity probe, Z3 CAPPED | `#blaster (timeout: 120) (solve-result: 1)` | **`⚠️ Undetermined` in 120.1 s** |
| indexed + negative control + tightness, Z3 capped at 300 s each | three `#blaster (timeout: 300) …` in one module | **killed at 1454 s, no verdict printed** (the cap is per Z3 QUERY, not per goal) |

WHERE THE COST IS (diagnostic, this task). The Z3-capped run above is decisive:
Blaster TRANSLATES the 1600-step residual goal fine and returns a verdict as
soon as the solver is capped — so neither `#prep_uplc` (50.1 s) nor the
translate/optimize step is the wall. **The wall is the SMT search itself**, and
what it returns is `Undetermined`, i.e. Z3 neither proves nor refutes the query.
So the honest reading of the missing vacuity certificate is
"solver-undetermined", NOT "vacuous": the 600-step prep is *provably* vacuous
(`✅ Valid`), whereas at 1600 Z3 simply does not decide. The concrete golden
witness (WSC/Props/P5_Witness1600.lean) is what tells us the truth is
"non-vacuous".

Consequently every bytecode-level statement below is a `Prop` DEFINITION with
the `#blaster` command recorded in its doc comment, never a `theorem`. What IS
machine-checked here is only what is genuinely proved: the mirror definitions,
and the pure-Lean reduction lemmas
(`nthFrom_mem`, `coversCS_elim`, `hasCoveringNode_of_mem`,
`authenticDirNode_of_authH`, `dirNodeKeyRaw_of_datum`,
`classifiedNonMember_of_nodeIdx`, `P5_exists_of_indexed`,
`P5_groundtruth_of_indexed`) — i.e. the whole ladder ABOVE the bytecode step,
including "(ii)+(iii) ⟹ (i)" and "bytecode-shaped ⟹ ground-truth".

Non-vacuity of budget 1600 is nevertheless established CONCRETELY and
independently of the solver, by WSC/Props/P5_Witness1600.lean: the real
compiled validator with the real golden NonMember/covering-node
`ScriptContext` applied HALTS at budget 1600 and budget-errors at 1553
(K = 1554, WSC/goldens/K-MEASUREMENTS.md §3). So the statements below are known
to be about a non-empty set of transactions — what is missing is the solver
verdict, not the witness.
══════════════════════════════════════════════════════════════════════════════

Stated against the ACTUAL compiled production bytecode
(`WSC/flats/programmableLogicGlobal.flat`, prepped in WSC/Prep/Global1600.lean
at CEK step budget 1600).

SCOPE (ADDENDUM E1, binding). `#prep_uplc … 1600` bakes a concrete CEK step
budget into `appliedGlobal1600.prop`; budget exhaustion evaluates to `Error`
and `isSuccessful` is then false. Every theorem below is therefore
BOUNDED-TRANSACTION model checking of the real bytecode: it constrains exactly
those invocations of the transfer validator whose run halts within **1600 CEK
steps** (bridged to real node acceptance by the LR-BUDGET axiom family in
WSC/Honest.lean). 1600 was chosen because the CHEAPEST accepting golden of this
validator, `programmableLogicGlobal.transfer-nonmember-covering-node`, halts in
**K = 1554** steps (WSC/goldens/K-MEASUREMENTS.md §3) — and that golden is
exactly P5's subject shape, and it HALTS inside the bound (concretely verified
in WSC/Props/P5_Witness1600.lean). It does NOT
cover the containment-carrying transfers (K = 3262 / 3726, P1's shapes), whose
symbolic prep is out of reach (K-MEASUREMENTS §5.2).

P5's STRENGTH IS EXACTLY DirWF's STRENGTH (ADDENDUM E4). What P5 CLAIMS (and
what a discharge of the obligation below would establish) is the covering-node
WITNESS: the bytecode really did authenticate a referenced node against the
deployment's directory policy and really did check the strict interval
`key < cs < next`. Turning that witness into "`cs` is not registered"
is the composition-layer step
`covering_node_excludes_registration : (∃ authentic covering node for cs) ∧ DirWF ⟹ cs ∉ R L`,
and it consumes DirWF conjuncts (ii) global key-uniqueness and (iii) NFT-name =
key datum binding, plus TS4's `key < next` order. Those are ASSUMED
(WSC/Honest.lean `DIRWF`, `TS4`); discharging them by a UPLC-level proof of
`mkDirectoryNodeMP` (deferred unit U10) is what would make the top claim rest
on nothing but TS1-TS5/LR1-LR7.

PRECONDITION AUDIT (arch §4.1 may-assume / must-not-assume):

MAY assume (and does):
* `validRewardingContext ctx` — CLAB ledger normalization ONLY (rewarding
  purpose; canonical/sorted values, mint, withdrawals, redeemer map; balanced
  tx). It never inspects `scriptContextRedeemer`'s CONTENT
  (CardanoLedgerApi/V3/Contexts.lean:1197-1246), so all attacker-controlled
  redeemer data — proof list, node indices, params index — stays adversarial.
* Pure PROJECTIONS of the (adversarial) redeemer and of the context, used only
  to NAME the objects the postcondition talks about: the params reference
  index, the directory policy the params datum at that index publishes, the
  `NonMember` node index positionally assigned to `cs`, and the reference input
  sitting at that index. Naming is not assuming: each projection is a total
  function of `(ctx, redeemer)` that the validator itself computes.

MUST NOT assume (and does not):
* NOTHING about the reference inputs being authentic directory nodes, or about
  their datums being well-formed, or about the covering interval — that is the
  POSTCONDITION, earned from the bytecode.
* NOTHING about the params reference input being NFT-authenticated (the
  validator's own `phasCSH` gate inside `pparamsAtRefIdx` forces it on the
  accept path — ProgrammableLogicBase.hs:829-838).
* No `HonestParams`/`Deployed`/`OnChain`/DirWF hypothesis in the bytecode
  statement. They appear ONLY in the clearly-labelled ground-truth reduction
  `P5_groundtruth_of_indexed`, which restates the same conclusion in
  WSC/Honest.lean's vocabulary and needs TS3 for the datum decode.
* `isTransferAct` is NOT assumed: it is IMPLIED by
  `nonMemberNodeIdxOf cs ctx = some nodeIdx` (only the `TransferAct` arm of the
  redeemer carries mint proofs; the `SeizeAct` arm of this validator is a hard
  `perror`, ProgrammableLogicBase.hs:1270).

SOURCE FIDELITY — the checks P5's postcondition mirrors, cited into
the Plutarch source of truth
(wsc-poc:src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs,
worktree `new-session-3c417d`):

* :1176-1177  `mkProgrammableLogicGlobal :: PAsData PCurrencySymbol :--> PScriptContext :--> PUnit`
              (1 script parameter, then ctx — the shape of `globalInputs1600`).
* :1190-1264  the `PTransferAct` arm: `referenceInputs` is `ptxInfo'referenceInputs`
              (:1195), the params UTxO is resolved at the redeemer's
              `paramsRefIdx` (:1196-1199) and `pdirectoryNodeCS` is read out of
              its datum — this is the `dirCS` the mint walk authenticates
              against, and the reason `paramsDatumDirCSRaw` at that index is the
              faithful way to NAME `dirCS`.
* :1240-1250  the mint walk `pcheckMintLogicAndGetProgrammableValue
              (pfromData pdirectoryNodeCS) referenceInputs (pfromData mintProofs)
              mintValueNoGuarantees` — the SAME `referenceInputs` list and the
              SAME directory policy.
* :982-1026   the lockstep walk itself: one `MintProof` is consumed per non-Ada
              `txInfoMint` entry, in ascending currency-symbol order
              (`mintedEntries = pto (pto totalMintValue)`, :983-984); a missing
              proof is `ptraceInfoError "mint proof missing"` (:1018) and an
              extra proof is `ptraceInfoError "extra mint proof"` (:1024).
              THIS is what makes the classification POSITIONAL (ADDENDUM E8) and
              is exactly what `WSC/Spec.lean`'s `mintProofFor` mirrors.
* :996-1015   the `PNonMember nodeIdx` branch:
              - :997-998  the node is `refInputs[nodeIdx]`, resolved via
                          `phead # (pdropList # pfromData nodeIdx # refInputs)`
                          — mirrored by `nthFrom refInputs nodeIdx.toNat`;
              - :999      `POutputDatum paramDat'` — an INLINE datum is
                          required (a datum hash or no datum fails to match);
              - :1000-1004 `punsafeCoerce @(PAsData PDirectorySetNode)` then
                          `pkey` / `pnext`. NOTE (fidelity, load-bearing): the
                          coerce performs NO datum validation, and
                          `PDirectorySetNode` is a `DeriveAsDataRec` record, so
                          the bytecode reads POSITION 0 and POSITION 1 of a
                          `Data.List` datum. `dirNodeKeyRaw` / `dirNodeNextRaw`
                          mirror precisely that, and are deliberately weaker
                          than WSC/Honest.lean's `dirNodeKey`/`dirNodeNext`
                          (which additionally require the full 5-field
                          `DirectorySetNode` decode — PTokenDirectory.hs:144-174).
                          The gap is bridged by TS3 in the corollary below.
              - :1009     `nodeKey #< currCS`   ⟶ `k < cs`
              - :1010     `currCS #< nodeNext`  ⟶ `cs < n`
                          (`#<` on `PCurrencySymbol` compiles to the
                          `lessThanByteString` builtin, whose PCB denotation is
                          literally `b1 < b2` on `ByteString` —
                          PlutusCore/ByteString/Basic.lean:185, :88 — i.e. the
                          `<` written in `coversCS` IS the on-chain relation);
              - :1011     `phasCSH # directoryNodeCS # directoryNodeUTxOFValue`
                          ⟶ `dirNodeAuthH`. `phasCSH` (:754-757) checks that the
                          FIRST NON-ADA policy entry of the node's value is
                          `directoryNodeCS` (`pfstBuiltin # (phead # (ptail #
                          value'))`), which is what `dirNodeAuthH` mirrors
                          byte-for-byte; `authenticDirNode_of_authH` below then
                          derives ground-truth membership from it, so the
                          weaker-shape check is not a soundness hole here.
              - :1013-1015 all three checks are `pand'List`-ed and a failure is
                          `perror` — so on an accepting run ALL THREE hold.
-/
import WSC.Prep.Global1600
import WSC.Honest
import WSC.Spec
import Blaster

-- The 1600-step prep is a large residual term; blaster's solve on it must not
-- be cut short by the default heartbeat cap.
set_option maxHeartbeats 0
-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false

namespace WSC

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext TxInInfo TxOut
                          hasCurrencySymbol validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

namespace P5

/-! ## Positional list access — the mirror of `phead # (pdropList # i # l)`

`pdropList` is the CIP-153-era `dropList` builtin; PCB's denotation is
`xs.drop n.toNat` (PlutusCore/UPLC/BuiltinFunctions/List.lean:102-110), so a
negative index behaves as `drop 0` and an out-of-range index leaves `[]`, on
which the validator's `phead` `perror`s. `nthFrom l i.toNat` is exactly
`(l.drop i.toNat).head?`, written as a pattern-match recursion because blaster
does not digest the stdlib list combinators (SPIKE-FINDINGS, F row). -/
def nthFrom : List TxInInfo → Nat → Option TxInInfo
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: rest, n + 1 => nthFrom rest n

/-- Indexing yields a genuine list member — this is what upgrades the indexed
theorem to the `∃`-form postcondition of ADDENDUM E3. -/
theorem nthFrom_mem : ∀ (l : List TxInInfo) (n : Nat) (t : TxInInfo),
    nthFrom l n = some t → t ∈ l := by
  intro l
  induction l with
  | nil => intro n t h; cases n <;> simp [nthFrom] at h
  | cons hd tl ih =>
      intro n t h
      cases n with
      | zero => simp [nthFrom] at h; simp [h]
      | succ m => exact List.mem_cons_of_mem _ (ih m t (by simpa [nthFrom] using h))

/-! ## The three NonMember checks, mirrored exactly (ProgrammableLogicBase.hs:1009-1011) -/

/-- `phasCSH dirCS value` (ProgrammableLogicBase.hs:754-757): the FIRST non-Ada
policy entry of the node's value is the directory policy. Deliberately the
validator's own (cheap, shape-based) authentication, not ground-truth
membership — see `authenticDirNode_of_authH`. -/
def dirNodeAuthH (dirCS : CurrencySymbol) (o : TxOut) : Bool :=
  match o.txOutValue with
  | _ :: (Data.B cs', _) :: _ => cs' == dirCS
  | _ => false

/-- `pkey` of the node datum as the bytecode reads it: position 0 of an INLINE
`Data.List` datum, with no validation of the remaining fields
(`punsafeCoerce`, ProgrammableLogicBase.hs:1000-1004). -/
def dirNodeKeyRaw (o : TxOut) : Option CurrencySymbol :=
  match o.txOutDatum with
  | .OutputDatum (Data.List (Data.B k :: _)) => some k
  | _ => none

/-- `pnext` of the node datum as the bytecode reads it: position 1. -/
def dirNodeNextRaw (o : TxOut) : Option CurrencySymbol :=
  match o.txOutDatum with
  | .OutputDatum (Data.List (_ :: Data.B n :: _)) => some n
  | _ => none

/-- The strict covering interval: `key < cs < next`
(ProgrammableLogicBase.hs:1009-1010). -/
def coversCS (cs : CurrencySymbol) (o : TxOut) : Bool :=
  match dirNodeKeyRaw o, dirNodeNextRaw o with
  | some k, some n => k < cs && cs < n
  | _, _ => false

/-- Some reference input is an authenticated directory node whose interval
strictly covers `cs`. The `∃`-form of ADDENDUM E3's postcondition, as a
pattern-match recursion. -/
def hasCoveringNode (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | t :: rest =>
      (dirNodeAuthH dirCS t.txInInfoResolved && coversCS cs t.txInInfoResolved)
      || hasCoveringNode dirCS cs rest

theorem hasCoveringNode_of_mem
    (dirCS cs : CurrencySymbol) (l : List TxInInfo) (t : TxInInfo)
    (hm : t ∈ l)
    (ha : dirNodeAuthH dirCS t.txInInfoResolved = true)
    (hc : coversCS cs t.txInInfoResolved = true) :
    hasCoveringNode dirCS cs l = true := by
  induction l with
  | nil => cases hm
  | cons hd tl ih =>
      rcases List.mem_cons.mp hm with h | h
      · subst h; simp [hasCoveringNode, ha, hc]
      · simp [hasCoveringNode, ih h]

theorem coversCS_elim (cs : CurrencySymbol) (o : TxOut) (h : coversCS cs o = true) :
    ∃ k n, dirNodeKeyRaw o = some k ∧ dirNodeNextRaw o = some n ∧ k < cs ∧ cs < n := by
  cases hk : dirNodeKeyRaw o with
  | none => simp [coversCS, hk] at h
  | some k =>
    cases hn : dirNodeNextRaw o with
    | none => simp [coversCS, hk, hn] at h
    | some n =>
      simp [coversCS, hk, hn] at h
      exact ⟨k, n, rfl, rfl, h.1, h.2⟩

/-! ## Bridges to the ground-truth vocabulary of WSC/Honest.lean -/

/-- The validator's cheap `phasCSH` authentication IMPLIES ground-truth
directory-token membership (`authenticDirNode`). Discharges the AUDIT NOTE at
WSC/Honest.lean:45-50 in the direction P5 needs — no TS5 required. -/
theorem authenticDirNode_of_authH (dirCS : CurrencySymbol) (o : TxOut)
    (h : dirNodeAuthH dirCS o = true) : authenticDirNode dirCS o = true := by
  unfold dirNodeAuthH at h
  unfold authenticDirNode
  match hv : o.txOutValue with
  | [] => rw [hv] at h; simp at h
  | _ :: [] => rw [hv] at h; simp at h
  | a :: (d, m) :: rest =>
      rw [hv] at h
      cases d with
      | B b => simp at h; subst h; simp [hasCurrencySymbol]
      | _ => simp at h

/-- When the node's datum DOES decode as a full `DirectorySetNode`, the
bytecode's positional reads agree with `WSC/Honest.lean`'s decoded accessors. -/
theorem dirNodeKeyRaw_of_datum (o : TxOut) (d : DirectorySetNode)
    (h : dirNodeDatum o = some d) :
    dirNodeKeyRaw o = some d.key ∧ dirNodeNextRaw o = some d.next := by
  unfold dirNodeDatum at h
  split at h
  · rename_i dat heq
    simp only [IsData.fromData] at h
    split at h
    · rename_i k n r1 r2 g _
      split at h
      · rename_i tls ils _
        cases h
        exact ⟨by simp [dirNodeKeyRaw, heq], by simp [dirNodeNextRaw, heq]⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Redeemer / context projections that NAME the objects (no honesty assumed) -/

/-- The `paramsRefIdx` field of a `TransferAct` redeemer
(ProgrammableLogicBase.hs:1053, mirrored in WSC/Redeemer.lean). -/
def transferParamsRefIdx (r : Data) : Option Integer :=
  match (IsData.fromData r : Option PLGRedeemer) with
  | some (.TransferAct _ _ _ i) => some i
  | _ => none

/-- `pdirectoryNodeCS` as the bytecode reads it out of the params datum:
position 0 of an inline `Data.List` datum (`punsafeCoerce
@(PAsData PProgrammableLogicGlobalParams)`, ProgrammableLogicBase.hs:834-836;
field order is normative — ProtocolParams.hs:44-68). -/
def paramsDatumDirCSRaw (o : TxOut) : Option CurrencySymbol :=
  match o.txOutDatum with
  | .OutputDatum (Data.List (Data.B dcs :: _)) => some dcs
  | _ => none

/-- POSITIONAL `NonMember` classification with its node index (ADDENDUM E8).
`WSC/Spec.lean`'s `mintProofFor` walks the proof list in lockstep with the
sorted `txInfoMint` entries, exactly as the validator does
(ProgrammableLogicBase.hs:984-1026), so this is "the proof at `cs`'s POSITION",
never "some proof in the list says NonMember". -/
def nonMemberNodeIdxOf (cs : CurrencySymbol) (ctx : ScriptContext) : Option Integer :=
  match transferMintProofs ctx.scriptContextRedeemer with
  | some ps =>
      match mintProofFor cs ps ctx.scriptContextTxInfo.txInfoMint with
      | some (.NonMember i) => some i
      | _ => none
  | none => none

/-- Naming the node index is exactly the `classifiedNonMember` predicate of
WSC/Spec.lean (audit link for ADDENDUM E8: the precondition below is the
positional classification and nothing more). -/
theorem classifiedNonMember_of_nodeIdx (cs : CurrencySymbol) (ctx : ScriptContext)
    (i : Integer) (h : nonMemberNodeIdxOf cs ctx = some i) :
    ∃ ps, transferMintProofs ctx.scriptContextRedeemer = some ps ∧
          classifiedNonMember ps ctx.scriptContextTxInfo.txInfoMint cs = true := by
  unfold nonMemberNodeIdxOf at h
  split at h
  · rename_i ps hps
    refine ⟨ps, hps, ?_⟩
    unfold classifiedNonMember
    split at h
    · rename_i j hj; rw [hj]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end P5


/-! ## P5 — the escape-critical property: STATEMENT + reduction lemmas

READ THE "OBLIGATION STATUS" BLOCK IN THE MODULE HEADER FIRST. The bytecode
obligation below is STATED, not discharged: `#blaster` did not return a verdict
on it within 87 minutes. Nothing in this section asserts that the property
holds; the only `theorem`s here are the pure-Lean REDUCTIONS between the three
postcondition strengths (i)/(ii)/(iii) of the task's weakening ladder, which are
proved unconditionally and are what a future discharge would be plugged into. -/

open P5

/-- **P5 (escape-critical), indexed form — THE BYTECODE OBLIGATION, NOT PROVED.**

*If the transfer validator accepts, and policy `cs` was classified `NonMember`
at its position in the mint walk with node index `nodeIdx`, then the reference
input at `nodeIdx` really is authenticated as a directory node of the policy
`dirCS` published by the params datum the validator itself read, and its
`(key, next)` interval strictly covers `cs`.*

The two conclusions are, verbatim, the three `pand'List` conditions of the
`PNonMember` branch (ProgrammableLogicBase.hs:1009-1011): `dirNodeAuthH` is
`phasCSH`, `coversCS` is `nodeKey #< currCS` ∧ `currCS #< nodeNext`. Together
they are the task's strength (ii) + (iii); `P5_exists_of_indexed` below turns
them into strength (i), ADDENDUM E3's ∃-form, so (ii)+(iii) ⟹ (i) is a THEOREM
here, not a hand-wave — the only thing (i) needs beyond them is the index
witness, discharged by `nthFrom_mem`.

Bounded to runs halting within 1600 CEK steps (ADDENDUM E1; module header).

STATUS: stated as a `Prop`. `#blaster` on it (as a `theorem … := by blaster`,
inside `lake build`, `maxHeartbeats 0`) was killed at 5241 s ≈ 87 min with NO
verdict — neither `Valid` nor `Undetermined` nor a counterexample. See the
module header. -/
def P5_nonmember_covering_node_indexed : Prop :=
  ∀ (protocolParamsCS dirCS cs : CurrencySymbol) (pIdx nodeIdx : Integer)
    (paramsIn node : TxInInfo) (ctx : ScriptContext),
    validRewardingContext ctx →
    transferParamsRefIdx ctx.scriptContextRedeemer = some pIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs pIdx.toNat = some paramsIn →
    paramsDatumDirCSRaw paramsIn.txInInfoResolved = some dirCS →
    nonMemberNodeIdxOf cs ctx = some nodeIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs nodeIdx.toNat = some node →
    isSuccessful (appliedGlobal1600.prop protocolParamsCS ctx) →
      dirNodeAuthH dirCS node.txInInfoResolved = true
      ∧ coversCS cs node.txInInfoResolved = true

/-- **(ii)+(iii) ⟹ (i): the ADDENDUM E3 ∃-form is a consequence of the indexed
form.** PROVED (pure Lean, no bytecode): if the node the redeemer names passes
the directory authentication and the covering-interval checks, then the
transaction genuinely REFERENCES an authentic covering directory node. This is
the reduction the composition layer's `covering_node_excludes_registration`
consumes. -/
theorem P5_exists_of_indexed
    (dirCS cs : CurrencySymbol) (node : TxInInfo) (refIns : List TxInInfo) (i : Nat)
    (hnode : nthFrom refIns i = some node)
    (ha : dirNodeAuthH dirCS node.txInInfoResolved = true)
    (hc : coversCS cs node.txInInfoResolved = true) :
    ∃ t ∈ refIns,
      dirNodeAuthH dirCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKeyRaw t.txInInfoResolved = some k ∧
             dirNodeNextRaw t.txInInfoResolved = some n ∧ k < cs ∧ cs < n :=
  ⟨node, nthFrom_mem _ _ _ hnode, ha, coversCS_elim cs _ hc⟩

/-- **Ground-truth restatement.** PROVED (pure Lean + one named axiom): the same
conclusion in WSC/Honest.lean's vocabulary — `authenticDirNode` (ground-truth
directory-token membership) and `dirNodeKey`/`dirNodeNext` (the FULL 5-field
`DirectorySetNode` decode).

Two bridges are needed, and only one is an assumption:
* `phasCSH` ⟹ membership is PROVED here (`authenticDirNode_of_authH`);
* the datum decoding as a well-formed `DirectorySetNode` is ASSUMED, via TS3
  (WSC/Honest.lean:160-165). It cannot come from the bytecode: the validator
  `punsafeCoerce`s the datum and reads only positions 0/1
  (ProgrammableLogicBase.hs:1000-1004). TS3 delegates to the directory minting
  policy / directory spending script (deferred unit U10). -/
theorem P5_groundtruth_of_indexed
    (hp0 : HonestParams) (cs : CurrencySymbol) (node : TxInInfo) (ctx : ScriptContext)
    (i : Nat)
    (hdep : Deployed hp0) (hoc : OnChain ctx)
    (hnode : nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs i = some node)
    (ha : dirNodeAuthH hp0.directoryNodeCS node.txInInfoResolved = true)
    (hc : coversCS cs node.txInInfoResolved = true) :
    ∃ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp0.directoryNodeCS t.txInInfoResolved = true ∧
      ∃ k n, dirNodeKey t.txInInfoResolved = some k ∧
             dirNodeNext t.txInInfoResolved = some n ∧ k < cs ∧ cs < n := by
  have hmem : node ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs := nthFrom_mem _ _ _ hnode
  have hauth : authenticDirNode hp0.directoryNodeCS node.txInInfoResolved = true :=
    authenticDirNode_of_authH _ _ ha
  obtain ⟨k, n, hk, hn, hlt1, hlt2⟩ := coversCS_elim cs _ hc
  have hsome : (dirNodeDatum node.txInInfoResolved).isSome :=
    TS3 hp0 ctx hdep hoc node hmem hauth
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hkr, hnr⟩ := dirNodeKeyRaw_of_datum _ d hd
  refine ⟨node, hmem, hauth, k, n, ?_, ?_, hlt1, hlt2⟩
  · have hkey : d.key = k := by rw [hkr] at hk; exact Option.some_inj.mp hk
    simp [dirNodeKey, hd, hkey]
  · have hnext : d.next = n := by rw [hnr] at hn; exact Option.some_inj.mp hn
    simp [dirNodeNext, hd, hnext]

/-! ## Polarity controls (ADDENDUM E9) — STATED, NOT DISCHARGED

All three stanzas below are `Prop`s plus the exact `#blaster` invocation that
would discharge them, kept as comments with the measured outcome. They are NOT
run in the build: the two that were attempted consumed 87 minutes each without
returning, and a build that hangs is worse than an honest gap.

NOTE (E9, binding, unchanged): the negative control is ALSO satisfied by
budget-`Error`, so it can never by itself detect the 1600-step bound; the
non-vacuity evidence is `WSC/Props/P5_Witness1600.lean` (concrete golden, HALT
at 1600 / ERROR at 1553) plus K = 1554 from K-MEASUREMENTS.md §3. -/

/-- Negative control (STATED): a context in which the redeemer positionally
claims `NonMember` for `cs` but the node at the claimed index FAILS either the
directory authentication or the covering interval must be REJECTED by the
bytecode.

Discharge command (NOT run — see above):
`theorem … := by blaster` on this statement's body. -/
def P5_negative_control : Prop :=
  ∀ (protocolParamsCS dirCS cs : CurrencySymbol) (pIdx nodeIdx : Integer)
    (paramsIn node : TxInInfo) (ctx : ScriptContext),
    validRewardingContext ctx →
    transferParamsRefIdx ctx.scriptContextRedeemer = some pIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs pIdx.toNat = some paramsIn →
    paramsDatumDirCSRaw paramsIn.txInInfoResolved = some dirCS →
    nonMemberNodeIdxOf cs ctx = some nodeIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs nodeIdx.toNat = some node →
    ¬(dirNodeAuthH dirCS node.txInInfoResolved = true
      ∧ coversCS cs node.txInInfoResolved = true) →
    isUnsuccessful (appliedGlobal1600.prop protocolParamsCS ctx)

/-- Tightness stanza (STATED): the NEGATION of P5's postcondition under an
accepting run must be FALSIFIABLE (mirrors
Tests/Scripts/MintingPolicy/Properties.lean:47-53 and
WSC/Props/P3_Base.lean:93-100). Expected result if it ever returns: Falsified.

Discharge command (NOT run):
`#blaster (gen-cex: 0) (solve-result: 1) [P5_tightness]` -/
def P5_tightness : Prop :=
  ∀ (protocolParamsCS dirCS cs : CurrencySymbol) (pIdx nodeIdx : Integer)
    (paramsIn node : TxInInfo) (ctx : ScriptContext),
    validRewardingContext ctx →
    transferParamsRefIdx ctx.scriptContextRedeemer = some pIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs pIdx.toNat = some paramsIn →
    paramsDatumDirCSRaw paramsIn.txInInfoResolved = some dirCS →
    nonMemberNodeIdxOf cs ctx = some nodeIdx →
    nthFrom ctx.scriptContextTxInfo.txInfoReferenceInputs nodeIdx.toNat = some node →
    isSuccessful (appliedGlobal1600.prop protocolParamsCS ctx) →
    ¬(dirNodeAuthH dirCS node.txInInfoResolved = true
      ∧ coversCS cs node.txInInfoResolved = true)

/-- MANDATORY vacuity probe (SPIKE-FINDINGS / ADDENDUM E9) — ATTEMPTED, NO
VERDICT. "No accepting context exists within 1600 CEK steps" must be FALSIFIED
for any `accept → POST` theorem at this budget to be non-vacuous.

MEASURED (2026-07-25, this task): `#blaster (gen-cex: 1) (solve-result: 1)` on
this statement, as its own module under `lake build` with `maxHeartbeats 0`,
ran 5241 s ≈ 87 min at ~1.2 GB RSS and was killed WITHOUT returning — no
`Valid`, no `Falsified`, no counterexample. Compare
WSC/Prep/Global.lean's probe at budget 600, which returns `✅ Valid` (= vacuous)
in seconds: the 1600 prep is a much larger residual term and the solve does not
terminate in a usable time.

So the symbolic non-vacuity certificate for `appliedGlobal1600.prop` is OPEN.
The substitute evidence is concrete and independent: WSC/Props/P5_Witness1600.lean
runs the real bytecode with the real golden NonMember ctx and gets HALT at 1600
/ ERROR at 1553 (K = 1554, K-MEASUREMENTS.md §3).

Discharge command (NOT run):
`#blaster (gen-cex: 1) (solve-result: 1) [P5_vacuity_probe_1600]` -/
def P5_vacuity_probe_1600 : Prop :=
  ∀ (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx →
    ¬ isSuccessful (appliedGlobal1600.prop protocolParamsCS ctx)

end WSC
