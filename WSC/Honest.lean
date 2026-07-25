/-
WSC/Honest.lean — the honest-deployment vocabulary (arch §4.2) and the FULL
axiom base of the WSC containment campaign: TS1-TS5, LR1-LR7, plus the
ADDENDUM v3 additions LR-BUDGET (E1), LR-CTX (E5), NONNEG (E6) and the
three-conjunct DirWF (E4).

Every axiom is a SIGNATURE ONLY (no proof obligations discharged here); each
carries a plain-English doc comment and an audit note saying how it is meant
to be discharged or reviewed. There is no `sorry` anywhere in this library —
every stub is either an axiom or a complete definition.

RECONSTRUCTION FLAG (prominent, for the fidelity audit): the binding
`arch-final.md` was NOT available when this file was written (the scratchpad
holding it was wiped between sessions). The axiom NAMES and the addendum
allocations (E1/E4/E5/E6) follow the task brief and the persisted project
memory; the axiom STATEMENTS are faithful reconstructions over the §3/§4.2
vocabulary and MUST be re-audited against arch-final.md when it is recovered.
-/
import CardanoLedgerApi.V3
import WSC.Imports
import WSC.Redeemer
import WSC.Spec

namespace WSC

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo TxInInfo TxOut
                          hasCurrencySymbol valueOf validTxOutValue
                          credentialInWithdrawals isBalanced
                          validInputs validOutputs validScriptInfo
                          validScriptContext validRewardingContext
                          validMintingContext validSpendingContext)
open CardanoLedgerApi.V3.Contexts (validMintValue validWithdrawals validRedeemerMap)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## §4.2 honest-deployment vocabulary -/

/-- The output is an AUTHENTIC directory node: its value carries the
directory-node state-token policy `dirCS`.

AUDIT NOTE: the validators use the cheaper `phasCSH` shape check — "the FIRST
non-Ada policy of the value is `dirCS`" (ProgrammableLogicBase.hs:754-757;
`phasCSHOrFalse` :774-780). Under the ledger value-canonicity rules (sorted,
Ada first — LR2/NONNEG) and directory-NFT custody (TS5) the two coincide for
directory UTxOs; the ground-truth definition here is membership, and the
equivalence is discharged in the proof tasks, not assumed. -/
def authenticDirNode (dirCS : CurrencySymbol) (o : TxOut) : Bool :=
  hasCurrencySymbol dirCS o.txOutValue

/-- Decode an output's inline datum as a `DirectorySetNode`
(shape: PTokenDirectory.hs:144-174, mirrored in WSC/Redeemer.lean). -/
def dirNodeDatum (o : TxOut) : Option DirectorySetNode :=
  match o.txOutDatum with
  | .OutputDatum d => (IsData.fromData d : Option DirectorySetNode)
  | _ => none

/-- The `key` field of an output's directory-node datum, if it decodes. -/
def dirNodeKey (o : TxOut) : Option CurrencySymbol :=
  (dirNodeDatum o).map (·.key)

/-- The `next` field of an output's directory-node datum, if it decodes. -/
def dirNodeNext (o : TxOut) : Option CurrencySymbol :=
  (dirNodeDatum o).map (·.next)

/-- Policy `cs` is REGISTERED in the directory view visible to a transaction:
some reference input resolves to an authentic directory node whose datum key
is `cs`.

AUDIT NOTE (P5 caveat, binding): P5's postcondition must use the
covering-node witness (∃ authentic node, key < cs < next), NOT `¬ IsRegistered`
over the tx's view — this definition is the tx-visible registry projection,
sound for positive registration facts only. -/
def IsRegistered (dirCS : CurrencySymbol) (refIns : List TxInInfo) (cs : CurrencySymbol) : Bool :=
  match refIns with
  | [] => false
  | t :: rest =>
      (authenticDirNode dirCS t.txInInfoResolved &&
       dirNodeKey t.txInInfoResolved == some cs) ||
      IsRegistered dirCS rest cs

/-- The honest deployment parameters of one protocol instance: the
protocol-params NFT policy plus the four fields of its NFT-authenticated
datum (`ProgrammableLogicGlobalParams`, ProtocolParams.hs:62-68). -/
structure HonestParams where
  protocolParamsCS : CurrencySymbol
  directoryNodeCS : CurrencySymbol
  progLogicCred : Credential
  globalLogicCred : Credential
  seizeLogicCred : Credential

/-- The Data-level params datum this deployment publishes. -/
def HonestParams.datum (hp : HonestParams) : GlobalParams :=
  ⟨hp.directoryNodeCS, hp.progLogicCred, hp.globalLogicCred, hp.seizeLogicCred⟩

/-- Decode an output's inline datum as protocol params
(shape: ProtocolParams.hs:70-96, mirrored in WSC/Redeemer.lean). -/
def paramsDatum (o : TxOut) : Option GlobalParams :=
  match o.txOutDatum with
  | .OutputDatum d => (IsData.fromData d : Option GlobalParams)
  | _ => none

/-! ## Modelling predicates (declared, never defined — the trust boundary) -/

/-- `OnChain ctx`: the script context arises from a REAL Cardano mainnet
transaction that reached phase-2 validation (i.e. was produced by the ledger,
not synthesised). All LR-axioms condition on this. Declared abstract: it is
the bridge between the model and the chain, and is never discharged in Lean. -/
axiom OnChain : ScriptContext → Prop

/-- `Deployed hp`: `hp` are the parameters of the audited production
deployment (protocol-params NFT minted by the hardened anchor policy, §4.1;
directory/base/global/seize credentials as published). All TS-axioms condition
on this. Declared abstract for the same reason as `OnChain`. -/
axiom Deployed : HonestParams → Prop

/-! ## TS1-TS5 — trusted-subsystem axioms

These delegate to protocol components OUTSIDE the four imported validators
(the protocol-params anchor policy and the directory node minting/spending
scripts). Highest-value follow-on: discharge them by UPLC-level proofs over
those scripts (DirWF discharge = directory MP at UPLC). -/

/-- TS1 (params-anchor integrity). Any reference input of an on-chain
transaction whose value carries the deployed protocol-params state token
resolves to the honest params datum. Delegates to the hardened anchor policy
(§4.1): the NFT is unique and its datum is immutable and well-formed.

AUDIT NOTE: reconstructed statement; validators additionally authenticate the
params UTxO positionally via `pparamsAtRefIdx`/`phasCSH`
(ProgrammableLogicBase.hs:824-838) — a wrong index fails, so TS1 only needs to
pin the datum carried by the authenticated UTxO. -/
axiom TS1 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      hasCurrencySymbol hp.protocolParamsCS t.txInInfoResolved.txOutValue →
      paramsDatum t.txInInfoResolved = some hp.datum

/-- TS2 (params-NFT uniqueness). At most one reference input of an on-chain
transaction carries the deployed protocol-params state token. Delegates to the
anchor policy's one-shot mint. -/
axiom TS2 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t₁ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
    ∀ t₂ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      hasCurrencySymbol hp.protocolParamsCS t₁.txInInfoResolved.txOutValue →
      hasCurrencySymbol hp.protocolParamsCS t₂.txInInfoResolved.txOutValue →
      t₁ = t₂

/-- TS3 (directory-datum well-formedness). Every authentic directory node
visible to an on-chain transaction carries an inline datum that decodes as a
`DirectorySetNode`. Delegates to the directory node minting policy (nodes are
only created with well-formed datums) and the directory spending script
(shape is preserved). -/
axiom TS3 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      (dirNodeDatum t.txInInfoResolved).isSome

/-- TS4 (linked-list order). Every authentic directory node's datum satisfies
`key < next` (head sentinel key = "" and tail sentinel next = 0xff…ff included
— PTokenDirectory.hs:216-223). Delegates to the directory minting policy's
insert rule. This is what makes a covering-interval witness
(key < cs < next) meaningful. -/
axiom TS4 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      ∀ d, dirNodeDatum t.txInInfoResolved = some d → d.key < d.next

/-- TS5 (directory-NFT custody). Directory state tokens never sit at outputs
other than the directory spending script's; in particular an authentic
directory node's FIRST non-Ada policy is the directory policy, so the
validators' cheap `phasCSH` authentication (ProgrammableLogicBase.hs:754-757)
agrees with ground-truth membership (`authenticDirNode`). Delegates to the
directory minting policy + directory spending script custody rules. -/
axiom TS5 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      match t.txInInfoResolved.txOutValue with
      | _ :: (Data.B cs, _) :: _ => cs = hp.directoryNodeCS
      | _ => False

/-! ## DirWF (ADDENDUM E4) — three-conjunct directory well-formedness -/

/-- DirWF (E4): the directory linked list is well-formed in the view of one
transaction. THREE conjuncts (binding, per adversarial review):

1. INSERT-ONLY: every authentic directory node consumed by the transaction
   reappears as an authentic output node with the same key (keys are never
   deleted or rewritten);
2. KEY-UNIQUENESS: no two distinct authentic reference-input nodes carry the
   same key;
3. NFT-NAME=KEY BINDING: an authentic node holds EXACTLY ONE directory state
   token, whose token name equals the datum's `key` bytes (this is what makes
   the issuance policy's datum-free `hasNodeNFT` check — Issuance.hs:154-157 —
   sound). -/
def DirWF (hp : HonestParams) (ctx : ScriptContext) : Prop :=
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
     authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
     ∃ o ∈ ctx.scriptContextTxInfo.txInfoOutputs,
       authenticDirNode hp.directoryNodeCS o ∧
       dirNodeKey o = dirNodeKey t.txInInfoResolved) ∧
  (∀ t₁ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
   ∀ t₂ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
     authenticDirNode hp.directoryNodeCS t₁.txInInfoResolved →
     authenticDirNode hp.directoryNodeCS t₂.txInInfoResolved →
     dirNodeKey t₁.txInInfoResolved = dirNodeKey t₂.txInInfoResolved →
     t₁ = t₂) ∧
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
     authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
     ∀ d, dirNodeDatum t.txInInfoResolved = some d →
       valueOf hp.directoryNodeCS d.key t.txInInfoResolved.txOutValue = 1)

/-- DirWF holds for every on-chain transaction of the audited deployment.
Delegates to the directory node minting policy + directory spending script;
highest-value follow-on is discharging this at UPLC level (directory MP). -/
axiom DIRWF :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx → DirWF hp ctx

/-! ## LR1-LR7 — ledger-rule axioms

Facts guaranteed by Cardano ledger rules (phase-1 validation and context
construction) about every REAL script invocation. CLAB encodes them as the
`valid*` Boolean predicates ([LEDGER-RULE] docs in
CardanoLedgerApi/V3/Contexts.lean); the axioms assert that on-chain contexts
satisfy them. They are consequences of LR-CTX; they are kept as named axioms
so each proof cites exactly the rule it needs (audit note: redundancy with
LR-CTX is intentional and harmless — same trust base). -/

/-- LR1: transaction inputs are non-empty, sorted by `TxOutRef`, and every
resolved input value is canonical (`validInputs`,
CardanoLedgerApi/V3/Contexts.lean:1005-1030). -/
axiom LR1 : ∀ (ctx : ScriptContext), OnChain ctx → validInputs ctx

/-- LR2: every transaction output value is canonical — Ada entry first,
policies sorted, token names sorted, quantities strictly positive
(`validOutputs` over `validTxOutValue`,
CardanoLedgerApi/V3/Contexts.lean:1064-1073). -/
axiom LR2 : ∀ (ctx : ScriptContext), OnChain ctx →
  validOutputs ctx.scriptContextTxInfo.txInfoOutputs

/-- LR3: the mint value is canonical — NO Ada entry, policies sorted, token
names sorted, quantities non-zero (`validMintValue` [V3],
CardanoLedgerApi/V3/Contexts.lean:784-813). The positional mint-proof
classification (WSC/Spec.lean `mintProofFor`) is meaningful because of this
sortedness. -/
axiom LR3 : ∀ (ctx : ScriptContext), OnChain ctx →
  validMintValue ctx.scriptContextTxInfo.txInfoMint

/-- LR4: the withdrawal map is sorted by credential (hence duplicate-free)
(`validWithdrawals`, CardanoLedgerApi/V3/Contexts.lean:915-930). The
withdrawal-index witnesses of the redeemers resolve unambiguously because of
this. -/
axiom LR4 : ∀ (ctx : ScriptContext), OnChain ctx →
  validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl

/-- LR5: the redeemer map is sorted by script purpose, and the running
script's own (purpose, redeemer) pair is present in it (`validRedeemerMap` +
the redeemer conjunct of `validScriptInfo`,
CardanoLedgerApi/V3/Contexts.lean:1075-1090 and :946-1002). The issuance
`DelegateSeize` arm's redeemer-map indexing (Issuance.hs:231-240) relies on
this. -/
axiom LR5 : ∀ (ctx : ScriptContext), OnChain ctx →
  validRedeemerMap ctx.scriptContextTxInfo.txInfoRedeemers ∧ validScriptInfo ctx

/-- LR6: a rewarding invocation's own credential is a script credential and
appears in the withdrawal map (rewarding conjunct of `validScriptInfo`,
CardanoLedgerApi/V3/Contexts.lean:988-990). The withdraw-zero forwarding
pattern (base → global/seize) is sound because of this. -/
axiom LR6 : ∀ (ctx : ScriptContext) (cred : Credential), OnChain ctx →
  ctx.scriptContextScriptInfo = ScriptInfo.RewardingScript cred →
  credentialInWithdrawals cred ctx.scriptContextTxInfo.txInfoWdrl

/-- LR7: the transaction is balanced — value in inputs + mint = value in
outputs + fee (`isBalanced`, CardanoLedgerApi/V3/Contexts.lean:1147-1154).
Containment arguments convert "does not remain at base outputs" into "escapes
to a non-base output" through this. -/
axiom LR7 : ∀ (ctx : ScriptContext), OnChain ctx → isBalanced ctx

/-! ## ADDENDUM axioms -/

/-- LR-CTX (ADDENDUM E5): the master context bridge. Every REAL invocation of
one of our validators receives a context satisfying CLAB's full
`validScriptContext` (and hence, per its purpose, `validRewardingContext` /
`validMintingContext` / `validSpendingContext`). This is the axiom that lets
theorems proved under `validXContext` hypotheses apply to real invocations. -/
axiom LR_CTX : ∀ (ctx : ScriptContext), OnChain ctx → validScriptContext ctx

/-- NONNEG (ADDENDUM E6): strict positivity of carried value. Every resolved
input and every output of an on-chain transaction has a canonical value with
STRICTLY POSITIVE quantities (`validTxOutValue`). This is the ground-truth
counterpart of the containment precondition "every quantity in
`expectedValue` is strictly positive" (ProgrammableLogicBase.hs:547-551) and
is what makes lower-bound containment monotone.

AUDIT NOTE: overlaps LR1/LR2 (both quantify `validTxOutValue`); kept separate
because the containment lemmas cite positivity alone. -/
axiom NONNEG : ∀ (ctx : ScriptContext), OnChain ctx →
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
     validTxOutValue t.txInInfoResolved.txOutValue) ∧
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs,
     validTxOutValue o.txOutValue)

/-! ### LR-BUDGET (ADDENDUM E1) — boundedness caveat, binding

`#prep_uplc` bakes a concrete CEK step budget into each `applied*.prop`
(base 600, minting 2000, seize 9000 — WSC/Imports.lean). Budget exhaustion
evaluates to `Error`, making `isSuccessful` FALSE and success-implies-P
theorems VACUOUS past the bound. ALL results of this campaign are therefore
BOUNDED-TRANSACTION model checking of the real bytecode; they must never be
claimed unbounded. The axioms below assert, per validator, that there is a
published transaction-size bound K within which the budgeted evaluation
agrees with the real (unbounded-budget) node verdict. K is established
empirically (per-validator spike) and published alongside the theorems. -/

/-- Coarse transaction-size measure used by the LR-BUDGET bounds: total count
of inputs, reference inputs, outputs, mint entries, withdrawal entries,
redeemer entries and signatories. -/
def txSize (ctx : ScriptContext) : Nat :=
  ctx.scriptContextTxInfo.txInfoInputs.length +
  ctx.scriptContextTxInfo.txInfoReferenceInputs.length +
  ctx.scriptContextTxInfo.txInfoOutputs.length +
  ctx.scriptContextTxInfo.txInfoMint.length +
  ctx.scriptContextTxInfo.txInfoWdrl.length +
  ctx.scriptContextTxInfo.txInfoRedeemers.length +
  ctx.scriptContextTxInfo.txInfoSignatories.length

/-- The real node (mainnet cost-model budget, no baked step cap) accepts this
invocation of the base validator with these parameters. Abstract — the
chain-side truth the budgeted model is bridged to. -/
axiom NodeAcceptsBase : Credential → Credential → ScriptContext → Prop

/-- The real node accepts this invocation of the issuance minting policy. -/
axiom NodeAcceptsMinting : CurrencySymbol → ByteString → ScriptContext → Prop

/-- The real node accepts this invocation of the seize validator. -/
axiom NodeAcceptsSeize : CurrencySymbol → ScriptContext → Prop

/-- LR-BUDGET for `appliedBase` (budget 600): within a published size bound K,
budgeted success coincides with node acceptance — so no theorem is vacuous by
budget exhaustion for transactions of size ≤ K. -/
axiom LR_BUDGET_base :
  ∃ K : Nat, 0 < K ∧
    ∀ (g s : Credential) (ctx : ScriptContext),
      OnChain ctx → txSize ctx ≤ K →
      (NodeAcceptsBase g s ctx ↔ isSuccessful (appliedBase.prop g s ctx))

/-- LR-BUDGET for `appliedMinting` (budget 2000): same statement shape. -/
axiom LR_BUDGET_minting :
  ∃ K : Nat, 0 < K ∧
    ∀ (pcs : CurrencySymbol) (mlh : ByteString) (ctx : ScriptContext),
      OnChain ctx → txSize ctx ≤ K →
      (NodeAcceptsMinting pcs mlh ctx ↔ isSuccessful (appliedMinting.prop pcs mlh ctx))

/-- LR-BUDGET for `appliedSeize` (budget 9000): same statement shape. -/
axiom LR_BUDGET_seize :
  ∃ K : Nat, 0 < K ∧
    ∀ (pcs : CurrencySymbol) (ctx : ScriptContext),
      OnChain ctx → txSize ctx ≤ K →
      (NodeAcceptsSeize pcs ctx ↔ isSuccessful (appliedSeize.prop pcs ctx))

end WSC
