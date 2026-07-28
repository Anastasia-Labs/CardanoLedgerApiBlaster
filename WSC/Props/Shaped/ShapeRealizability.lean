-- ⚠️ PRE-#112 (PARTIAL): part of this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Read WSC/IMPACT-PR112.md for the split before quoting anything here.
/-
WSC/Props/Shaped/ShapeRealizability.lean — **why audit finding F1 cannot be closed
with the shapes this library has** (task A2).

════════════════════════════════════════════════════════════════════════════
THE FINDING, IN ONE PARAGRAPH
════════════════════════════════════════════════════════════════════════════
`WSC/Composition.lean`'s `top_claim` consumes `leaves : LeafSet hp Shape`, and
`Shape` is exactly the hook a shaped leaf needs: instantiate `Shape` with "`ctx` is
an instance of SHAPE T1", discharge `LeafSet.p1` from `WSC.P1_T1`, and F1 is closed.
**That plan produces a theorem about an EMPTY class.**

Every shaped context in this library bakes a **one-entry redeemer map** — two for
SHAPE DS1 — because the redeemer map is part of the `Data` skeleton `#prep_uplc`
freezes, and a symbolic map is exactly what makes the prep intractable. Every shaped
context ALSO bakes a **two-entry withdrawal map whose entries are both SCRIPT
credentials** (`p1ShapedWdrl`, `localShapedWdrl`, `mintShapedWdrl`,
`globalShapedWdrl`, `seizeShapedWdrl` — all five are
`[(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]`). The Conway UTXOW rule
`MissingRedeemers` requires one redeemer-map entry per script witness, and a
script-credential withdrawal IS a script witness (that is the very rule
`WSC.LR_WDRL_RUNS_VALIDATOR` encodes). So no shaped context is the context of any
transaction a node would accept.

For SHAPE T1 this is provable **from the axioms already in this library, with no new
assumption at all** (§1). For the other shapes it needs the `MissingRedeemers` rule,
which `WSC/Honest.lean` does not state; §2 states it as a `Prop` — `RedeemerCoverageAllPlutus`,
NOT an axiom — and proves the emptiness conditionally on it, shape by shape.

════════════════════════════════════════════════════════════════════════════
PROVENANCE — THE OBSERVATION IS NOT NEW, THE PROOF AND ITS CONSEQUENCE ARE
════════════════════════════════════════════════════════════════════════════
`WSC/SHAPING-RESULTS.md` §7 already recorded, as honest limit 3, that *"SHAPE M1/M2
have a ONE-entry redeemer map … but that is precisely the mixed spending+minting map
that every real programmable-token mint carries"*, and its "what to do next" item 5
asked for CLAB to be fixed so shaped theorems could use realistic multi-entry maps.
Both were right. What was NOT said, and is what this module establishes, is the
consequence: a one-entry map does not merely make a shape unrepresentative — with the
axioms of `WSC/Honest.lean` it makes the shape class **empty**, so a composition
result quantified over a shaped class is VACUOUS rather than narrow. (CLAB's ordering
defects D1/D2 were fixed by task Z1, so a multi-entry shaped map is now sortable; the
blocker is prep-and-reprove work, not the substrate.)

════════════════════════════════════════════════════════════════════════════
WHAT THIS MODULE IS AND IS NOT
════════════════════════════════════════════════════════════════════════════
It is NOT a refutation of any P-theorem. `WSC.P1_T1`, `WSC.P4_disjunction_at_L1`,
`WSC.P2a_shaped_structure`, `WSC.P5_shaped` and the rest are exactly as true as
before: each says *"IF the real compiled bytecode accepts this `Data` skeleton with
these symbolic scalars THEN <postcondition>"*, and the bytecode really does. What
this module shows is that the antecedent's `ScriptContext` cannot be a LEDGER
context, which matters for one thing only — **composition**. A shaped theorem
remains evidence about the validator's logic; it cannot be plugged into a
ledger-level claim through a `Shape` restriction without emptying the claim.

WHY YOU CANNOT ESCAPE BY PINNING LESS. The obvious dodge is to define `Shape` so that
it constrains only the fields the leaf's conclusion mentions (inputs, outputs, mint)
and leaves `txInfoRedeemers` free, making the class non-empty again. That does not
work, and the reason is structural rather than accidental: a shaped P-theorem's
hypothesis is `isSuccessful (appliedXShaped.prop <scalars>)`, whose subject is the
prep of ONE `Data` skeleton — the whole context, redeemer map included. To apply it to
a transaction you must exhibit that transaction's context AS the shaped context, i.e.
pin every field the skeleton pins. `Shape` can be weaker only by making the leaf
inapplicable. The redeemer map is part of `TxInfo`, so it is shared by every purpose
view of the transaction (`WSC.withPurpose` copies `scriptContextTxInfo` verbatim) —
there is no purpose at which it becomes free.

WHY NOTHING CAUGHT THIS EARLIER, and it is a CLAB-fidelity finding in its own right:
`validRewardingContext` / `validMintingContext` check the redeemer map only for the
script that is CURRENTLY RUNNING (`validScriptInfo`'s first conjunct,
`CardanoLedgerApi/V3/Contexts.lean:1035-1037` = audit row B of `WSC/Honest.lean`'s
LR-CTX table). Neither predicate has a clause for "every script this transaction
needs has an entry", so every shaped witness is `validXContext = true` while being
unrealizable. §5 states that as a theorem against a witness the library already has,
and the LR-CTX audit table has no row for the `MissingRedeemers` rule — that missing
row is exactly `RedeemerCoverageAllPlutus` below.

WHAT WOULD FIX IT, sized: re-shape with a ledger-realistic redeemer map. Adding the
missing entries changes the `Data` skeleton, so each affected shape needs a new
`#prep_uplc` (measured cost of a shaped prep: ≈1 s, and budget-independent —
`WSC/SHAPING-RESULTS.md` §2.5) and each theorem over it must be re-verified by
`blaster` (the risk: the extra map entries enlarge the residual). The cheapest
variant is a shape whose withdrawal entries are PUBKEY credentials wherever the
validator does not need a script there — SHAPE T1 needs `w0` to be the global
validator's own script credential, and `w1` only to be *some* entry the redeemer's
`transferWdrlIdxs = [1]` can name, so `w1` pubkey plus a `Spending` redeemer entry
for the base input may be enough. That experiment is NOT run here.

════════════════════════════════════════════════════════════════════════════
LAYOUT
════════════════════════════════════════════════════════════════════════════
* §1 SHAPE T1 — emptiness, UNCONDITIONAL (`WSC.LR_SPEND_RUNS_VALIDATOR` + `LR_CTX`)
* §2 `RedeemerCoverageAllPlutus` and the conditional emptiness of L1 / M1 / G1 / S1 / DT1 / DS1
* §2.2 the TRUE Conway rule (`RedeemerCoverageTrue`) and `RedeemerCoverageAt` —
  audit finding **F18**: the all-Plutus reading is strictly stronger than the
  ledger, so every §2 result now carries its non-native side condition in its type
* §2.3 the F18 audit table: every NEGATIVE use of the rule in the library, one by
  one, with its verdict under the TRUE rule
* §3 the VACUOUS `LeafSet` at SHAPE T1, built and labelled as such
* §5 the CLAB-fidelity corollary: the witnesses pass `validRewardingContext` anyway
* §4 axiom census
-/
import WSC.Composition
import WSC.Props.Shaped.P1Shaped
import WSC.Shaped.GlobalShapedP1
import WSC.Shaped.MintingLocalShaped
import WSC.Shaped.MintingDelegateShaped
import WSC.Shaped.MintingShaped
import WSC.Shaped.GlobalShaped
import WSC.Shaped.SeizeShaped

namespace WSC.ShapeRealizability

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptInfo ScriptPurpose
                          ScriptHash TxInInfo TxOutRef findRedeemer validScriptContext
                          validScriptInfo)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! # §0 Two generic lemmas about CLAB's own `validScriptInfo` -/

/-- **If the transaction's redeemer map has no entry for the running script's
purpose, the ledger's own `validScriptInfo` is FALSE.** This is CLAB's transcription
(`CardanoLedgerApi/V3/Contexts.lean:1035-1037`) of the Conway rule that the redeemer
handed to a script is its `Redeemers` entry (`Babbage/TxInfo.hs:217-221`) — audit row
B of `WSC/Honest.lean`'s LR-CTX table. -/
theorem validScriptInfo_false_of_no_redeemer (ctx : ScriptContext)
    (h : findRedeemer ctx.scriptContextScriptInfo.toScriptPurpose
           ctx.scriptContextTxInfo.txInfoRedeemers = none) :
    validScriptInfo ctx = false := by
  unfold validScriptInfo
  simp [h]

/-- Consequence: such a context cannot be `WSC.OnChain`, because `WSC.LR_CTX` asserts
`validScriptContext` of every on-chain context. -/
theorem not_onChain_of_no_redeemer (ctx : ScriptContext)
    (h : findRedeemer ctx.scriptContextScriptInfo.toScriptPurpose
           ctx.scriptContextTxInfo.txInfoRedeemers = none) :
    ¬ WSC.OnChain ctx := by
  intro hoc
  have h2 := WSC.LR_CTX ctx hoc
  rw [validScriptContext, validScriptInfo_false_of_no_redeemer ctx h] at h2
  simp at h2

/-! # §1 SHAPE T1 — the class is EMPTY, and no new assumption is needed

SHAPE T1's input 0 sits at `ScriptCredential plc`, and a `LeafSet` discharged from
`WSC.P1_T1` must identify that with `hp.progLogicCred` (otherwise the shaped
theorem's `Model.outSum (.ScriptCredential plc) …` is not the composition's
`outAtB hp.progLogicCred …` and the leaf says nothing about the mini-ledger). So the
transaction SPENDS a mini-ledger UTxO, `WSC.LR_SPEND_RUNS_VALIDATOR` runs the base
validator on it, and `WSC.LR_CTX` then demands a `Spending` entry in SHAPE T1's
redeemer map — which holds exactly one `Rewarding` entry. -/

/-- SHAPE T1's redeemer map has NO `Spending` entry, for any `TxOutRef`. Kernel
computation (`rfl`): the two `ScriptPurpose` constructors differ, so
`beqScriptPurpose` returns `false` without inspecting the symbolic hashes. -/
theorem t1_no_spending_redeemer (o : TxOutRef) (w0 : ByteString) :
    findRedeemer (.Spending o)
      [(ScriptPurpose.Rewarding (.ScriptCredential w0), p1ShapedRedeemer)] = none := rfl

/-- **THE T1 SHAPE CLASS IS EMPTY — machine-checked, no new assumption.**

*No on-chain transaction of an honest deployment has SHAPE T1's `TxInfo`, once the
shape's base credential `plc` is the deployment's `progLogicCred`.*

The scalars are universally quantified exactly as in `WSC.P1_T1`, so this is a
statement about the whole shape class, not about one instance.

TRUST COST: `WSC.Deployed`, `WSC.OnChain`, `WSC.LR_SPEND_RUNS_VALIDATOR`,
`WSC.LR_CTX` — nothing else, and NO `sorryAx` (see §4). -/
theorem t1_class_is_empty
    (hp : WSC.HonestParams) (ctx : ScriptContext)
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hdep : WSC.Deployed hp) (hoc : WSC.OnChain ctx)
    (hbase : hp.progLogicCred = Credential.ScriptCredential plc)
    (hsh : ctx.scriptContextTxInfo =
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  -- the mini-ledger input SHAPE T1 spends
  have ht : p1ShapedBaseIn plc owner inAda cs tn qIn ∈ ctx.scriptContextTxInfo.txInfoInputs := by
    rw [hsh]; exact List.mem_cons_self ..
  have hpc : WSC.payCred (p1ShapedBaseIn plc owner inAda cs tn qIn).txInInfoResolved
      = hp.progLogicCred := by rw [hbase]; rfl
  obtain ⟨r, d, hoc', -⟩ :=
    WSC.LR_SPEND_RUNS_VALIDATOR hp ctx _ hdep hoc ht hpc
  refine not_onChain_of_no_redeemer _ ?_ hoc'
  show findRedeemer (.Spending _) ctx.scriptContextTxInfo.txInfoRedeemers = none
  rw [hsh]
  exact t1_no_spending_redeemer _ w0

/-! # §2 The other shapes: empty under the `MissingRedeemers` rule

`WSC/Honest.lean` has no axiom saying "every script the transaction needs has a
redeemer-map entry". It is a real Conway rule, and the library already needed a
piece of it once: `WSC/Composition.lean` §10.3's `SeizeWdrlOfScoped` is the
CONVERSE direction ("a redeemer-map entry for a rewarding purpose implies the reward
account is withdrawn from") and its docstring records that `WSC.LR5` does not supply
it either.

It is stated here as a `Prop`, deliberately NOT as an axiom: nothing in this library
is allowed to become stronger because of a negative result. -/

/-- **THE MISSING LEDGER RULE (a `Prop`, not an axiom).** *A script-credential
withdrawal requires a `Rewarding` redeemer-map entry for that credential.*

LEDGER RULE: Conway UTXOW — `scriptsNeeded` includes the script of every
script-credential withdrawal, and `MissingRedeemers` rejects a transaction that does
not carry a redeemer for a needed script (`Alonzo/Rules/Utxow.hs`); the Plutus
`txInfoRedeemers` map IS that redeemer set (`Babbage/TxInfo.hs:217-221`, audit row B).
It is the same rule `WSC.LR_WDRL_RUNS_VALIDATOR` relies on to conclude that the
global/seize validator RAN — stated here about the redeemer MAP instead of about
acceptance.

**IT IS STRONGER THAN THE LEDGER RULE — audit finding F18, and the reason for
the `AllPlutus` suffix.** Conway keeps only the needed `(purpose, hash)` pairs
whose provided script satisfies `not (isNativeScript script)`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:247-251`,
`cardano-ledger` @ `cd8b7fab8`). A withdrawal at a NATIVE-script credential
needs no redeemer entry, and by the `ExtraRedeemers` half must not have one. So
a genuine on-chain transaction can falsify this `Prop`. Because every use below
is NEGATIVE — the `Prop` is ASSUMED and a contradiction derived — the error runs
against us, and §2.2 records what each shape's emptiness really rests on. -/
def RedeemerCoverageAllPlutus : Prop :=
  ∀ (ctx : ScriptContext) (h : ScriptHash) (n : Integer),
    WSC.OnChain ctx →
    (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl →
      findRedeemer (.Rewarding (.ScriptCredential h))
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-! ### §2.2 THE TRUE RULE, and what each retired shape really needs (F18)

Every emptiness proof in §2 turns on ONE withdrawal credential — the shape's
`w0` or `w1` — and nothing else. So the hypothesis they need is not the full
`RedeemerCoverageAllPlutus` but `RedeemerCoverageAt w`, coverage at that single
credential; that is what they are stated with below, which makes each of them
strictly more general than before AND makes the F18 question local and visible.

`RedeemerCoverageAt w` has exactly two suppliers:

* `RedeemerCoverageAt_of_allPlutus` — from the ALL-PLUTUS reading, i.e. from
  `RedeemerCoverageAllPlutus` or from the axiom `WSC.LR_REDEEMER_COVERAGE`.
  **Over-strong (F18).**
* `RedeemerCoverageAt_of_true` — from the TRUE rule
  (`RedeemerCoverageTrue isNative`) PLUS the side condition `¬ isNative w`, i.e.
  "the script witnessing this withdrawal is not a native timelock". **Faithful,
  and the side condition is the honest cost.**

`isNative` is left an arbitrary predicate on hashes: nothing here assumes
anything about it, and `TxInfo` cannot decide it (`CardanoLedgerApi/V3/
Contexts.lean`, expressibility verdict — `TxInfo` carries script HASHES but no
script bodies and no language tags). No shape below pins its witness credential
to a deployed WSC validator hash: in `localShapedCtx` / `dtShapedCtx` /
`mintShapedCtx` / `globalShapedCtx` / `p1ShapedCtx` / `seizeShapedCtx` /
`memberShapedCtx` the credentials `w0`, `w1` are FREE `ByteString` parameters.
So none of them can be re-established outright, and every one carries a
non-native side condition. The full per-use table is in §2.3. -/

/-- Coverage AT ONE CREDENTIAL. The only instance any §2 emptiness proof uses. -/
def RedeemerCoverageAt (w : ScriptHash) : Prop :=
  ∀ (ctx : ScriptContext) (n : Integer),
    WSC.OnChain ctx →
    (Credential.ScriptCredential w, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl →
      findRedeemer (.Rewarding (.ScriptCredential w))
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-- **THE TRUE CONWAY RULE**, relative to a language oracle on script hashes:
only a NON-NATIVE needed script requires a redeemer entry. -/
def RedeemerCoverageTrue (isNative : ScriptHash → Prop) : Prop :=
  ∀ (ctx : ScriptContext) (h : ScriptHash) (n : Integer),
    WSC.OnChain ctx →
    (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl →
    ¬ isNative h →
      findRedeemer (.Rewarding (.ScriptCredential h))
        ctx.scriptContextTxInfo.txInfoRedeemers ≠ none

/-- Supplier 1 — the ALL-PLUTUS reading. **Over-strong (F18).** -/
theorem RedeemerCoverageAt_of_allPlutus (rc : RedeemerCoverageAllPlutus)
    (w : ScriptHash) : RedeemerCoverageAt w :=
  fun ctx n hoc hw => rc ctx w n hoc hw

/-- Supplier 2 — the TRUE rule plus the explicit non-native side condition. -/
theorem RedeemerCoverageAt_of_true {isNative : ScriptHash → Prop}
    (rc : RedeemerCoverageTrue isNative) {w : ScriptHash} (hnn : ¬ isNative w) :
    RedeemerCoverageAt w :=
  fun ctx n hoc hw => rc ctx w n hoc hw hnn

/-- The all-Plutus `Prop` IS the `isNative = fun _ => False` instance of the true
rule — the precise sense in which it reads the rule at an all-Plutus
transaction. -/
theorem redeemerCoverageAllPlutus_iff_true_allPlutus :
    RedeemerCoverageAllPlutus ↔ RedeemerCoverageTrue (fun _ => False) :=
  ⟨fun rc ctx h n hoc hw _ => rc ctx h n hoc hw,
   fun rc ctx h n hoc hw => rc ctx h n hoc hw (fun h => h.elim)⟩

/-- The shape-independent shell: a transaction whose withdrawal map contains a
script credential with no `Rewarding` redeemer entry cannot exist.

Stated at `RedeemerCoverageAt w`, so the caller decides — visibly — whether it
is paying with the over-strong all-Plutus reading or with the true rule plus a
non-native side condition. -/
theorem empty_of_uncovered_wdrl_at {w : ScriptHash} (rcw : RedeemerCoverageAt w)
    (ctx : ScriptContext) (n : Integer) (hoc : WSC.OnChain ctx)
    (hw : (Credential.ScriptCredential w, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl)
    (hr : findRedeemer (.Rewarding (.ScriptCredential w))
      ctx.scriptContextTxInfo.txInfoRedeemers = none) : False :=
  rcw ctx n hoc hw hr

/-- The original shell, kept because `WSC/Props/Shaped/GlobalRealizability.lean`
`open`s it. `RedeemerCoverageAllPlutus` is over-strong (F18); prefer
`empty_of_uncovered_wdrl_at`. -/
theorem empty_of_uncovered_wdrl (rc : RedeemerCoverageAllPlutus) (ctx : ScriptContext)
    (h : ScriptHash) (n : Integer) (hoc : WSC.OnChain ctx)
    (hw : (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl)
    (hr : findRedeemer (.Rewarding (.ScriptCredential h))
      ctx.scriptContextTxInfo.txInfoRedeemers = none) : False :=
  rc ctx h n hoc hw hr

/-- A `Minting`-keyed singleton redeemer map covers no `Rewarding` purpose. `rfl`. -/
theorem minting_map_covers_no_rewarding (ownCS : CurrencySymbol) (c : Credential) (r : Data) :
    findRedeemer (.Rewarding c) [(ScriptPurpose.Minting ownCS, r)] = none := rfl

/-- **SHAPE L1 (P4's `Local` arm, budget 2500) — EMPTY under `RedeemerCoverageAllPlutus`.**
Its withdrawal entry 0 is `ScriptCredential w0` and its redeemer map is the single
`Minting ownCS` entry. (Its OWN theorem `WSC.P4a_local_shaped` proves that an
accepted L1 mint has `ScriptCredential mlh` in that withdrawal map — so the
uncovered script withdrawal is not an artefact of the shape, it is what the arm
requires.) -/
theorem l1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (rc : RedeemerCoverageAt w0)
    (hsh : ctx.scriptContextTxInfo =
      (localShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a0 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_self ..
  · rw [hsh]; exact minting_map_covers_no_rewarding _ _ _

/-- **SHAPE DT1 (P4's `DelegateTransfer` arm, budget 2500) — EMPTY under
`RedeemerCoverageAllPlutus`.** Same skeleton and the same singleton `Minting` map. -/
theorem dt1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (o0h : ByteString) (outAda0 : Integer) (c0 tn0 : ByteString) (qq0 : Integer)
    (o1h : ByteString) (outAda1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (rc : RedeemerCoverageAt w0)
    (hsh : ctx.scriptContextTxInfo =
      (dtShapedCtx ownCS tn q owner inAda qIn o0h outAda0 c0 tn0 qq0 o1h outAda1
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a0 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_self ..
  · rw [hsh]; exact minting_map_covers_no_rewarding _ _ _

/-- **SHAPE M1 (P4's `BurnOnly` arm, budget 900) — EMPTY under `RedeemerCoverageAllPlutus`.**
The one shape whose leaf the composition can reach at the PUBLISHED `K_mint = 900`,
and its class is empty too. -/
theorem m1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (ownCS tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda qIn : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) (txid : ByteString) (oidx : Integer)
    (lo hi : Integer) (tid : ByteString)
    (rc : RedeemerCoverageAt w0)
    (hsh : ctx.scriptContextTxInfo =
      (mintShapedCtx ownCS tn q owner inAda qIn dest outAda qOut
        w0 w1 a0 a1 fee txid oidx lo hi tid).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a0 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_self ..
  · rw [hsh]; exact minting_map_covers_no_rewarding _ _ _

/-- A `Rewarding w0`-keyed singleton redeemer map covers `Rewarding w1` only if
`w1 = w0`. The side condition `w0 ≠ w1` below is forced on any real transaction by
`validWithdrawals`' strict ordering (`WSC.LR4`), so it costs nothing. -/
theorem rewarding_purpose_beq_false (w0 w1 : ByteString) (hne : w1 ≠ w0) :
    (ScriptPurpose.Rewarding (Credential.ScriptCredential w0) ==
      ScriptPurpose.Rewarding (Credential.ScriptCredential w1)) = false := by
  refine beq_eq_false_iff_ne.mpr ?_
  intro h
  injection h with h
  injection h with h
  exact hne h.symm

theorem rewarding_singleton_covers_only_itself (w0 w1 : ByteString) (r : Data)
    (hne : w1 ≠ w0) :
    findRedeemer (.Rewarding (.ScriptCredential w1))
      [(ScriptPurpose.Rewarding (.ScriptCredential w0), r)] = none := by
  show (if (ScriptPurpose.Rewarding (Credential.ScriptCredential w0) ==
             ScriptPurpose.Rewarding (Credential.ScriptCredential w1)) = true
        then some r else none) = none
  rw [rewarding_purpose_beq_false w0 w1 hne]
  simp

/-- **SHAPE G1 (P5, budget 1600) — EMPTY under `RedeemerCoverageAllPlutus`.** Withdrawal
entry 1 (`ScriptCredential w1`) has no redeemer entry: the map holds only the
validator's OWN `Rewarding w0`. -/
theorem g1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hne : w1 ≠ w0)
    (rc : RedeemerCoverageAt w1)
    (hsh : ctx.scriptContextTxInfo =
      (globalShapedCtx cs tn q owner inAda dest outAda qOut
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a1 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hsh]; exact rewarding_singleton_covers_only_itself w0 w1 _ hne

/-- **SHAPE T1 again — EMPTY under `RedeemerCoverageAllPlutus` TOO**, by the withdrawal route
rather than the spending route, i.e. even a re-shaping that removed the base input
would not rescue it. -/
theorem t1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (cs tn plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer) (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hne : w1 ≠ w0)
    (rc : RedeemerCoverageAt w1)
    (hsh : ctx.scriptContextTxInfo =
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
        pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
        key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a1 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hsh]; exact rewarding_singleton_covers_only_itself w0 w1 _ hne

/-- **SHAPE S1 (P2, budget 3800) — EMPTY under `RedeemerCoverageAllPlutus`.** Same withdrawal
route as G1/T1. -/
theorem s1_class_is_empty_under_coverage
    (ctx : ScriptContext) (hoc : WSC.OnChain ctx)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 fee : Integer)
    (hne : w1 ≠ w0)
    (rc : RedeemerCoverageAt w1)
    (hsh : ctx.scriptContextTxInfo =
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo) :
    False := by
  refine empty_of_uncovered_wdrl_at rc ctx a1 hoc ?_ ?_
  · rw [hsh]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hsh]; exact rewarding_singleton_covers_only_itself w0 w1 _ hne

/-! ### §2.1 SHAPE DS1 — the only two-entry redeemer map, and it is still short

SHAPE DS1's map is `[(.Minting ownCS, …), (.Rewarding (.ScriptCredential sCred), …)]`
(`WSC/Shaped/MintingDelegateShaped.lean:190-193`), i.e. it covers ONE of the two
script withdrawals. Since `validWithdrawals` forces `w0 ≠ w1`, at least one of them
is not `sCred`, so the class is empty under `RedeemerCoverageAllPlutus` for every `sCred`.
Recorded here in the form the proof takes: the two cases, each with its own witness
credential.

**F18 DOWNGRADE.** Which of `w0`, `w1` is the uncovered one depends on `sCred`,
so the true-rule version of this argument needs `¬ isNative w0 ∧ ¬ isNative w1` —
DS1 is the one retired shape whose side condition is on BOTH credentials. -/
/-- A `[Minting ownCS, Rewarding sCred]` map covers `Rewarding w` only if `w = sCred`.
-/
theorem mintingRewarding_map_covers_only (ownCS : CurrencySymbol) (sCred w : ByteString)
    (r0 r1 : Data) (hne : w ≠ sCred) :
    findRedeemer (.Rewarding (.ScriptCredential w))
      [(ScriptPurpose.Minting ownCS, r0),
       (ScriptPurpose.Rewarding (.ScriptCredential sCred), r1)] = none := by
  show (if (ScriptPurpose.Minting ownCS ==
            ScriptPurpose.Rewarding (Credential.ScriptCredential w)) = true then some r0
        else if (ScriptPurpose.Rewarding (Credential.ScriptCredential sCred) ==
                 ScriptPurpose.Rewarding (Credential.ScriptCredential w)) = true then some r1
        else none) = none
  rw [show (ScriptPurpose.Minting ownCS ==
      ScriptPurpose.Rewarding (Credential.ScriptCredential w)) = false from rfl,
    rewarding_purpose_beq_false sCred w hne]
  simp

/-- **SHAPE DS1's two-entry map is STILL short of coverage.** Its withdrawal map has
the two script credentials `w0`, `w1` and its redeemer map covers only `sCred`; since
`validWithdrawals` forces `w0 ≠ w1`, at least one of the two is uncovered. -/
theorem ds1_uncovered_wdrl_exists (ownCS sCred w0 w1 : ByteString) (r0 r1 : Data)
    (hne : w0 ≠ w1) :
    findRedeemer (.Rewarding (.ScriptCredential w0))
      [(ScriptPurpose.Minting ownCS, r0),
       (ScriptPurpose.Rewarding (.ScriptCredential sCred), r1)] = none
    ∨ findRedeemer (.Rewarding (.ScriptCredential w1))
      [(ScriptPurpose.Minting ownCS, r0),
       (ScriptPurpose.Rewarding (.ScriptCredential sCred), r1)] = none := by
  by_cases h : w0 = sCred
  · exact Or.inr (mintingRewarding_map_covers_only ownCS sCred w1 r0 r1
      (fun hEq => hne (h.trans hEq.symm)))
  · exact Or.inl (mintingRewarding_map_covers_only ownCS sCred w0 r0 r1 h)

/-! ### §2.3 THE F18 AUDIT — every NEGATIVE use of the coverage rule, one by one

Task G2. `redeemerCoverageAllPlutus` / `RedeemerCoverageAllPlutus` /
`WSC.LR_REDEEMER_COVERAGE` are the ALL-PLUTUS reading of Conway's
`MissingRedeemers`, which is STRICTLY STRONGER than the rule
(`CardanoLedgerApi.V3.Contexts.coveredByNonNative_strictly_weaker`). POSITIVE
uses — the realizability inhabitants — are conservative and unaffected
(`redeemerCoverageModNative_of_allPlutus`). NEGATIVE uses ASSUME the rule and
derive a contradiction, so the error runs against them. Every negative use in the
library, and what it really establishes:

| emptiness theorem | route | witness the argument turns on | holds under the TRUE rule? | evidence |
|---|---|---|---|---|
| `t1_class_is_empty` (§1) | SPENDING, via `LR_SPEND_RUNS_VALIDATOR` + `LR_CTX` | the base input at `hp.progLogicCred` | **YES, unaffected** | never touches `scriptsNeeded`. It uses `validScriptInfo`'s FIRST conjunct: the running script's own entry. `Deployed hp` pins that script to the compiled WSC programmable-logic-base validator, a Plutus V3 script, so `isNativeScript` is irrelevant to it |
| `t1Shape_is_empty`, `t1_leafSet_is_vacuous` (§3) | wrappers of the above | same | **YES, unaffected** | same |
| `t2_class_is_empty`, `t6_class_is_empty`, `t7_class_is_empty` (`GlobalRealizability.lean` §4) | SPENDING, same route | same base input | **YES, unaffected** | same; `GlobalRealizability.lean:822-910` |
| `l1_class_is_empty_under_coverage` | WITHDRAWAL, entry 0 | `w0`, a FREE `ByteString` of `localShapedCtx` | **NO — downgraded** | now stated at `RedeemerCoverageAt w0`; faithful supplier is `RedeemerCoverageAt_of_true` with `¬ isNative w0`. Nothing in the shape pins `w0` to a deployed validator hash |
| `dt1_class_is_empty_under_coverage` | WITHDRAWAL, entry 0 | `w0` of `dtShapedCtx`, free | **NO — downgraded** | same |
| `m1_class_is_empty_under_coverage` | WITHDRAWAL, entry 0 | `w0` of `mintShapedCtx`, free | **NO — downgraded** | same |
| `g1_class_is_empty_under_coverage` | WITHDRAWAL, entry 1 | `w1` of `globalShapedCtx`, free (`w0` is the running rewarding credential; `w1` is not constrained) | **NO — downgraded** | now stated at `RedeemerCoverageAt w1` |
| `s1_class_is_empty_under_coverage` | WITHDRAWAL, entry 1 | `w1` of `seizeShapedCtx`, free | **NO — downgraded** | same |
| `t1_class_is_empty_under_coverage` | WITHDRAWAL, entry 1 | `w1` of `p1ShapedCtx`, free | **NO for this route — but the RESULT survives** | T1's emptiness is independently proved unconditionally by `t1_class_is_empty` (§1). This theorem was only the second, redundant route |
| §2.1 DS1 (`ds1_uncovered_wdrl_exists`) | WITHDRAWAL, whichever of `w0`/`w1` is not `sCred` | BOTH `w0` and `w1`, free | **NO — downgraded, and on both credentials** | the lemma itself is a pure `findRedeemer` computation and stays true; the EMPTINESS reading of it needs `¬ isNative w0 ∧ ¬ isNative w1` |
| `WSC.g6_class_is_empty` (`GlobalRealizability.lean` §4) | WITHDRAWAL, entry 1, via the AXIOM `LR_REDEEMER_COVERAGE` | `w1` of `memberShapedCtx`, free | **NO — downgraded**, and it is the worst case because the statement is UNCONDITIONAL | `g6_class_is_empty_nonNative` there is the true-rule form, with `¬ isNative w1` explicit |
| `RealizableShapes.all_old_witnesses_fail_c3_coverage` | MEASUREMENT: five pre-C2 witnesses have `redeemerCoverageAllPlutus … = false` | the uncovered purposes of those five concrete contexts | **statement YES, interpretation NO** | it is a closed `native_decide` on `Bool`s and stays true verbatim. What it does NOT establish under the true rule is "these witnesses are unrealizable": a witness whose only uncovered purpose is native passes the ledger. See `RealizableShapes.lean` §4 |

SUMMARY: **6 of 13 negative uses survive untouched** (all the SPENDING-route
ones, which never consult `scriptsNeeded`), **6 are downgraded to an explicit
non-native side condition** on one credential (DS1: two), and **1 is a
measurement whose statement survives but whose interpretation is downgraded**.
No POSITIVE result, no realizability inhabitant, and neither composed
containment theorem depends on any of these — nothing in `WSC/Composition.lean`
consumes a `*_under_coverage` theorem or `g6_class_is_empty`. What the downgrade
costs is the strength of the JUSTIFICATION for retiring the pre-C2 shapes: it is
now "empty unless witnessed by a native timelock" rather than "empty". The
re-cut shapes' realizability, which is what the campaign's results actually rest
on, is a positive claim and is unaffected. -/

/-! # §3 THE VACUOUS `LeafSet` AT SHAPE T1 — built, and labelled

Task A2 asked for a `LeafSet` term. Here is the one the shaped route yields, so that
nobody has to take §1 on trust: all four fields hold, by `absurd` on §1's emptiness
proof, and `WSC/Composition.lean`'s `top_claim` instantiates at it. **It is worth
NOTHING**, and `t1_no_honest_step` is the proof of that: no `Reachable.step` can
fire, so the instantiated top claim is `ts_genesis` with extra syntax.

It is included because F1's exact wording is "no `LeafSet` term is ever constructed
anywhere in the library", and the correct response to that is not to construct one
and declare victory — it is to construct one, show what it is worth, and put the
non-vacuous one (`WSC/Composition.lean` §11) beside it. -/

/-- SHAPE T1 as a `Shape` predicate: `ctx` shares its `TxInfo` with some instance of
SHAPE T1 whose base credential is the deployment's. This is EXACTLY the
instantiation a `LeafSet` discharged from `WSC.P1_T1` needs. -/
def t1Shape (hp : WSC.HonestParams) (ctx : ScriptContext) : Prop :=
  ∃ plc, hp.progLogicCred = Credential.ScriptCredential plc ∧
    ∃ cs tn owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
      pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
      key next tlsH ilsH gsCS w0 w1 a0 a1 fee,
      ctx.scriptContextTxInfo =
        (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest escAda qEsc
          pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
          key next tlsH ilsH gsCS w0 w1 a0 a1 fee).scriptContextTxInfo

/-- §1, packaged over the `Shape` predicate. -/
theorem t1Shape_is_empty (hp : WSC.HonestParams) (ctx : ScriptContext)
    (hdep : WSC.Deployed hp) (hoc : WSC.OnChain ctx) (hsh : t1Shape hp ctx) : False := by
  obtain ⟨plc, hbase, cs, tn, owner, inAda, qIn, ext, in2Ada, qIn2, outAda, qOut, dest,
    escAda, qEsc, pHash, pCS, pTn, pAda, pQty, dirCS, glc, slc, nHash, nCS, nTn, nAda, nQty,
    key, next, tlsH, ilsH, gsCS, w0, w1, a0, a1, fee, hEq⟩ := hsh
  exact t1_class_is_empty hp ctx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut dest
    escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc nHash nCS nTn nAda nQty
    key next tlsH ilsH gsCS w0 w1 a0 a1 fee hdep hoc hbase hEq

/-- **THE VACUOUS `LeafSet`.** Every field by `absurd`. Do not cite this as a
discharge of any leaf: cite `WSC/Composition.lean`'s `containedLeaves` for a real
one, and cite this only as the demonstration that a shaped `Shape` instantiation is
worthless. -/
theorem t1VacuousLeaves (hp : WSC.HonestParams) (hdep : WSC.Deployed hp) :
    Composition.LeafSet hp (t1Shape hp) :=
  { p4 := fun ctx _ _ _ _ hoc hsh _ _ _ _ _ _ =>
      (t1Shape_is_empty hp ctx hdep hoc hsh).elim
  , p1 := fun ctx _ _ _ _ hoc hsh _ _ _ _ _ _ _ =>
      (t1Shape_is_empty hp ctx hdep hoc hsh).elim
  , p2 := fun ctx _ _ _ _ hoc hsh _ _ _ _ _ _ =>
      (t1Shape_is_empty hp ctx hdep hoc hsh).elim
  , nopre := fun _ ctx _ _ _ _ _ htx _ _ =>
      (t1Shape_is_empty hp ctx hdep htx.1 htx.2.2).elim }

/-- **AND HERE IS WHY IT IS WORTH NOTHING.** No transaction can take a step in the
T1 class, so `Reachable hp (t1Shape hp)` is `Genesis` and the instantiated top claim
below carries no information beyond `WSC.Composition.ts_genesis`. -/
theorem t1_no_honest_step (hp : WSC.HonestParams) (hdep : WSC.Deployed hp)
    (ctx : ScriptContext) (htx : Composition.HonestTx hp (t1Shape hp) ctx) : False :=
  t1Shape_is_empty hp ctx hdep htx.1 htx.2.2

/-- The instantiated top claim at SHAPE T1 — TRUE, and VACUOUS. Kept next to
`t1_no_honest_step` so the two cannot be quoted apart. -/
theorem t1_top_claim_is_vacuous (hp : WSC.HonestParams) (hdep : WSC.Deployed hp) :
    ∀ (L : Composition.Ledger), Composition.Reachable hp (t1Shape hp) L →
      Composition.I hp L :=
  Composition.top_claim hp (t1Shape hp) (t1VacuousLeaves hp hdep) hdep

/-! # §5 THE CLAB-FIDELITY COROLLARY — why every witness looked ledger-legal

`WSC.P1ShapedWitness.ctxOk` is the accepting SHAPE-T1 witness the P1 campaign is
calibrated on: `validRewardingContext ctxOk = true` (`native_decide`, zero failing
conjuncts) and the real CEK machine halts on it in 2,603 steps. It is also, by §1,
NOT the context of any on-chain transaction of a deployment whose base credential is
`ScriptCredential "PROGLOGIC"`.

Both statements are theorems, so the conclusion is unavoidable: **CLAB's
`validRewardingContext` is strictly weaker than the ledger rules this library already
axiomatizes.** The gap is precisely the Conway `MissingRedeemers` rule —
`validScriptInfo` checks the redeemer map for the RUNNING script only
(`CardanoLedgerApi/V3/Contexts.lean:1035-1037`), never for the other scripts the
transaction needs — and `WSC/Honest.lean`'s LR-CTX audit table has no row for it.
`RedeemerCoverageAllPlutus` (§2) is the missing row.

This is not a criticism of the witnesses: they were built to satisfy the strongest
ledger predicate the substrate offers, and they do. It is the reason a whole layer of
the campaign could be built on unrealizable contexts without any check firing. -/

/-- **CLAB's ledger predicate cannot see the defect.** The library's own accepting
SHAPE-T1 witness passes `validRewardingContext` and is nevertheless unrealizable. -/
theorem clab_validRewardingContext_admits_unrealizable
    (hp : WSC.HonestParams) (hdep : WSC.Deployed hp)
    (hbase : hp.progLogicCred = Credential.ScriptCredential (ByteString.mk "PROGLOGIC")) :
    CardanoLedgerApi.V3.validRewardingContext WSC.P1ShapedWitness.ctxOk = true ∧
      ¬ WSC.OnChain WSC.P1ShapedWitness.ctxOk := by
  refine ⟨WSC.P1ShapedWitness.ctxOk_valid, fun hoc => ?_⟩
  exact t1_class_is_empty hp _ (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4 150 5
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS") (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0 50
    hdep hoc hbase rfl

/-! # §4 AXIOM CENSUS — printed at build time -/
#print axioms WSC.ShapeRealizability.validScriptInfo_false_of_no_redeemer
#print axioms WSC.ShapeRealizability.not_onChain_of_no_redeemer
#print axioms WSC.ShapeRealizability.t1_no_spending_redeemer
#print axioms WSC.ShapeRealizability.t1_class_is_empty
#print axioms WSC.ShapeRealizability.l1_class_is_empty_under_coverage
#print axioms WSC.ShapeRealizability.m1_class_is_empty_under_coverage
#print axioms WSC.ShapeRealizability.g1_class_is_empty_under_coverage
#print axioms WSC.ShapeRealizability.s1_class_is_empty_under_coverage
#print axioms WSC.ShapeRealizability.ds1_uncovered_wdrl_exists
#print axioms WSC.ShapeRealizability.t1VacuousLeaves
#print axioms WSC.ShapeRealizability.t1_no_honest_step
#print axioms WSC.ShapeRealizability.clab_validRewardingContext_admits_unrealizable

end WSC.ShapeRealizability
