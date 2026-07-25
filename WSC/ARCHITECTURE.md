I have complete, verified grounding. Notably I confirmed several facts that correct or strengthen the investigations: `MintValue := V2.Value` (no `mintToValue` needed), `validTxOutValue` already forces ada-first (discharges skeptic 1.3 via the precondition), `validXContext` bakes in value conservation (`isBalanced`) yet leaves the redeemer wholly unconstrained, and the import smoke test already exists. Here is the synthesized architecture.

---

# WSC Programmable-Tokens Containment: Lean4 + Blaster Proof Architecture

**Top claim being assured (plain English):** *In an honest deployment, programmable tokens cannot ever exist outside the mini-ledger (the `programmableLogicBase` payment credential).*

**Assurance method:** six leaf properties P1–P6, each proved `by blaster` against the **actual compiled UPLC bytecode** (gold standard, zero model-fidelity gap) wherever the bytecode decodes; a hand-written Lean composition theorem lifts the leaves to the top claim over an unbounded ledger; a closed, audit-mapped axiom set carries the irreducible "honest deployment" + "trust the Cardano ledger" core.

---

## 0. Status snapshot and resolved disagreements

### 0.1 Verified substrate facts (empirically confirmed this session; several correct the investigations)

| Fact | Location | Consequence |
|---|---|---|
| Project is `lakefile.lean`, Lean `v4.24.0`, requires `PlutusCore` (PlutusCoreBlaster @ `main`) + `Blaster` (@ `beta-lambda-cache-optimization`) via git — **PlutusCore pin SUPERSEDED by ADDENDUM E11 (local path, `cip153-value-builtins` @ `9f9ca8c`)** | `CardanoLedgerApiBlaster/lakefile.lean` | New project depends on CLAB, which transitively brings PlutusCore+Blaster. |
| Proof idiom: `#import_uplc n PlutusV3 double_cbor_hex "x.flat"` → `def nInputs p ctx : List Term := toTerm p :: xInputs ctx` → `#prep_uplc appliedN n nInputs BUDGET` → `theorem … validXContext ctx → isSuccessful (appliedN.prop p ctx) → POST := by blaster` | `Tests/Scripts/MintingPolicy/{MintingPolicy,Properties}.lean` | Canonical template for all six. |
| `MintValue := V2.Value` (abbrev) | `V3/Contexts.lean:295` | **Corrects property-statements:** `mintOf cs tn ctx := valueOf cs tn ctx.scriptContextTxInfo.txInfoMint` — no `mintToValue` accessor exists or is needed. |
| `validTxOutValue` **requires** `(Data.B "", Data.Map [(Data.B "", Data.I n)]) :: rest` with `n > 0`, `rest` sorted & positive | `V1/Contexts.lean:769-784` | **Discharges skeptic 1.3 (ada-first) via the precondition, not a new axiom.** Every input/output value is guaranteed lovelace-first; the `pstripAdaH`/`ptail#pasMap` sites are sound on ledger TxOut values. |
| `validMintValue` is **ada-free** (`adaSymbol < cs₁`), different shape from TxOut values | `V3/Contexts.lean:801-813` | The ada-strip sites must never be applied to `txInfoMint`; this becomes a code-audit item (skeptic 1.3), not an axiom. |
| `validXContext ctx = <purpose-match> && validScriptContext ctx`, `validScriptContext = validScriptInfo && validTxInfo`, and `validTxInfo` includes `isBalanced` (value conservation) | `V3/Contexts.lean:1197-1246` | **Value conservation (skeptic LR4) is available inside every leaf as a hypothesis** — it is a documented `[LEDGER-RULE]`, not merely assumed. It remains a *chain-step* axiom for the trace (§5). |
| `validXContext` never inspects `scriptContextRedeemer` | `V3/Contexts.lean:1197-1246` | **Satisfies skeptic 1.1:** the attacker-controlled redeemer is wholly unconstrained by the precondition. |
| `credentialInWithdrawals (cred : V2.Credential) (w) := Recursor.any x in w => x.1 == cred`; `ownCurrencySymbol ctx : Option V2.CurrencySymbol` | `V3/Contexts.lean:763, 629` | P3/P4/P4a statements type-check verbatim. |
| Governance (4264 B) discharges **22** `by blaster` theorems at `#prep_uplc … 9000` | `Tests/Scripts/Governance/{Governance,Properties}.lean` | Tractability precedent; seize/minting/base are smaller. |
| Import smoke test already scaffolded with all four flats via `double_cbor_hex` | `Tests/Scripts/WstImportSmoke/Smoke.lean` | Unit A0 partially done; global will fail decode until CIP-153 builtins land. |
| Extracted flats present | `…/scratchpad/uplcflats/{programmableLogicBase,programmableTokenMinting,programmableSeize,programmableLogicGlobal}.flat` | On-disk flat bytes 260/2472/3932/6880; decoded UPLC program bytes 128/1233/1963/3437 (ground truth). |

### 0.2 Resolved investigator disagreements

- **D1 — Phase B route for P1 (biggest disagreement).** *cip153-unblock* predicts P1's symbolic `unionValue`/`valueContains`/`unValueData` will time out under `by blaster` (HIGH risk) and recommends a source model for P1; *composition-axioms* optimistically lists "add builtins ⟹ P1/P5/P6 `by blaster`"; *fidelity-skeptic* wants UPLC and treats source-model as PROVISIONAL. **Resolution — staged hybrid.** Contribute the six CIP-153 builtins unconditionally (required just to *decode* the global). Then P5/P6 → UPLC `by blaster` (all agree these are structural walks). For P1: **first attempt UPLC with the builtin-algebra lemmas registered** (characterize the denotations by their per-key `lookupCoin` algebra so Blaster reasons over integer `(+,≤)`, not symbolic map-merge); **only if that stalls, fall back to a source model for P1's containment arithmetic *only***, bridged to the *same* denotations via the *same* algebra lemmas. Net added trust in the fallback = one small, auditable P1-transcription fidelity axiom. This makes the outcome empirical rather than a bet, and honors the skeptic's "UPLC preferred, source-model provisional with an equivalence bridge." (Details §2, §3.1.)
- **D2 — P2 one-shot vs decomposed.** *property-statements* writes P2 as one `by blaster`; *uplc-proof-mechanics* flags it riskiest (two data-dependently-coupled walks) and prescribes Lemma A (per-pair value-delta) + Lemma B (walk induction), with a bounded-input-length precondition as last resort. **Resolution:** state the full ground-truth postcondition (structure ∧ containment); attempt one-shot at budget 9000; **expect to need the A+B decomposition**. Bounded-length is a documented scope limitation acceptable *only because P3 carries the unbounded universal gate*. Resolve the harness's sub-lemma capability in an early spike (Unit A1).
- **D3 — tautology risk.** *fidelity-skeptic 0.1* warns a postcondition that re-invokes the validator's own accumulator is `X ⟹ X`. *property-statements* already phrases everything in ground-truth `valueOf`/base-credential sums. **Resolution:** adopt property-statements' `WSC.Spec` vocabulary (`outAtBase`, `inAtBase`, `mintOf`, `mintPos`, `seizeCorrespondence`) as **canonical for P1/P2/P6**, and make "no postcondition may mention the validator's computed `expectedValue`/`deltaAccumulator`" a hard acceptance gate.
- **D4 — directory integrity (P5 crux).** All three of *composition-axioms*, *property-statements*, *fidelity-skeptic* converge: axiomatize `directory_partition`/`DirWF` **now** as the single named top trust assumption, folding in the skeptic's datum-binding refinement (2.2), and schedule the `mkDirectoryNodeMP` UPLC formalization as the highest-value follow-on.
- **D5 — composition mechanization.** No disagreement: top claim is a hand-written Lean theorem with machine-checked leaves; optional `#kind` on an abstract arithmetic state machine. Adopted.
- **D6 — `mintToValue`.** Resolved by substrate read: does not exist; `MintValue` is `V2.Value`.

---

## 1. PROJECT LAYOUT

A **new Lean library `WSC`**, added *inside* the CardanoLedgerApiBlaster checkout as a sibling test library (mirrors how `Tests` depends on the API and reuses the `#import_uplc`/`#prep_uplc` elaborators). This avoids re-deriving the build wiring; CLAB already `require`s PlutusCore + Blaster.

```
CardanoLedgerApiBlaster/
├─ lakefile.lean                         # add:  lean_lib «WSC»   (below)
├─ WSC.lean                              # root import aggregator for the WSC lib
├─ WSC/
│  ├─ flats/                             # the four compiled validators (copied verbatim)
│  │   ├─ programmableLogicBase.flat
│  │   ├─ programmableTokenMinting.flat
│  │   ├─ programmableSeize.flat
│  │   └─ programmableLogicGlobal.flat
│  ├─ Imports.lean                       # §0.1 idiom: 4× #import_uplc + 4× #prep_uplc (per-validator budgets)
│  ├─ Redeemer.lean                      # mirror inductives + IsData instances (frozen makeIsDataIndexed tags)
│  ├─ Spec.lean                          # GROUND-TRUTH vocabulary: payCred/outAtBase/inAtBase/mintOf/mintPos,
│  │                                     #   seizeCorrespondence, custody predicates, redeemer projections
│  ├─ Honest.lean                        # honest-deployment predicates + ALL axioms (TS1-5, LR1-6, DirWF)
│  ├─ Witnesses.lean                     # anti-vacuity: positive + negative acceptance witness per validator
│  ├─ props/
│  │   ├─ P3_Base.lean                   # Phase A  (keystone; do first)
│  │   ├─ P4_Minting.lean                # Phase A
│  │   ├─ P4_Minting_Aux.lean            #   L4.1–L4.4
│  │   ├─ P2_Seize.lean                  # Phase A  (riskiest of A)
│  │   ├─ P2_Seize_Aux.lean              #   L2.1–L2.5 (Lemma A/B decomposition)
│  │   ├─ P1_Transfer.lean               # Phase B  (global; blocked until CIP-153)
│  │   ├─ P1_Transfer_Aux.lean           #   L1.1–L1.6
│  │   ├─ P5_NonMember.lean              # Phase B
│  │   └─ P6_Member.lean                 # Phase B
│  ├─ BuiltinAlgebra.lean                # Phase B: lookupCoin-algebra lemmas about the CIP-153 denotations
│  │                                     #   (lookupCoin_unionValue, valueContains_iff, insertCoin_lookup, unValueData_lookup)
│  └─ Composition.lean                   # inductive invariant I, Preservation, chain induction, TOP CLAIM
└─ (PlutusCoreBlaster/ — separate repo)  # Phase B contribution site for the six Value builtins (§2)
```

`lakefile.lean` addition:

```lean
@[test_driver] lean_lib «WSC» where
  -- reuses PlutusCore + Blaster + CardanoLedgerApi already required by the package
```

**Which file holds what (the assignment the task asks for):**
- **Imports/harness** → `WSC/Imports.lean` (the only file that names the `.flat` paths and budgets).
- **Honest-deployment predicates + axioms** → `WSC/Honest.lean` (single source of truth for every `axiom`).
- **Ground-truth spec vocabulary + redeemer decoders** → `WSC/Spec.lean` (+ `WSC/Redeemer.lean`). *Nothing here refers to the validator internals* — this is what defeats the tautology risk.
- **Each property** → `WSC/props/Pn_*.lean` (statement + `by blaster`), with `*_Aux.lean` for lemmas.
- **Composition** → `WSC/Composition.lean` (consumes the six P-theorems + axioms).
- **Anti-vacuity controls** → `WSC/Witnesses.lean`.

---

## 2. PHASE PLAN

### Phase A — P2, P3, P4 at UPLC level (gold standard, achievable now)

All three validators decode into PlutusCoreBlaster's CEK today (`dropList` + standard ops). No builtin work, no fidelity gap. Sequence **P3 → P4 → P2** (risk-ascending):

1. **A0 — substrate + import smoke.** Copy the four flats into `WSC/flats/`; confirm base/minting/seize report *"Successfully decoded"* and `#prep_uplc` succeeds; confirm global reports *"Could not decode"* (expected, gates Phase B). The `WstImportSmoke/Smoke.lean` scaffold already does the imports.
2. **A1 — P3 (base), the keystone.** 128-byte withdrawal scan; structurally identical to the proven `MintingPolicy` reference. Bare `by blaster` at budget 600 (ceiling 1200). Also proves toolchain works on *our* `double_cbor_hex` bytecode. **Spike here:** verify whether the harness supports proving auxiliary lemmas on sub-terms / `induction … <;> blaster` (needed for P2's decomposition, D2).
3. **A2 — P4 (minting).** Redeemer decode + 4-arm custody disjunction. Budget start 2000 → escalate 4000 → 9000. If the raw-field `pall` output scan (Local arm) defeats one-shot unification, `rcases` the decoded redeemer and `by blaster` each of the 4 arms (L4.1–L4.4).
4. **A3 — P2 (seize).** Budget 9000. Expect the Lemma A (per-pair `pvalueEqualsDeltaCurrencySymbol`) + Lemma B (input/output walk induction) decomposition (D2). Bounded-length precondition is the documented last resort.

Each of A1–A3 ships a **positive + negative witness** (§6, anti-vacuity) and the `#blaster (gen-cex:…)` tightness stanza on the postcondition's negation.

### Phase B — P1, P5, P6 (global `mkProgrammableLogicGlobal`, currently blocked at the flat decoder)

Root cause is narrow and confirmed: PlutusCoreBlaster's `builtinTable` has tags **94–99 commented out**, so the flat stream aborts on the first CIP-153 builtin node. The chosen route is the **staged hybrid** (D1):

- **B0 — contribute the six CIP-153 builtins to PlutusCoreBlaster (unconditionally required; ~1.5–2 days, mechanical, `dropList`-templated).** Five files:
  1. Enum: add `InsertCoin | LookupCoin | UnionValue | ValueContains | ValueData | UnValueData` after `DropList` — `PlutusCore/UPLC/Term/Basic.lean:170`.
  2. Arity (all `ArgV`, monomorphic): `Builtins.lean` `expectedArgs` after :134 — InsertCoin=4, LookupCoin=3, UnionValue=2, ValueContains=2, ValueData=1, UnValueData=1.
  3. Flat decoder: uncomment `(94,.InsertCoin)…(99,.UnValueData)` — `FlatEncoding/Basic.lean:269-274`. **This alone makes `programmableLogicGlobal.flat` decode.**
  4. Denotations: new `BuiltinFunctions/Value.lean` (template `List.lean:102`; honor reversed CEK args) + dispatch arms in `BuiltinFunctions/Evaluate.lean:146`. New `Const.Value : List (ByteString × List (ByteString × Integer))` carrier (normalized sorted assoc-list) + `packValue` (sort strict-asc, drop zeros/empties, reject `|q|>2^127-1`). Match `plutus-core/src/PlutusCore/Value.hs:300-523` **exactly**, including error conditions (unionValue overflow-error, valueContains negative-error, insertCoin 0 = delete, unValueData ordering-validation).
  5. Cost model: five `builtinCosts{A..E}` arms (template `CostModels.lean:391/…`). **Not load-bearing** — `#prep_uplc` bounds symbolic CEK steps, not ExBudget; add for realism.
- **B1 — P5, P6 at UPLC `by blaster`.** These live on the directory mint/NonMember/Member walk (symbolic key vs concrete `cs`, add-or-not an integer) — structurally identical to the Phase-A walks. Expected to blast directly once the program decodes. Budget 9000.
- **B2 — P1 at UPLC, algebra-assisted (attempt gold standard first).** Prove the four **`BuiltinAlgebra.lean`** lemmas about the *denotations from B0* (pure closed-form facts on finite lists — no ctx, no CEK, no budget):
  - `lookupCoin_unionValue : lookupCoin c t (unionValue v₁ v₂) = lookupCoin c t v₁ + lookupCoin c t v₂` (no-overflow branch)
  - `valueContains_iff : valueContains v₁ v₂ = true ↔ noNeg v₁ ∧ noNeg v₂ ∧ ∀ c t, lookupCoin c t v₂ ≤ lookupCoin c t v₁`
  - `insertCoin_lookup`, `unValueData_lookup`
  Register them so the P1 proof reduces to integer monotonicity over `lookupCoin` results (no symbolic map-merge exposed to Z3).
- **B3 — P1 fallback (only if B2 stalls, the cip153-unblock HIGH-risk prediction).** Transcribe `mkProgrammableLogicGlobal`'s TransferAct containment into `mkProgrammableLogicGlobalModel` against CLAB `Value`, with the five builtins as the *abstractly specified* operations characterized by the *same* `BuiltinAlgebra` lemmas. Add exactly **one** `axiom mkProgrammableLogicGlobalModel_faithful` (the sole trust delta vs UPLC). Every hypothesis, aux lemma, and postcondition is substrate-independent and reused verbatim; when B2 later succeeds, delete the axiom and swap the applied term back.

**Justification for hybrid over the extremes:** pure contribute-and-UPLC likely ships a red P1 (symbolic containment intractable); pure source-model discards the zero-gap UPLC results already available for P2/P3/P4 and cheaply gettable for P5/P6, and hand-models the whole validator. Hybrid confines hand-modeling to the *single* intractable obligation and still bottoms it out in the *actual* builtin denotations via B2's lemmas.

---

## 3. THE SIX THEOREMS

Common preamble (`WSC/Spec.lean`), all over **ground-truth ledger quantities** (defeats tautology, D3). `open CardanoLedgerApi.V3`, `open CardanoLedgerApi.V2 (Value valueOf merge hasCurrencySymbol CurrencySymbol TokenName Credential Address TxOut)`.

```lean
def payCred (o : TxOut) : Credential := o.txOutAddress.addressCredential

def outAtBase (base : Credential) (cs : CurrencySymbol) (tn : TokenName) (ctx : ScriptContext) : Integer :=
  (ctx.scriptContextTxInfo.txInfoOutputs.filter (fun o => payCred o == base)).foldl
    (fun a o => a + valueOf cs tn o.txOutValue) 0

def inAtBase (base : Credential) (cs : CurrencySymbol) (tn : TokenName) (ctx : ScriptContext) : Integer :=
  (ctx.scriptContextTxInfo.txInfoInputs.filter (fun i => payCred i.txInInfoResolved == base)).foldl
    (fun a i => a + valueOf cs tn i.txInInfoResolved.txOutValue) 0

-- MintValue := V2.Value, so this is direct (no mintToValue):
def mintOf  (cs : CurrencySymbol) (tn : TokenName) (ctx : ScriptContext) : Integer :=
  valueOf cs tn ctx.scriptContextTxInfo.txInfoMint
def mintPos (cs : CurrencySymbol) (tn : TokenName) (ctx : ScriptContext) : Integer :=
  let m := mintOf cs tn ctx; if m > 0 then m else 0
```

### P3 — base spend forces the global or seize validator to run (keystone; **Phase A, prove first**)

> *You cannot spend a mini-ledger UTxO unless the global (transfer) or seize validator runs — which forces P1 or P2 on every exit from the mini-ledger.*

```lean
theorem P3_base_requires_global_or_seize :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    isSuccessful (appliedBase.prop globalCred seizeCred ctx) →
      credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl := by blaster
```

- **Precondition:** `validSpendingContext` (forces `SpendingScript`, sorted `wdrl`). Assumes **nothing** about which creds are in `wdrl` (not the conclusion).
- **Strategy:** bare `by blaster`, single tail loop over `wdrl` — the `MintingPolicy` reference shape.
- **Aux:** L3.1 `wdrl_scan_sound` (validator fixpoint ≡ `credentialInWithdrawals`); likely closed inline.
- **Honest-deployment link:** none needed at the validator level — which is *why* it is both safest and the structural keystone. The lift to "P1/P2 actually ran" uses ledger axioms LR2 + TS2 (§5).

### P4 — every mint routes tokens into the mini-ledger, or is a pure burn (**Phase A**)

> *An accepted mint of `cs` satisfies one of four custody proofs: Local (its own no-escape scan), DelegateTransfer (⇒ P1), DelegateSeize (⇒ P2), or BurnOnly. Every mint drives `cs` into the mini-ledger or is a pure burn.*

```lean
theorem P4_mint_routes_or_burns :
  ∀ (protocolParamsCS mintingLogicHash : ByteString) (ctx : ScriptContext) (cs : CurrencySymbol),
    validMintingContext ctx →
    ownCurrencySymbol ctx = some cs →
    isSuccessful (appliedMinting.prop protocolParamsCS mintingLogicHash ctx) →
      LocalCustodyOk cs ctx ∨ DelegateTransferOk ctx ∨ DelegateSeizeOk ctx ∨ BurnOnlyOk cs ctx := by blaster

-- Common corollary (all four arms):
theorem P4a_mint_runs_minting_logic :
  ∀ (protocolParamsCS mintingLogicHash : ByteString) (ctx : ScriptContext) (cs : CurrencySymbol),
    validMintingContext ctx → ownCurrencySymbol ctx = some cs →
    isSuccessful (appliedMinting.prop protocolParamsCS mintingLogicHash ctx) →
      credentialInWithdrawals (Credential.ScriptCredential mintingLogicHash)
        ctx.scriptContextTxInfo.txInfoWdrl := by blaster
```

Where (`WSC/Spec.lean`, all pure over ctx): `LocalCustodyOk cs ctx` = minting-logic invoked ∧ node-NFT named `cs` present ∧ `∀ o, payCred o ≠ progLogicCred → ¬ hasCurrencySymbol cs o.txOutValue`; `DelegateTransferOk` / `DelegateSeizeOk` = minting-logic invoked ∧ reg-by-**ref** NFT named `cs` ∧ (global cred in wdrl / seize redeemer scoped to `cs`'s node); `BurnOnlyOk cs ctx` = minting-logic invoked ∧ `∀ (tn,q) ∈ ownCS mint-map, q ≤ 0`.

- **Precondition:** `validMintingContext` (forces `MintingScript ownCS`, `validMintValue`). Redeemer unconstrained.
- **Strategy:** likely bare `by blaster`; fallback `rcases` the decoded `MintRedeemer` then blast each arm.
- **Aux:** L4.1 redeemer-totality; L4.2 `local_noEscape_sound` (raw-field `pall` ⇒ non-base outputs hold zero `cs`); L4.3 `delegate_regByRef_only` (registration only via reference input — ties to P5, closes the fresh-node race); L4.4 `burnOnly_whole_map` (full token-map scan).
- **Closure:** DelegateTransfer ⟹ P1; DelegateSeize ⟹ P2/P2′; Local ⟹ L4.2 directly; BurnOnly ⟹ nothing positive.

### P2 — seizure relocates only the seized policy, and it stays in the mini-ledger (**Phase A, riskiest**)

> *An accepted SeizeAct moves only the seized policy: every base input has a continuing base output preserving address/datum/reference-script and differing at most in the seized `cs`; and the clawed delta plus any seize-mint of the seized policy never leaves the base credential.*

```lean
theorem P2_seize_relocates_only_seized :
  ∀ (protocolParamsCS : ByteString) (base : Credential) (dirCS seizedCS : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx →
    isSeizeAct ctx →
    HonestParams protocolParamsCS base dirCS ctx →
    seizedPolicyOf dirCS ctx = some seizedCS →
    isSuccessful (appliedSeize.prop protocolParamsCS ctx) →
      seizeStructurePreserved base seizedCS ctx = true
      ∧ (∀ tn, outAtBase base seizedCS tn ctx ≥ inAtBase base seizedCS tn ctx + mintOf seizedCS tn ctx)
  := by blaster   -- expect the Lemma A + Lemma B decomposition (D2)
```

`seizeStructurePreserved` (spec-level recursion over inputs × outputs-suffix from `outStartIdx`): each base input paired with a continuing output equal in `txOutAddress` (full address, staking included), `txOutDatum`, `txOutReferenceScript`, and `∀ cs tn, cs ≠ seizedCS → valueOf cs tn out = valueOf cs tn in`; non-base inputs consume no output.

- **Note:** P2(b) uses **signed** `mintOf` (a legitimate burn of the seized policy lowers the requirement), unlike P1's `mintPos`.
- **Precondition:** `validRewardingContext` (forces `RewardingScript`, `validTxOutValue` on every value — load-bearing since the seize walk assumes well-formed sorted values). `HonestParams` names `base`/`dirCS`. Do **not** assume `isSeizeAct` — but it is derivable; state it as hypothesis for readability, discharge via a decode lemma.
- **Strategy (D2):** Lemma A (`pvalueEqualsDeltaCurrencySymbol` accept ⟹ `∀ cs≠seizedCS, equal` ∧ delta = seized delta) isolates the nested value-diff; Lemma B (list induction, "base input ⟹ consume one output satisfying A"); compose. One-shot @9000 first; bounded-length last resort.
- **Aux:** L2.1 covers-all-base-inputs; L2.2 delta-is-seized-only (the `goOuter` `perror` on any non-seized divergence — verified at `ProgrammableLogicBase.hs:1795/1810/1815`); L2.3 non-contamination (`pcurrencyListHasCS` forces the paired input to actually hold `seizedCS`); L2.4 balance-invariant-sound; L2.5 seized-bound-to-authentic-node.

**P2′ (cross-validator, Phase A over the minting validator)** — a seized-policy mint cannot bypass the seize:

> *If the seized policy `cs` is itself minted in a seize tx, its minting policy's DelegateSeize arm binds that mint to this seize (same authentic node keyed `cs`, deployed seize credential).*

```lean
theorem P2'_delegateSeize_binds_mint_to_seize :
  ∀ (protocolParamsCS mintingLogicHash : ByteString) (base : Credential) (dirCS seizeCred : CurrencySymbol)
    (ctx : ScriptContext) (cs : CurrencySymbol),
    validMintingContext ctx → ownCurrencySymbol ctx = some cs →
    HonestParams protocolParamsCS base dirCS ctx →
    isDelegateSeize ctx →
    isSuccessful (appliedMinting.prop protocolParamsCS mintingLogicHash ctx) →
      IsRegistered dirCS cs ctx
      ∧ ∃ idx, redeemerAt idx ctx = some (ScriptPurpose.Rewarding (Credential.ScriptCredential seizeCred), …SeizeAct…)
      ∧ dirNodeKeyAtRefIdx (nodeRefIdxOf ctx) ctx = some cs := by blaster
```

### P1 — transfers conserve programmable tokens inside the mini-ledger (**Phase B**)

> *In an honest deployment, an accepted TransferAct never lets a registered programmable token leave or vanish from the mini-ledger: for every registered `cs` and `tn`, the amount at base outputs is at least the amount at base inputs plus any positive net mint. Unregistered policies are not programmable tokens and are correctly outside the guarantee.*

```lean
theorem P1_transfer_conserves :
  ∀ (protocolParamsCS : ByteString) (base : Credential) (dirCS : CurrencySymbol)
    (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx →
    isTransferAct ctx →
    HonestParams protocolParamsCS base dirCS ctx →
    IsRegistered dirCS cs ctx →
    isSuccessful (appliedGlobal.prop protocolParamsCS ctx) →
      outAtBase base cs tn ctx ≥ inAtBase base cs tn ctx + mintPos cs tn ctx := by blaster
```

- **Precondition:** `validRewardingContext` + `HonestParams` + `IsRegistered` + `isTransferAct`. **RHS is ground-truth** (base-input sum + positive mint), *not* the validator's `expectedValue` (D3).
- **Strategy:** B2 (algebra-assisted UPLC) → B3 (source-model fallback with one fidelity axiom).
- **Aux:** L1.1 `outAtBase_containment_sound` (must cover *all three* dispatch paths — single-asset scan, wholesale byte-equality, builtin `valueContains`; each independently ⟹ aggregate `≥`); L1.2 foldl-distribution; L1.3 `witness_forces_all_base_inputs` (`pvalueFromCred` `perror`s, does not skip, when `payCred = base` and owner witness absent ⟹ counts *every* base input); L1.4 `registered_survives_filter` (= contrapositive of P5); L1.5 `mint_positive_enters_additively` (= P6 specialized); L1.6 `filterPositive_preserves_positive`.

### P5 — a containment exemption can only be claimed for genuinely-unregistered policies (**Phase B**)

> *If the global accepts and `cs` was classified NonMember (claimed exempt via a covering directory node), then no authentic directory node is keyed `cs`. You cannot buy an exemption for a registered policy.*

```lean
theorem P5_nonmember_implies_unregistered :
  ∀ (protocolParamsCS : ByteString) (base : Credential) (dirCS : CurrencySymbol)
    (ctx : ScriptContext) (cs : CurrencySymbol),
    validRewardingContext ctx →
    HonestParams protocolParamsCS base dirCS ctx →
    classifiedNonMember cs ctx →
    isSuccessful (appliedGlobal.prop protocolParamsCS ctx) →
      ¬ IsRegistered dirCS cs ctx := by blaster
```

- **Aux:** L5.1 `covering_node_authentic` (accept + NonMember ⟹ referenced node passes `key < cs < next` ∧ `phasCSH dirCS`); L5.2 = the **`directory_partition`** axiom (§4/§5) — *without it P5 is unprovable, and correctly so.* This is the escape-critical direction.

### P6 — the Member claim is self-penalizing and sound (**Phase B**)

> *If the global accepts and `cs` was classified Member, its positive minted amount is added to (never subtracted from) the value that must remain at base outputs. Claiming Member can only enlarge the containment obligation.*

```lean
theorem P6_member_adds_to_requirement :
  ∀ (protocolParamsCS : ByteString) (base : Credential) (dirCS : CurrencySymbol)
    (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx →
    HonestParams protocolParamsCS base dirCS ctx →
    classifiedMember cs ctx →
    isSuccessful (appliedGlobal.prop protocolParamsCS ctx) →
      outAtBase base cs tn ctx ≥ mintPos cs tn ctx := by blaster
```

- **Aux:** L6.1 `member_conses_positive` (Member branch conses the mint entry unchanged, positive sign, touching no node); L6.2 `member_reversal_order` (`preverseCurrencyPairs` restores canonical order, sign preserved); reuses L1.1/L1.2/L1.6. The Member amount comes from `txInfoMint` (ledger truth), not redeemer — the attacker cannot inflate it.

**Redeemer mirror types** (`WSC/Redeemer.lean`, frozen `makeIsDataIndexed` tags, IsData instances mirroring `ScriptInfo`/`SellDatum` in CLAB): `MintProof {Member=0, NonMember nodeIdx=1}`, `PLGRedeemer {TransferAct proofs wdrlIdxs mintProofs paramsRefIdx =0, SeizeAct dirNodeIdx inputIdxs outStartIdx lenInputIdxs seizeParamsRefIdx issuerWdrlIdx =1}`, `RegWitness {RegByRefInput=0, RegByOutput=1}`, `MintRedeemer {Local=0, DelegateTransfer=1, DelegateSeize=2, BurnOnly=3}`. Conditioning postconditions on the decoded redeemer is what makes each theorem *mean* its plain-English claim.

**Per-validator budgets** (`#prep_uplc`; not load-bearing for correctness, only unroll depth): base 600 (ceiling 1200); minting 2000→4000→9000; seize 9000; global 9000.

---

## 4. HONEST-DEPLOYMENT PREDICATES

Two strata, deliberately separated (skeptic 1.2): **(i)** per-transaction ledger normalization = CLAB's `validXContext`, used verbatim as each theorem's precondition; **(ii)** global honest-deployment facts = named `axiom`s stated once in `WSC/Honest.lean`, never baked into a per-tx predicate (so a forged params/directory UTxO stays *inside* the theorem's universe).

### 4.1 Per-transaction precondition (stratum i) — reuse CLAB, calibrated

Use `validSpendingContext` / `validMintingContext` / `validRewardingContext` exactly as the reference proofs do. Verified properties that make them **minimal and non-conclusion-assuming**:

- **Fixes only the script purpose** (`SpendingScript`/`MintingScript`/`RewardingScript`) — required for `xInputs ctx` to yield `[toTerm ctx]`.
- **Guarantees value well-formedness we actually depend on:** every input/output value satisfies `validTxOutValue` ⟹ **ada-first + sorted + positive** (discharges skeptic 1.3 *in the precondition*, `V1/Contexts.lean:782`); `txInfoMint` satisfies `validMintValue` ⟹ **ada-free + sorted + nonzero**; `txInfoWdrl`/redeemers/signatories sorted; **`isBalanced`** (value conservation) holds.
- **Constrains the redeemer by *nothing*** — `validXContext` never reads `scriptContextRedeemer` (satisfies skeptic 1.1: proof lists, indices, `RegistrationWitness`, Member/NonMember claims all stay adversarial; a decode failure maps to reject, not exclusion).
- **Asserts nothing about reference inputs** being authentic directory/params nodes (skeptic 1.2 must-not-assume). Authenticity is earned at runtime by `phasCSH`/NFT gates inside the validator.

Publish, per validator, the one-line precondition annotated as "= CLAB `validXContext` = ledger normalization only." Any clause not reducible to a CLAB `[LEDGER-RULE]` tag is over-reach — there are none, because we reuse CLAB's predicate unchanged.

### 4.2 Global honest-deployment facts (stratum ii) — `WSC/Honest.lean`

```lean
-- Authentic directory node: reference input carrying the directory NFT (first non-ada policy = dirCS,
-- per phasCSH) whose datum decodes as a PDirectorySetNode.
def authenticDirNode (dirCS : CurrencySymbol) (i : TxInInfo) : Prop := …
def dirNodeKey  (i : TxInInfo) : Option CurrencySymbol := …   -- datum .pkey
def dirNodeNext (i : TxInInfo) : Option CurrencySymbol := …   -- datum .pnext

-- "cs is a genuine programmable token" ≙ an authentic directory node keyed exactly cs is present.
def IsRegistered (dirCS cs : CurrencySymbol) (ctx : ScriptContext) : Prop :=
  ∃ i ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs, authenticDirNode dirCS i ∧ dirNodeKey i = some cs

-- HONEST-DEPLOYMENT params: the redeemer-selected params ref-input is NFT-authenticated by protocolParamsCS
-- (forced on the accept path) AND — the honest part — its datum names the genuinely deployed base credential
-- and directory symbol.  Justified by the unique params NFT (TS1/TS5).
def HonestParams (protocolParamsCS : CurrencySymbol) (base : Credential) (dirCS : CurrencySymbol)
    (ctx : ScriptContext) : Prop := …
```

`Spec.lean` redeemer projections (pure decoders of `scriptContextRedeemer`, no honesty assumed): `isTransferAct`, `isSeizeAct`, `isDelegateSeize`, `classifiedMember cs`, `classifiedNonMember cs`, `seizedPolicyOf dirCS`.

---

## 5. COMPOSITION

### 5.1 Inductive invariant (`WSC/Composition.lean`)

For ledger `L`, `hold(u,cs) = Σ_tn valueOf cs tn u.value` (≥0), `Base(L) = {u : payCred u = progLogicCred}`, `OutOfBase(L,cs) = Σ_{u ∈ L\Base(L)} hold(u,cs)`, `R(L)` = registered policies (authentic directory node keyed `cs`).

```lean
-- "In an honest deployment, programmable tokens cannot exist outside the mini-ledger."
def I (L : Ledger) : Prop := ∀ cs, cs ∈ R L → OutOfBase L cs = 0
```

Two support lemmas make the quantifier over the *growing* `R` sound:
- **L-monotone** (registration is insert-only): `R L ⊆ R L'` per valid step — history property of `mkDirectoryNodeMP`.
- **L-mint-needs-reg** (no pre-registration tokens): every positive-mint arm of `mkProgrammableLogicMinting` except `BurnOnly` requires an NFT registration proof, and `BurnOnly` forbids positive mint (P4/L4.4) ⟹ a `cs` enters `R` no later than its first token.

### 5.2 Reduction to per-transaction Preservation

```lean
theorem Preservation : ∀ L tx L', validLedgerStep L tx L' → I L → I L'
```
Fix registered `cs`. By LR5 (UTxO semantics) + LR4 (conservation), `OutOfBase(L',cs) = OutOfBase(L,cs) − hold(cs, out-of-base inputs) + hold(cs, out-of-base outputs)`. `I L` gives `OutOfBase(L,cs)=0`; non-negativity forces out-of-base inputs = 0. So the obligation collapses to **Non-Escape** `NE(tx,cs) : hold(cs, out-of-base outputs) = 0`, equivalently (with conservation) `B_out(cs) ≥ B_in(cs) + mint(cs)` — exactly the shape P1/P2/P4 produce. Ledger-trigger case split:

| Branch | Ledger rule fires | Discharged by |
|---|---|---|
| (A) no base input holds `cs`, `mint(cs) ≤ 0` | — | pure conservation + `I L` |
| (B) `mint(cs) > 0` (entrance) | LR1 mint policy runs | **P4** by arm: Local ⟹ NE directly; BurnOnly excluded; DelegateTransfer ⟹ **P1**; DelegateSeize ⟹ **P2/P2′** |
| (C) spends a base UTxO holding `cs`, `mint(cs) ≤ 0` (exit) | LR3 base runs ⟹ **P3** ⟹ global/seize in wdrl ⟹ LR2 runs it | **P1** (global) or **P2** (seize) |

Exit via global uses P5 (registered `cs` can't be dropped by a covering proof) + P6 (Member adds the mint) ⟹ `B_out ≥ B_in + mint`. Exit via seize uses P2 for the seized policy and `pvalueEqualsDeltaCurrencySymbol` (every non-seized policy unchanged, all base inputs paired) for the rest. Every branch yields `NE(tx,cs)`. With genesis (TS3), induction on the reachable trace gives the top claim:

```lean
theorem no_programmable_tokens_outside_mini_ledger : ∀ L, Reachable L → I L
```

**Non-circularity (skeptic 5.3):** P4's delegate arms *witness that P1/P2 ran* (LR1 forces P4-accept, P4-delegate + LR2 forces P1/P2-accept); they do not themselves bound outputs. P3→P1/P2 rests on LR3 ("spending a script-cred UTxO runs that script"), a ledger axiom independent of any P-theorem.

### 5.3 Complete axiom list (audit-mapped)

**Trusted-setup (one-time deployment audit):**
| Axiom | Statement | Justification / audit |
|---|---|---|
| **TS1** `ts_params_authentic` | the `protocolParamsCS` NFT is unique and its datum names the genuine base/global/seize/directory creds | every validator reads config from this datum; audit the one-shot params MP |
| **TS2** `ts_script_hash_binding` | those creds = UPLC hashes of the imported `.flat` files | true by construction for imported bytecode; explicit audit item for global once decoded |
| **TS3** `ts_genesis` | `I L₀ ∧ DirWF(dir L₀)`: directory holds only sentinels, no live-cs node, `OutOfBase(L₀,·)=0` | base case |
| **TS4** `ts_minting_identity` | every programmable `cs` is a `mkProgrammableLogicMinting` instance parameterized by `(protocolParamsCS, its mintingLogicHash)` | ties abstract `R` to real policy ids |
| **TS5** `ts_singleton_config` | exactly one params NFT and one directory instance | no shadow config |

**Ledger-rule (trusting the Cardano ledger):**
| Axiom | Statement | Note |
|---|---|---|
| **LR1** `lr_mint_runs_policy` | `mint(cs) ≠ 0` ⟹ ledger runs `cs`'s policy with `scriptInfo = MintingScript cs`, rejects on error | forces P4 on entrance |
| **LR2** `lr_withdrawal_runs_validator` | a script-cred withdrawal entry ⟹ that stake validator ran & succeeded (incl. withdraw-zero) | makes P3's "cred in wdrl" mean it *ran* |
| **LR3** `lr_spend_runs_validator` | spending a script-payment-cred UTxO ⟹ that spending validator ran & succeeded | forces P3 on every base spend |
| **LR4** `lr_value_conservation` | `Σ outputs + burned = Σ inputs + minted` per `(cs,tn)` | *per-tx instance already provided inside each leaf by `isBalanced` (§0.1); axiom needed at the chain-step level* |
| **LR5** `lr_utxo_semantics` | `L' = (L \ tx.inputs) ∪ tx.outputs`, inputs distinct & existing (no double-spend) | defines the OutOfBase split |
| **LR6** `lr_scriptcontext_faithful` | the `ScriptContext` handed to each validator faithfully reflects tx inputs/refs/outputs/mint/wdrl | bridges UPLC postcondition ↔ ledger fact |
| **LR7** `lr_collateral_pubkey_only` | collateral inputs must be pubkey addresses; script-payment-cred UTxOs cannot be collateral | closes the collateral exit route (skeptic 6.1) |

**Directory integrity (the single named top assumption; escape-critical):**
| Axiom | Statement |
|---|---|
| **DirWF / `directory_partition`** | the authentic directory under `directoryNodeCS` is a sorted, unique-keyed, sentinel-bounded linked set whose `(key,next)` intervals partition the key space; **and** any UTxO holding a genuine `directoryNodeCS` token has its `(key,next)` datum constrained by `mkDirectoryNodeMP` (datum-binding, skeptic 2.2). Hence an authentic node with `key < cs < next` witnesses `cs ∉ keys`. |

Redeemer/ref-input honesty needs **no** axiom: every index is a self-validating hint (`pparamsAtRefIdx`'s `phasCSH`, `pcheckedDrop`'s negative guard, covering-interval checks), so a dishonest index only fails its own tx — liveness, never safety.

### 5.4 Clean PROVEN / ASSUMED / DEFERRED partition

- **PROVEN — machine-checked UPLC, now:** **P2, P3, P4, P2′** over the actual imported bytecode (all smaller than the proven Governance precedent).
- **PROVEN-BY-DESIGN, blocked only at the decoder (mechanical unblock):** **P1, P5, P6** (global TransferAct; CIP-153 builtins).
- **PROVEN — composition layer:** Preservation + chain induction + L-monotone + L-mint-needs-reg — hand-written Lean, leaves = P-theorems + axioms; **not push-button** (unbounded ledger); optional `#kind` on an abstract counter SM for the arithmetic core.
- **ASSUMED (explicit axioms):** TS1–TS5, LR1–LR7, **DirWF** (flagged load-bearing & escape-critical).
- **DEFERRED (priority order):** (1) contribute CIP-153 builtins ⟹ discharge P1/P5/P6 `by blaster`; (2) formalize `mkDirectoryNodeMP` at UPLC, prove `DirWF` preservation per insert, lift over history ⟹ **converts DirWF from ASSUMED to PROVEN** (highest-value follow-on, since P5 is the only escape-critical direction); (3) optional `#kind` arithmetic core.

**Residual trust surface after all deferred work:** only TS1–TS5 (deployment audit) + LR1–LR7 (trusting the Cardano ledger) — the irreducible honest-deployment core, every validator-level and directory-level claim machine-checked over real bytecode.

---

## 6. FIDELITY OBLIGATIONS (acceptance criteria)

The skeptic's checklist as concrete gates. **Status** marks what the substrate already discharges vs what the implementer must produce.

**TIER 0 — vacuity/tautology (highest priority):**
- **0.1 ground-truth postconditions** — P1/P2/P6 RHS must be `outAtBase/inAtBase/mintOf` (ground truth), never the validator's `expectedValue`/`deltaAccumulator`. *Status: enforced by design (§3, D3); reviewer rejects any postcondition mentioning validator-internal accumulators.* The real content is the bridging lemma L1.1 (`poutputsContainExpectedValueAtCred` ⟹ aggregate `≥`), which is **not** one-line `by blaster`.
- **0.2 anti-vacuity witnesses** — each of base/minting/seize (and global once decoded) ships a **positive** honest `ctx` (golden vector from the off-chain suite / `ExampleTransferLogic.hs`) with `isSuccessful` proven `True`. *Gate: no green P-set without a witnessed accepting ctx per validator; cross-check decoded fields against the CBOR the off-chain builds.*
- **0.3 polarity controls** — each validator ships a **negative** control (`¬POST → isUnsuccessful`) plus the `#blaster (gen-cex: 0) (solve-result: 1)` tightness stanza on the postcondition's negation (mirrors `MintingPolicy/Properties.lean:47-53`). Pins the accept/reject axis from both sides.

**TIER 1 — precondition over-reach:**
- **1.1 redeemer wholly unconstrained** — *Status: DISCHARGED by substrate* (`validXContext` never reads `scriptContextRedeemer`, §0.1). Gate: line-audit the final theorems — no hypothesis may constrain proof lists/indices/`RegistrationWitness`.
- **1.2 authenticity as global axioms, not per-tx** — *Status: DISCHARGED by design* (`HonestParams`/`IsRegistered`/DirWF in `Honest.lean`, never in `validXContext`). Publish each per-validator precondition annotated may-assume vs must-not-assume.
- **1.3 ada-first** — *Status: DISCHARGED by substrate* (`validTxOutValue` forces lovelace-first, §0.1). Remaining **code-audit item:** confirm each of the three ada-strip sites in the global (`ProgrammableLogicBase.hs:133,471,667`) is only reached on ledger TxOut values, never `txInfoMint` (which is ada-free).

**TIER 2 — directory integrity (crux):**
- **2.1 / 2.2** — state DirWF (with datum-binding) as the single named top trust assumption; mark P5's strength = exactly DirWF's strength. Gate: DirWF appears prominently in the top-claim docstring; DEFERRED-2 discharges it.
- **2.3 minting↔global consistency** — prove "in one tx, no `cs` admits both an authentic keyed node and an authentic covering node," from DirWF, with both nodes authenticated against the *same* `directoryNodeCS` from the *same* authenticated params; confirm `regByRef`-only (no output-arm) at `Issuance.hs:207` is normative (L4.3).

**TIER 3 — abstract-spec weakness:**
- **3.1 containment over every (cs,tn), all three dispatch paths** — L1.1 must show single-asset scan, wholesale byte-equality, *and* builtin `valueContains` each independently imply the aggregate `≥` (the source comment at `:560` asserting path-equivalence is not a theorem).
- **3.2 mint sign / Member self-penalization** — only positive mint raises the requirement; burns do not; explicitly test `mint<0` does not lower base-input containment (P6, L1.6).
- **3.3 payment- vs staking-credential scope** — **document the boundary:** P1 proves *aggregate containment at the base payment credential*, NOT per-holder ownership; intra-ledger reshuffling between holders is enforced by per-policy transfer-logic scripts, **outside** this formalization. No summary may overclaim.
- **3.4 seize both halves** — P2 must conjoin corresponding-output preservation (full address incl. staking, datum, refscript byte-identical) AND remaining-output containment; treat each `pvalueEqualsDeltaCurrencySymbol` branch (`:1795/1801-1817/1827`) as a distinct obligation (historically bug-prone: the `:1738/1740` silently-dropped-token fix).

**TIER 4 — source-model divergence (only if P1 uses B3 fallback):**
- **4.x** — model each of the five builtins from `Value.hs` *including* error conditions (unionValue overflow-error, valueContains negative-error, insertCoin-0-deletes, unValueData ordering-validation); model all three `pvalueFromCred` phases and all three containment paths; replicate the exact cons/reverse accumulator order (the landed "accumulator-order fix"). **Preferred bar: eliminate the model via B2 (UPLC).** If B3 ships, mark P1 **PROVISIONAL** with golden cross-checks (real CEK output ≡ model on sampled ctx) + the single `_faithful` axiom.

**TIER 5 — composition/circularity:**
- **5.1 shared TxInfo** — the top theorem instantiates each per-validator theorem at *one common* `TxInfo` (LR6), never conjoins independently-quantified `ctx`s.
- **5.2 / 5.3 / 5.4** — LR1/LR2/LR3 stated and connected (cred read from wdrl/params = cred the theorem is parameterized by, via TS1); confirm each of global (`pvalueFromCred`) and seize (`processThirdPartyTransfer`) *independently* constrains **every** base input, and that a script-staking base input fails closed on missing withdrawal (`pisScriptInvokedEntries` `phead`s ⟹ errors on empty).

**TIER 6 — scope gaps:** LR7 closes collateral (6.1); enterprise-address base outputs fail closed on transfer, movable only via seize (6.2); withdrawals carry only lovelace (6.3); datum/refscript swaps allowed on transfer by design, preserved on seize — documented (6.4); every `pdropList`/`phead` index deref is followed by an authentication gate or fails closed on bad index (6.5); `BurnOnly` full-scans the ownCS mint-map (6.6, L4.4).

**One-line acceptance gate:** ground-truth non-tautological postconditions (0.1) + positive/negative witnesses per validator (0.2/0.3) + published redeemer-unconstrained preconditions (1.x) + DirWF named as top assumption (2.x) + aggregate all-path correct-sign containment with scope boundary documented (3.x) + global proven at UPLC (preferred) or provisional model with cross-checks (4.x) + one-shared-TxInfo composition with explicit LR axioms (5.x) + every exit route closed or scoped (6.x).

---

## 7. PARALLELIZABLE IMPLEMENTATION PLAN

Legend: **[A]** Phase A (do first, low risk, gold standard now) · **[B]** Phase B (higher risk, needs decoder unblock) · risk ↑ within each phase.

### Foundation (blocks everything; single owner, ~0.5 day)
- **U0 [A] — substrate + spec skeleton.** Add `lean_lib «WSC»`; copy four flats to `WSC/flats/`; write `Imports.lean` (4× import/prep) and confirm base/minting/seize decode, global does not (extends `WstImportSmoke`). Write `Spec.lean` (ground-truth vocab), `Redeemer.lean` (mirror types + IsData), `Honest.lean` (predicate + axiom *signatures*, `sorry`-free stubs). **Deliverable other units import.** *Depends on: nothing.*

### Phase A units (all unblocked by U0; parallelizable)
- **U1 [A] — P3 base (keystone) + toolchain spike.** `props/P3_Base.lean`, bare `by blaster` @600. **Also resolves the harness sub-lemma/`induction<;>blaster` capability** that U3 needs. Ship positive+negative witnesses. *Depends on: U0. Lowest risk — do first as the smoke-proof of the whole pipeline.*
- **U2 [A] — P4 minting + P2′.** `props/P4_Minting*.lean`, L4.1–L4.4; `P4a`; `P2'`. *Depends on: U0. Medium risk (raw-field Local scan).* Parallel with U1/U3.
- **U3 [A] — P2 seize.** `props/P2_Seize*.lean`, L2.1–L2.5, Lemma A + Lemma B decomposition. *Depends on: U0 + U1's capability spike. Highest Phase-A risk; budget 9000; bounded-length fallback documented.*
- **U4 [A] — anti-vacuity + fidelity controls.** `Witnesses.lean` (golden vectors from off-chain suite), negative controls, `#blaster` tightness stanzas; the §6 Tier-0/1/3 code-audit items for base/minting/seize. *Depends on: U1/U2/U3 statements exist (can start against stubs).* Parallel.

### Phase B units (gated on the decoder contribution)
- **U5 [B] — CIP-153 builtins in PlutusCoreBlaster.** Enum + arity + flat-table + denotations (`BuiltinFunctions/Value.lean`) + cost stubs, matching `Value.hs`. **Deliverable: `programmableLogicGlobal.flat` decodes and `#prep_uplc @9000` succeeds.** *Depends on: nothing (separate repo) — can run fully parallel to all of Phase A. Highest external risk; ~1.5–2 days mechanical. Start it at the same time as U0 so Phase B isn't serialized behind Phase A.*
- **U6 [B] — P5 + P6 at UPLC.** `props/P5_NonMember.lean`, `props/P6_Member.lean`, L5.1/L6.1/L6.2, `by blaster` @9000. *Depends on: U5 + U0. Low/medium risk (structural walks).* 
- **U7 [B] — BuiltinAlgebra + P1 (B2 route).** `BuiltinAlgebra.lean` (four lookupCoin-algebra lemmas about the U5 denotations) + `props/P1_Transfer*.lean` L1.1–L1.6, algebra-assisted `by blaster`. *Depends on: U5 + U0 + (reuses P5 via L1.4). Highest Phase-B risk.*
- **U7′ [B] — P1 source-model fallback.** Trigger only if U7 stalls: `mkProgrammableLogicGlobalModel` + one `_faithful` axiom, bridged through the *same* `BuiltinAlgebra` lemmas; golden cross-checks. *Depends on: U7 attempt outcome. Contingent.*
- **U8 [B] — global fidelity controls.** Global positive/negative witnesses; §6 Tier-3.1 (all three dispatch paths), Tier-4 (if U7′), Tier-2.3 consistency lemma. *Depends on: U6/U7.*

### Composition + directory (final integration)
- **U9 [A/B mixed] — composition.** `Composition.lean`: `I`, `Preservation`, chain induction, L-monotone, L-mint-needs-reg, top claim; wires LR/TS axioms and the P-leaves. Can be drafted against **Phase-A leaves + axiomatized P1/P5/P6** immediately (so the top claim compiles end-to-end before Phase B lands), then re-pointed to the real P1/P5/P6 once U6/U7 close. *Depends on: U1–U3 (real), U6/U7 (deferred swap-in), U0 axioms.*
- **U10 [DEFERRED] — DirWF discharge.** Import `mkDirectoryNodeMP.flat`; prove `DirWF` preservation per insert at UPLC; lift over history. Converts DirWF ASSUMED→PROVEN. *Depends on: U5 pattern (uses the same import/blaster machinery). Schedule after U6/U7; highest assurance ROI.*

### Critical path & risk ordering
```
U0 ──┬─► U1 (keystone + spike) ──► U3 (seize) ─┐
     ├─► U2 (minting + P2') ─────────────────── ┼─► U9 (composition, Phase-A leaves) ─► TOP CLAIM (Phase-A-backed)
     └─► U4 (anti-vacuity A) ───────────────────┘
U5 (builtins, parallel from t0) ─► U6 (P5/P6) ─┬─► U9 re-point ─► TOP CLAIM (fully UPLC-backed)
                                  └─► U7 (P1) ─┴─(U7′ fallback)─► U8
                                                     U10 (DirWF) ─► residual-trust minimized
```
Start **U0 and U5 simultaneously** so the two-repo work (Lean proofs vs Blaster builtins) never serializes. Ship a green top claim on Phase-A leaves early (U9 with P1/P5/P6 axiomatized), then replace the three axioms with U6/U7 outputs. **DirWF (U10) is the last mile that turns the biggest assumption into a proof — schedule it, don't let it hide in "honest deployment."**
---

# ADDENDUM v3 — BINDING REVIEW RESOLUTIONS (supersedes conflicting text in the base architecture)

The adversarial review returned GO-WITH-CHANGES. The following ten edits are BINDING on the
implementation. Where they conflict with the base architecture document, the addendum wins.

## E1 (T1, was BLOCKER) — Bounded-transaction scope, stated honestly everywhere
`#prep_uplc … n` bakes a concrete CEK step budget; `runSteps` returns `State.Error` when the budget
is exhausted (`CekMachine.lean:233`), and `isSuccessful` matches only `.Halt`. Hence every
`isSuccessful (prop …) → POST` theorem constrains ONLY transactions whose validator run halts
within the budget. Mandatory consequences:
- New axiom in `Honest.lean`: `LR-BUDGET`: for any transaction whose validator execution halts
  within K CEK steps, ledger-accept ⟺ `isSuccessful (appliedX.prop …)`. K is per-validator and
  must be computed and published (empirically calibrated with concrete accepting ctxs run through
  `cekExecuteProgram`).
  > **IMPLEMENTATION DEVIATION, recorded (task A1, 2026-07-25) — comment only, no
  > requirement is withdrawn.** The four `LR_BUDGET_*` axioms name
  > `Runs.XRun K` (`WSC/Runs.lean`) rather than `appliedX.prop`.
  > `Runs.XRun K params ctx = cekExecuteProgram <imported flat>.script
  > (<WSC/Prep inputs fn> params ctx) K` — i.e. literally the last clause of this
  > requirement ("concrete accepting ctxs run through `cekExecuteProgram`"), with
  > no `Blaster.Optimize` pass interposed. Everything E1 demands is preserved: the
  > bound is on CEK STEPS, budget exhaustion is still `State.Error`, `K` is still
  > per-validator and published as a `def` (seven of them now, each ≥ a named
  > witness's measured accepting step count), and the scope language is unchanged.
  > What the deviation buys: the connective to a shaped theorem becomes the
  > kernel-checked `rfl` `ShapeBridge.exec_<S>` instead of a solver verdict, the
  > side condition `GlobalPreppedAt` disappears, and the axioms become statable at
  > the budgets 2500/3300/3800/4400 where no `#prep_uplc` is affordable. What it
  > does NOT buy: nothing about shape coverage, and `PropExecFaithful` still binds
  > the shaped layer (the P-theorems remain on `.prop`). Full rationale in
  > `WSC/Honest.lean` §LR-BUDGET "RESTATEMENT"; disposition per audit finding in
  > `WSC/AUDIT.md` Appendix A.
- The invariant `I(L)`, `Preservation`, and the top claim are scoped to the bounded-tx class
  (`validLedgerStep` gains a `WithinBudget tx` hypothesis), OR the top claim carries an explicit
  unproven residual for >K transactions. The docstring of the top theorem MUST state this.
- DELETE every occurrence of "P3 carries the unbounded universal gate" and any claim that
  Phase-A leaves are unqualified "PROVEN". Label: "machine-checked for all transactions within
  the published step bound K (bounded model checking over the real bytecode)".
- DEFERRED research note: a length-generalizing proof mode is an open substrate gap; the plan
  must not depend on it.

## E2 (T2) — Governance precedent struck; empirical spike gates P1/P2
[RESOLVED 2026-07-24 — spike completed; findings in WSC/SPIKE-FINDINGS.md. Verdicts:
 (a) P2 one-shot NOT plausible: needs lemma-DAG decomposition AND shaped contexts (fixed spines +
     concrete redeemer indices) — fully-symbolic prep never completes at any non-vacuous budget;
     seize accept is UNSAT within 600/1000 steps (vacuity-probed).
 (b) P1 B2 algebra-assisted plausible CONDITIONAL on blaster-friendly restatement of the CIP-153
     denotations (pattern-match recursions, not stdlib combinators); do not jump to B3.
 (c) Harness: `have`-threading only (no simp/lemma-name reuse); `#blaster` not `#solve`;
     blaster-proved theorems close via admit (whitelist in audits); Z3-only timeouts.]

## E3 (S1) — P5's postcondition is the covering-node witness
`¬ IsRegistered dirCS cs ctx` (this-tx reference inputs) does NOT feed the composition. P5 becomes:
  `classifiedNonMember cs ctx ∧ accept ⟹ ∃ i ∈ refInputs ctx, authenticDirNode dirCS i ∧
   dirNodeKey i < cs < dirNodeNext i`
plus a composition bridge lemma
  `covering_node_excludes_registration : (∃ authentic covering node for cs in L) ∧ DirWF L ⟹ cs ∉ R L`.
Branch C of Preservation routes registered⟹Member through this pair, never through `¬IsRegistered(ctx)`.

## E4 (S2) — DirWF strengthened to three conjuncts
 (i) insert-only / no key removal (⟹ L-monotone; no deregistration attack),
 (ii) global key-uniqueness across all authentic nodes in L,
 (iii) NFT-name = node-key datum binding (any UTxO carrying a genuine `directoryNodeCS` token is an
      authentic node with well-formed `(key, next)` and NFT name = `key`).
U10 must prove all three. (i)+(iii) are escape-critical; they appear in the top-claim docstring.

## E5 (S3) — New axiom LR-CTX
For every real script invocation, the ledger-constructed ScriptContext satisfies the matching
`validXContext`; plus a clause-by-clause audit table mapping each conjunct to the Cardano ledger
rule entailing it.

## E6 (S4) — Non-negativity axiom
`∀ u ∈ L, ∀ cs tn, valueOf cs tn u.value ≥ 0` (used by the Preservation reduction).

## E7 (F1) — Flat-provenance gate
Compute each imported flat's script hash and assert equality with the deployment suite's hash;
record sha256 + provenance in `WSC/flats/PROVENANCE.md`. TS2 is "checked", not "by construction".

## E8 (F2) — Golden-CBOR redeemer gate + positional classifiedMember
Every IsData mirror instance gets a golden round-trip vs off-chain-produced CBOR; tags read off
`makeIsDataIndexed` in source. `classifiedMember/NonMember cs` are POSITIONAL (index of cs in the
sorted txInfoMint entries walked in lockstep with the proof list).

## E9 (F3/F4) — Corrected discharges + boundary witnesses
`validScriptInfo` DOES read the redeemer (consistency only, never content). Anti-vacuity witnesses
certify behavior only within K; the negative control `¬POST → isUnsuccessful` is satisfied by
budget-Error and cannot detect the bound — pin tightness with K-sized accepting AND rejecting
concrete ctxs per validator (vacuity probes per the E2 spike are mandatory for every prep).

## E10 — Relabeled partition
P2/P3/P4/P2′: "expected-provable, bounded". P1: "bounded; PROVISIONAL risk via B3". P5/P6:
"bounded; expected after CIP-153 decode". DirWF: ASSUMED, escape-critical, U10 scheduled.
Never "PROVEN-BY-DESIGN".

## E11 — Substrate pins (X4; supersedes the "PlutusCoreBlaster @ `main`" row of §0.1)

**Current pins** (`CardanoLedgerApiBlaster/lakefile.lean`, branch `wsc-containment-proofs`):

| Dependency | Pin | Why |
|---|---|---|
| `Blaster` | git `https://github.com/input-output-hk/Lean-blaster` @ `beta-lambda-cache-optimization` (resolved `59db213`) | UNCHANGED — the solver pin stays on its git rev. |
| `PlutusCore` | **local path** `/home/gumbo/iohk/PlutusCoreBlaster`, branch `cip153-value-builtins` @ `9f9ca8c76baf3b5efdb63c33ca0091efa606b474` | The CIP-153 Value builtins live only on this (unpushed) branch; without them the global validator does not even DECODE. |

**Why the local path.** `programmableLogicGlobal` is compiled against the CIP-153 Value builtins.
PlutusCoreBlaster `main` @ `4ef48606303c45225d3ed2e2a87fc50280a763b7` has flat builtin tags 94–99
commented out (`PlutusCore/UPLC/FlatEncoding/Basic.lean:269+`), so the import fails with
`Decoding error … Could not decode program!` (negative control re-verified 2026-07-25 by running the
same `#import_uplc` against the stale `.lake/packages/PlutusCore` @ `4ef4860` build). Against the
local branch the same flat reports
`Successfully decoded double CBOR hex 'WSC/flats/programmableLogicGlobal.flat'`, and the decoded
program carries **46 CIP-153 builtin occurrences** (InsertCoin 4, UnionValue 14, ValueContains 2,
ValueData 4, UnValueData 22, LookupCoin 0) out of 282 builtin occurrences / 3444 term nodes — i.e.
tags 94–99 are genuinely consumed, not silently skipped. This unblocks P1/P5/P6 *in principle*
(WSC/Prep/Global.lean; P-theorems still gated on Stage-3b shaped preps + measured K).

**What the branch contains** (2 commits, +2832/−6 over `a04042c`):
`830819b` adds the six CIP-153 builtins end-to-end — `BuiltinFun` constructors
(`Term/Basic.lean`), flat tags 94–99 (`FlatEncoding/Basic.lean`), textual encoding, `ToExpr`,
denotations (`BuiltinFunctions/Value.lean`), cost-model entries for all five budget eras
(`CostModels.lean`), plus `PlutusCore/Value/{Basic,Tests}.lean`.
`9f9ca8c` adds the blaster-friendly denotation restatement + `PlutusCore/Value/Algebra.lean`
(53 lemmas) that P1's containment algebra will be have-fed from (D1 resolution, §0.2).

**How to restore the git pin.** In `lakefile.lean` replace
`require PlutusCore from "/home/gumbo/iohk/PlutusCoreBlaster"` with the commented line kept directly
above it (`require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"`),
then `lake update PlutusCore` to rewrite `lake-manifest.json` (the manifest entry flips between
`{"type":"path","dir":…}` and `{"type":"git","rev":…}`). Reverting drops the global validator back to
"does not decode" — `WSC/Prep/Global.lean` (and therefore `WSC/Imports.lean`, `WSC.lean`) will fail
to build, so the import must be commented out again in lockstep.

**Reproducibility requirement (BINDING).** This checkout is currently reproducible only on this
machine: `git ls-remote origin cip153-value-builtins` on the PlutusCoreBlaster remote returns
nothing — the branch is UNPUSHED. Before the WSC proof library can be built anywhere else (CI
included), `cip153-value-builtins` must be pushed to `input-output-hk/PlutusCoreBlaster` and the
`lakefile.lean` pin changed to `git … @ "cip153-value-builtins"` (or the merge commit), pinned by
full rev, not branch name. Until then, any claim of the form "P1/P5/P6 proved against production
bytecode" carries the caveat that the verifying substrate exists only as a local branch. The
`dropList`-only trio (base/minting/seize) is unaffected: it decodes on both substrates, and the
repoint was verified behaviour-neutral for it (X4 step 4 regression gate: P3_Base's five markers
unchanged; base non-vacuous @600, minting/seize vacuous @600).

> **PARTIAL DISCHARGE (task E5, 2026-07-25) — the paragraph above stands, with one
> change.** "Reproducible only on this machine" is no longer accurate, and "must be
> pushed *before* it can be built anywhere else" is now too strong. The repository
> carries `WSC/substrate/pcb-cip153-value-builtins.bundle` — an **incremental** git
> bundle (39,068 bytes, sha256
> `3d34a23d5e25ac09beddcdf6032ecb3d13c47d064239b09be8040842d1a82789`) holding exactly
> the two branch commits on top of the PUBLIC base `a04042c`. Task E5 applied it from
> a clone of the base and verified it reconstructs HEAD `9f9ca8c` and tree
> `e75862b26b5055e8cc36ea8cf393054e2417ca62` with `diff -r` clean. The revision is now
> also recorded in `lake-manifest.json` (lake **preserves** `"rev"`/`"inputRev"` on a
> `"type":"path"` entry across a full build — measured; it does not *verify* them, and
> `lake update` would drop them).
>
> **What remains binding:** the branch is still unpushed, so the bundle's custody is
> the trust anchor; the `require` is still an absolute path, so building elsewhere
> needs a two-file edit (`lakefile.lean` AND the manifest's `"dir"`). Pushing the
> branch and restoring a real git pin retires all of it in one line.
>
> Recipes: `WSC/substrate/README.md` (apply/verify, and why a whole-history bundle
> made from this SHALLOW clone would be unusable) and `WSC/REPRODUCE.md` (full
> third-party build). Audit disposition: `WSC/AUDIT.md` §6.2 — D5 downgraded
> HIGH/OPEN → MEDIUM/PARTIALLY REPAIRED, not closed.
