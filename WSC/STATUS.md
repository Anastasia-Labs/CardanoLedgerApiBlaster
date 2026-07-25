# WSC containment campaign — AUTHORITATIVE STATUS

**Read this first.** Everything below is either machine-checked in this
repository or measured in this repository, with the file/line or measurement
cited. Where a result is not there yet, this table says so in those words.

* Top claim being pursued (plain English): *in an honest deployment,
  programmable tokens cannot exist outside the mini-ledger (the
  `programmableLogicBase` payment credential).*
* Method: leaf properties proved `by blaster` against the **actual compiled
  production UPLC bytecode**, under a per-validator **CEK step budget**; a
  hand-written composition theorem (not yet written) lifts the leaves; a closed,
  audit-mapped axiom set (`WSC/Honest.lean`) carries the "honest deployment" +
  "trust the Cardano ledger" core.
* Last updated: 2026-07-25 (task Z4 — global source model, P1/P6). Baseline
  commit `dd86906`; global-model work on top of `fc44f3d`.

## 0. The three sentences that must never be dropped

1. **Everything is BOUNDED.** `#prep_uplc … n` bakes a finite CEK step budget
   into the term the theorems quantify over; exceeding it evaluates to `Error`,
   which makes `isSuccessful` false and any `accept → POST` theorem vacuous past
   the bound. Every result below is bounded-transaction model checking of the
   real bytecode (ADDENDUM E1). **No result here covers unboundedly large
   transactions.**
2. **The prep-cost wall, not the validators, is the blocker.** The validators
   halt in 208–4,647 CEK steps on real golden transactions, but symbolic
   `#prep_uplc` cost grows exponentially in the BUDGET (marginal doubling every
   ~100–113 budget steps) and then hits a cliff. Measured:
   `WSC/goldens/K-MEASUREMENTS.md` §5.1.
3. **`DirWF` is the single escape-critical assumption.** P5 is exactly as strong
   as `DirWF` (`WSC/Honest.lean` §Dir). U10 (`mkDirectoryNodeMP` at UPLC) is what
   would turn it from ASSUMED into PROVEN.

## 1. Property status table

State vocabulary (only these five are used):

* `PROVEN-AT-UPLC-WITHIN-BUDGET-K` — a `by blaster` theorem over the real
  bytecode exists in this repo, at a named budget, with a non-vacuity witness.
* `IN PROGRESS` — being attempted by a task in flight; **no claim is made**.
* `NOT-REACHABLE-AT-UPLC-see-source-model-route` — measured out of reach at UPLC
  over a fully symbolic context; needs shaped contexts or the source-model (B3)
  route.
* `BLOCKED-ON-BUDGET` — the property is expected to be provable, but the prep
  budget in the repo today is below the measured non-vacuity floor, so any
  theorem stated now would be vacuous.
* `DEFERRED` — not started; depends on work that is not scheduled yet.

| Prop | Plain English | State | Budget K / non-vacuity witness | Honest caveat |
|---|---|---|---|---|
| **P3** | *You cannot spend a mini-ledger UTxO unless the global (transfer) or seize validator runs in the same transaction.* | **PROVEN-AT-UPLC-WITHIN-BUDGET-K** — `WSC/Props/P3_Base.lean:67` (`P3_base_requires_global_or_seize`), plus negative control `:83`, tightness stanza `:100` (Falsified), vacuity probe `:112` (Falsified), concrete accepting witness `:190`/`:197`. | **K = 600** (`WSC/Prep/Base.lean:39`). Witnesses: golden `programmableLogicBase.base-spend-transfer-tx` halts accepting in **208** CEK steps (K-MEASUREMENTS §3); in-library concrete ctx `WSC.P3Witness.ctx` accepted by the real CEK at 600. Prep cost ~11 s. | Covers base-spend runs halting within 600 steps only. Its conclusion is "the credential is in `txInfoWdrl`"; upgrading that to "the validator actually ran" is the ledger axiom `LR_WDRL_RUNS_VALIDATOR`, not part of the proof. |
| **P4** | *Every accepted mint routes tokens into the mini-ledger or is a pure burn (Local / DelegateTransfer / DelegateSeize / BurnOnly).* | **IN PROGRESS** (a parallel task is raising `WSC/Prep/Minting.lean` from 600 to ~900 and attempting the theorem). At commit `dd86906` the prep is 600, which is **BLOCKED-ON-BUDGET**. | Target **K_mint = 900** (`WSC/Honest.lean`). Non-vacuity floor **784** = golden `mint-burnonly` (K-MEASUREMENTS §3/§4). Prep cost measured **27.6 s @ 900**. | At 900 the scope is "burn-only-sized minting transactions". The other two accepting minting goldens need 1,257 and 1,681 steps; a prep at 1,700 did **not** finish in 48.6 min, so widening is not available. **Additionally: `validMintingContext` WAS UNSATISFIABLE for real issuance transactions** — defect D1, **FIXED by task Z1** (§3), so the hypothesis is now satisfiable on the target class; what remains is the solver wall. |
| **P4a** | *Every accepted mint invokes the token's own minting-logic script (common corollary of all four arms).* | **IN PROGRESS** — same task, same prep, same budget as P4. | Same as P4. | Same as P4; defect D1 is FIXED (§3), so the remaining blocker is solver search, not vacuity. |
| **P5** | *A containment exemption can only be claimed for a genuinely unregistered policy: accept + NonMember ⟹ an authentic directory node covers `cs` (`key < cs < next`).* | **IN PROGRESS** (a parallel task is raising `WSC/Prep/Global.lean` from 600 to 1,600 and attempting the theorem). At `dd86906` the prep is 600 and its own probe CHARACTERIZES that as vacuous (`WSC/Prep/Global.lean:78-83`), so **BLOCKED-ON-BUDGET**. | Target **K_global = 1600**. Non-vacuity floor **1,554** = golden `transfer-nonmember-covering-node` — which is exactly P5's subject shape (ADDENDUM E3). Prep at 1,600 **measured 35.7 min / 1.55 GB, COMPLETED** (K-MEASUREMENTS §5.1). | P5's strength = `DirWF`'s strength; the postcondition is the covering-node witness, **not** `¬ IsRegistered` (E3). The bridge from a covering node to "not registered in the ledger" is the composition lemma `covering_node_excludes_registration`, which does not exist yet. Requires the CIP-153 PlutusCoreBlaster branch, which is **unpushed** (ADDENDUM E11). |
| **P6** | *Claiming Member is self-penalizing: an accepted Member classification adds the positive minted amount to the value that must remain at base outputs.* | **PROVED-ON-SOURCE-MODEL (core), STATED (inequality form)** — the self-penalization CORE is machine-checked on the source model: `WSC/Props/P6_Member.lean:mintWalk_sublist` (the mint walk returns an order-preserving SUBLIST of `txInfoMint`, so every retained entry is byte-identical ledger truth and the walk has no quantity arithmetic at all — nothing can be negated) and `:mintWalk_member_retains` (a `Member` proof retains its entry while touching no directory node). The §3-P6 INEQUALITY `outAtBase ≥ mintPos` is `WSC/Props/P1_Transfer.lean:P6_model` — STATED, not proved (needs L1.1a/b + L1.2 + L1.6). | **No UPLC K.** Not attempted at UPLC: the Member-transfer accepts cost 3,262 / 3,726 CEK steps and no Member-shaped accept below 1,600 has been measured. Model-level non-vacuity witness: the accepting golden `transfer-member-single-policy` (`WSC/Model/GlobalGoldens.lean`). | Model-level, so it rests on `globalModel_faithful` (one axiom, 4/4 golden agreement — see the P1 row). The inequality form additionally needs the un-discharged links listed in the OBLIGATION STATUS block. |
| **P2** | *An accepted seizure relocates only the seized policy and it stays in the mini-ledger (structure preserved + clawed delta contained).* | **NOT-REACHABLE-AT-UPLC-see-source-model-route** | **No published K.** Cheapest accepting seize run = **2,570** steps; symbolic prep at 2,000 never completed in 77 min and at 9,000 never completed in 62 min; 2,570 extrapolates to ≥ 15 days. Vacuity probes at 600 and 1,000 returned `Valid` for "no accepting context exists" (E2 spike). | `WSC/Honest.lean`'s `LR_BUDGET_seize` deliberately publishes **no** `K_seize` and is gated on a non-vacuity hypothesis that is measured FALSE. Routes: shaped contexts (fixed spines **and** concrete redeemer indices **and** concrete `Data` scalars — shaping spines alone was measured insufficient) with per-shape K, or the source-model route with a compilation-fidelity bridge. |
| **P2′** | *A seized-policy mint cannot bypass the seize: the issuance `DelegateSeize` arm binds that mint to this seize.* | **DEFERRED** | — | Lives on the minting policy, so it inherits P4's budget situation, and its postcondition also names the seize redeemer — so it is only meaningful once P2 (or a shaped P2) exists. |
| **P1** | *Transfers conserve programmable tokens inside the mini-ledger: for every registered `(cs, tn)`, the amount at base outputs is at least the amount at base inputs plus the net mint.* | **NOT-REACHABLE-AT-UPLC** (unchanged) — **SOURCE MODEL BUILT AND CROSS-CHECKED; ONE containment path PROVED on it.** `WSC/Model/GlobalModel.lean` transcribes the whole `TransferAct` path with per-clause source citations and calls PlutusCoreBlaster's real CIP-153 builtin denotations rather than modelling them. `WSC/Model/GlobalGoldens.lean` proves by `native_decide` that the model's verdict equals the REAL bytecode's on **4/4** global goldens, including the rejecting `transfer-containment-violation-REJECT`. PROVED on the model: `WSC/Props/P1_Transfer.lean:pathC_sound` (ARCHITECTURE Tier 3.1 Path C — the builtin `valueContains` dispatch is containment-sound, discharged through the PROVED `PlutusCore/Value/Algebra.lean` lemmas) and `:accum_lookup`. `P1_model` itself is **STATED, not proved** — Paths A/B and links L1.2-L1.6 are recorded as `Prop` definitions with per-item status in that file's OBLIGATION STATUS block. | **No UPLC K** (unchanged): the containment-carrying accepts cost 3,262 and 3,726 CEK steps; preps extrapolate to years (K-MEASUREMENTS §5.1/§5.2). Model-level positive witness + negative control: `WSC/Model/GlobalGoldens.lean` (`model_is_non_vacuous`, `model_matches_bytecode_containment_violation`). | Rests on **one** axiom, `globalModel_faithful` (whole-validator model↔bytecode equivalence; evidence, discharge route and residual risk in its docstring). **Two findings**: (a) ARCHITECTURE §3-P1's `mintPos` form is REFUTED for burns — the true (and the form §5.2's Preservation actually consumes) inequality is the SIGNED `out ≥ in + mintOf`; (b) `WSC/Honest.lean`'s `DirWF` omits the interval-PARTITION conjunct that ARCHITECTURE §5.3 describes, so "registered ⟹ no covering node" is NOT derivable from the axiom base and is carried as an explicit hypothesis (`coveringNodeExists … = false`). |

### Composition

| Item | State | Note |
|---|---|---|
| `WSC/Composition.lean` (invariant `I`, `Preservation`, chain induction, top claim) | **DEFERRED** — the file does not exist. | Blocked less by the leaves than by the missing ledger-level vocabulary: there is no `Ledger` type, so §5.3's `lr_utxo_semantics` and `ts_genesis` are deliberately NOT stated in `WSC/Honest.lean` (recorded there rather than invented). |
| `L-monotone` (registration is insert-only) | **ASSUMED** — `DirWF` conjunct (i). | Discharged by U10. |
| `L-mint-needs-reg` | **DEFERRED** | Would follow from P4 + `TS_MINTING_IDENTITY`. |

## 2. Axiom base (`WSC/Honest.lean`) — what is assumed

Grouped as ARCHITECTURE.md §5.3 does. **Read the numbering-collision table at
the top of `WSC/Honest.lean` before citing a name** — the file-local `TS1…TS5`
and `LR1…LR7` do not mean the same things as §5.3's.

| Group | Axioms | Discharged by |
|---|---|---|
| Modelling boundary | `OnChain`, `Deployed` | Never — they are the model/chain bridge. |
| TRUSTED-SETUP | `TS1` (params-anchor integrity), `TS2` (params-NFT uniqueness), `TS_MINTING_IDENTITY`, `mlhPolicyId` (abstract) | Deployment audit of the one-shot params anchor policy; U10 for the registration side. `TS_SCRIPT_HASH_BINDING` is **checked, not assumed** (E7, `WSC/flats/PROVENANCE.md`). |
| LEDGER-RULE (per-tx) | `LR1`–`LR7`, `LR_CTX` | Trusting the Cardano ledger; **every** conjunct is mapped to a cited ledger rule in `LR_CTX`'s audit table. The two conjuncts that were NOT justified (§3 D1/D2) were fixed in CLAB by task Z1, and `LR_CTX`'s `CLABMapOrderAgrees` side condition was deleted as unnecessary. |
| LEDGER-RULE (triggers) | `LR_MINT_RUNS_POLICY`, `LR_WDRL_RUNS_VALIDATOR`, `LR_SPEND_RUNS_VALIDATOR` | Trusting the Cardano ledger (UTXOW scripts-needed). |
| Non-negativity | `NONNEG` | Trusting the ledger; the ledger-WIDE form still has to be restated in `Composition.lean`. |
| Budget bridge | `LR_BUDGET_base` (K=600), `LR_BUDGET_minting` (K=900), `LR_BUDGET_global` (K=1600), `LR_BUDGET_seize` (**no K**) | A budget-monotonicity meta-theorem about `runSteps` that the substrate does not provide. Each is gated on an explicit non-vacuity hypothesis; only `BaseNonVacuous` is dischargeable today. |
| DIRECTORY | `DIRWF` (3 conjuncts), `TS3`, `TS4`, `TS5` | **U10** — `mkDirectoryNodeMP` at UPLC. Escape-critical. |
| NOT STATED (deliberately) | §5.3 `ts_genesis`, §5.3 `lr_utxo_semantics` | Need a `Ledger` type; belong in `Composition.lean`. Inventing them here would have been a wrong axiom. |
| NOT EXPRESSIBLE | §5.3 `lr_collateral_pubkey_only` | PlutusV3 `TxInfo` has no collateral field; the collateral exit route must be closed by a ledger-level argument outside this model. |

## 3. Defects found this session (task Y3); D1/D2 FIXED by task Z1

**D1 — ✅ FIXED (task Z1). Was: `validRedeemerMap` is REFUTED for every WSC
issuance transaction (top-priority substrate defect).** CLAB ordered
`ScriptPurpose` as
`Minting < Spending < Rewarding < Certifying < …`
(`CardanoLedgerApi/V3/Contexts.lean:20-27, 66-85`, the Plutus constructor order).
The Cardano ledger emits `txInfoRedeemers` in `ConwayPlutusPurpose AsIx` order —
`ConwaySpending < ConwayMinting < ConwayCertifying < ConwayRewarding < …`
(`cardano-ledger` @ `cd8b7fab8`,
`eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs:202-213`, derived `Ord`)
— and does **not** re-sort
(`transTxRedeemers = unsafeFromList ∘ mapM … ∘ Map.toList`,
`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, used for V3 at
`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:499,512`). Any transaction
carrying both a spending and a minting redeemer — i.e. every programmable-token
mint — is therefore NOT CLAB-sorted, so `validMintingContext` is false and any
P4/P4a/P2′ theorem is vacuous on exactly its target class. Independently
reproduced on the goldens: the 2 accepting minting goldens have redeemer
purposes `[Spending, Minting, Rewarding, Rewarding, Rewarding]` and
`validRedeemerMap = false`.

**FIX AS LANDED (Z1).** `ltScriptPurpose` in `CardanoLedgerApi/V3/Contexts.lean`
now uses the ledger order
`Spending < Minting < Certifying < Rewarding < Voting < Proposing`, with the
`cardano-ledger` citations in its docstring; the same defect in the V1/V2
`ltScriptPurpose` (`CardanoLedgerApi/V1/Contexts.lean`) was fixed to the
`AlonzoPlutusPurpose` order `Spending < Minting < Certifying < Rewarding`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Scripts.hs:308-313`; the Conway order
restricted to those four kinds is the same sequence, so it is era-robust). The
alternative — weakening `validRedeemerMap` to duplicate-freeness — was NOT taken:
the ledger order is a ledger fact, so correcting it keeps the precondition as
strong as reality permits. Effects, all machine-checked: both accepting minting
goldens now PASS `validRedeemerMap` (their only failing conjunct is the zero fee);
`WSC/Honest.lean` audit rows L and M are JUSTIFIED and its `CLABMapOrderAgrees`
quarantine on `LR_CTX` is DELETED; `WSC/Props/P4_Minting.lean`'s caveat theorem is
now `ctx_fails_validMintingContext_on_exactly_one_conjunct`. **`validMintingContext`
is satisfiable on P4's target class again, so the minting theorems are no longer
vacuous by construction** — what still blocks a verdict on P4a is the Z3 search
wall, not vacuity: re-measured post-fix at budget 900, both the vacuity probe and
the P4a obligation are still `Undetermined` at a 600 s Z3 cap (601 s wall each),
indistinguishable from the pre-fix runs.

**D2 — ✅ FIXED (task Z1). Was: `validWithdrawals` is REFUTED for withdrawal maps
mixing script and key credentials.** Ledger `Credential` Ord is `ScriptHashObj < KeyHashObj`
(`libs/cardano-ledger-core/src/Cardano/Ledger/Credential.hs:96-99`), CLAB's is
`PubKeyCredential < ScriptCredential` (`CardanoLedgerApi/V1/Credential.lean:61-66`),
and `transTxBodyWithdrawals` does not re-sort (`Conway/TxInfo.hs:544-546, 692-694`).
Narrower than D1: WSC's own withdrawals are all script credentials, where the two
orders agree. **FIX AS LANDED (Z1):** `ltCredential` in
`CardanoLedgerApi/V1/Credential.lean` now reads
`ScriptCredential < PubKeyCredential`, with the ledger citation and a note on the
`AccountAddress = (Network, Credential)` key (Plutus drops the network; harmless
because `validateWrongNetworkWithdrawal`,
`eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxo.hs:181,384`, admits one
network per transaction). As predicted, this changes NO golden verdict — every
golden withdrawal credential is a script credential — which confirms that the
seize goldens' `validWithdrawals` failure is a harness artifact (A2), not a CLAB
defect.

**D3 — no golden satisfies `validXContext`, so the golden suite cannot supply an
anti-vacuity witness.** All 13 golden contexts were CBOR-decoded into Lean and
every `validTxInfo` conjunct evaluated: all 13 have `txInfoFee = 0`, so
`txInfoFee > 0` (`Contexts.lean:1201`) fails. This is a builder artifact — the
goldens are produced by the repo's `ScriptContext.Builder`, not captured from a
chain (`WSC/goldens/MANIFEST.md`). Two further builder artifacts surfaced in the
same pass: the 3 seize goldens emit their two script withdrawal credentials
DESCENDING (`0x40…` before `0x14…`), and the 2 accepting seize goldens have a
residual output carrying **no ada entry at all**, which min-ada forbids on chain.
Consequence: the only `validXContext`-satisfying accepting witness in the library
is the hand-built `WSC.P3Witness.ctx`. **STILL OPEN after Z1** — D1/D2 were CLAB's
fault, D3 is the builder's: post-fix **8 of the 13 goldens fail on the fee ALONE**
(7 accepting — the base spend, all 3 global transfers and all 3 minting goldens —
plus `mint-local-empty-withdrawals-REJECT`), up from 6 before the fix, so a single
builder change (a positive fee with the balance adjusted) would turn each of them
into a genuine `validXContext` witness. Fix: give the golden builder a positive
fee, sorted withdrawals and min-ada on every output, then re-dump.

**D4 — CLAB does not assert the PV11 rule `txInfoInputs ∩ txInfoReferenceInputs = ∅`**
(`Conway/TxInfo.hs:492, 811-822`). This is a *missing* conjunct, i.e. the
precondition is weaker than reality, which strengthens the theorems — recorded,
not a problem.

**D5 — the substrate is not reproducible off this machine.** P5/P6/P1 need the
CIP-153 Value builtins, which live only on the **unpushed** PlutusCoreBlaster
branch `cip153-value-builtins` @ `9f9ca8c` (ADDENDUM E11). Until it is pushed and
the `lakefile.lean` pin changed to a full rev, any "proved against production
bytecode" claim for the global validator carries that caveat.

## 4. What would move the needle, in order

1. ✅ **DONE (task Z1)** — Fix D1/D2 in CLAB (small, mechanical): without it P4/P4a
   were vacuous on their target transaction class no matter what budget is used.
   Vacuity-by-precondition is gone; the remaining obstacle to P4a is the Z3 search
   wall (re-measured post-fix at budget 900, see §3 D1).
2. Land the minting prep at 900 and prove P4/P4a (cheapest new UPLC result:
   ~28 s of prep).
3. Land the global prep at 1,600 and prove P5 (the one newly-affordable global
   result: 36 min of prep, measured to complete).
4. Fix D3 so the golden suite can act as the anti-vacuity witness set.
5. **U10** — `mkDirectoryNodeMP` at UPLC, discharging `DirWF`. Highest assurance
   ROI: it is the only escape-critical assumption.
6. For P1 and P2, stop attempting fully-symbolic preps and decide between shaped
   contexts (with per-shape measured K — K-MEASUREMENTS §3 already lists the
   numbers) and the source-model route.

## 5. Reproduction of everything cited here

```
# the proof library (P3 green, probes Falsified as expected)
cd <CLAB checkout> && lake build WSC

# CEK step counts K of the 13 goldens (3.2 s)  -- WSC/goldens/K-MEASUREMENTS.md §6
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure   # git log -1 == 9f9ca8c
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# prep-cost wall (budget sweeps)  -- WSC/goldens/prep-probes/*.lean.disabled

# per-conjunct golden validXContext audit (§3 D1/D2/D3)
python3 WSC/goldens/ctx-audit/GenCtxAudit.py       && lake env lean CtxAudit.lean
python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py && lake env lean CtxAuditDetail.lean
```
