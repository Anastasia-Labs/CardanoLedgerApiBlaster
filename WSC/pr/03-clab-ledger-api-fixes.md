# SUBMISSION 2 — CardanoLedgerApiBlaster: two ledger-API bug fixes

**Repo** `input-output-hk/CardanoLedgerApiBlaster` · **new branch cut from `main`**
(`5dab3c43f042b8735b6d067223baaa8d32ed28a1`) — **not** `wsc-containment-proofs`
· **3 files, +686/−19**, all under `CardanoLedgerApi/`

Two independent defects, each verified against `cardano-ledger` source, each small and
independently valuable. Part 1 is the PR description. Part 2 is how to cut the branch
and what must be written first.

---
---

# PART 1 — PR DESCRIPTION (submit this)

## Summary

Two fixes to the PlutusV1/V2/V3 ledger-context predicates, both found by formalising
real transaction contexts and discovering that the predicates rejected transactions the
node emits.

1. **`ScriptPurpose` and `Credential` were compared in the *Plutus* declaration order,
   not the *ledger's* order.** Because `TxInfo`'s maps reach a script unsorted-by-Plutus
   — the ledger hands over `Map.toList` output and never re-sorts — the sortedness
   checks in `validScriptContext` rejected real transactions. The most damaging instance:
   **every transaction carrying both a spending and a minting redeemer was rejected**, so
   `validMintingContext` was *unsatisfiable* and every
   `validMintingContext ctx → … → POST` theorem was vacuously true on exactly the class
   it is meant to constrain.
2. **The Conway `hasExactSetOfRedeemers` rule was missing.** `TxInfo` carries enough
   information to transcribe `scriptsNeeded` and to state both halves of the rule
   (`MissingRedeemers` and `ExtraRedeemers`); it did not exist. This adds it — in the
   honest form, with the one thing `TxInfo` provably cannot express separated out and
   both error directions stated as theorems rather than comments.

All ledger citations are against `cardano-ledger` at `cd8b7fab8` (Conway era) and were
read from source.

---

## Fix 1 — the map orders (`CardanoLedgerApi/V1/Contexts.lean`, `V1/Credential.lean`, `V3/Contexts.lean`)

### `ScriptPurpose`

The ledger builds `txInfoRedeemers` as `unsafeFromList ∘ map … ∘ Map.toList` over a map
keyed by `PlutusPurpose AsIx`, with **no re-sorting**
(`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, used for V3 at
`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:499,512`). The derived `Ord` on
`ConwayPlutusPurpose` (`eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs:202-213`)
is therefore what a script sees:

```
Spending  <  Minting  <  Certifying  <  Rewarding  <  Voting  <  Proposing
```

CLAB's `ltScriptPurpose` used the Plutus *declaration* order, which puts `Minting` first.
Fixed in V3.

The same defect exists for V1/V2, where the relevant order is
`AlonzoPlutusPurpose`'s derived `Ord`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Scripts.hs:308-313`):

```
AlonzoSpending  <  AlonzoMinting  <  AlonzoCertifying  <  AlonzoRewarding
```

`PlutusPurpose f BabbageEra = AlonzoPlutusPurpose f BabbageEra`
(`eras/babbage/impl/src/Cardano/Ledger/Babbage/Scripts.hs:61`). The Conway order
restricted to those four kinds is the **same sequence**, so the V1/V2 fix is unambiguous
across eras. Fixed in V1.

### `Credential`

```haskell
data Credential (kr :: KeyRole) = ScriptHashObj !ScriptHash | KeyHashObj !(KeyHash kr)
  deriving (Show, Eq, Generic, Ord)
```
(`libs/cardano-ledger-core/src/Cardano/Ledger/Credential.hs:96-99`) — so the ledger's
derived order is **`ScriptHashObj < KeyHashObj`**, the opposite of Plutus's
`PubKeyCredential | ScriptCredential` declaration order that `ltCredential` used.

Credential-keyed maps reach `TxInfo` unsorted for the same reason:
`txInfoWdrl = transMap transAccountAddress transCoinToLovelace (unWithdrawals …)` with
`transMap = PV3.unsafeFromList . map … . Map.toList`
(`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:544-546, 692-694`). So
`validWithdrawals` must use the ledger order or it rejects any real withdrawal map that
mixes script and key credentials.

One side fact, needed and documented in-code: the ledger's withdrawal key is
`AccountAddress = (Network, AccountId Credential)`
(`libs/cardano-ledger-core/src/Cardano/Ledger/Address.hs:183-191`) and Plutus drops the
`Network` component. That is harmless because `validateWrongNetworkWithdrawal`
(`eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxo.hs:181, 384`) forces a single
network per transaction, on which `(Network, Credential)` order restricts to `Credential`
order.

### Why correct the orders rather than weaken the predicates

The alternative was to relax the sortedness conjuncts to plain duplicate-freeness. The
orders are **ledger facts**, so correcting them keeps the precondition as strong as
reality permits and needs no apology. No other conjunct is touched; the only structural
change is the direction of two comparisons, and **every `lt`/irreflexivity/decidability
proof in the repository survived unchanged**.

---

## Fix 2 — the Conway exact-redeemer rule (`CardanoLedgerApi/V3/Contexts.lean`)

The rule is `hasExactSetOfRedeemers`
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`): compute
`redeemersNeeded` from `scriptsNeeded`, then require the redeemer map's key set to equal
it **exactly** — failures are `MissingRedeemers` and `ExtraRedeemers`.

### What is added

**The `scriptsNeeded` transcription**, per purpose kind, in `TxInfo` vocabulary:

| definition | what it collects |
|---|---|
| `credScriptHash` | the script hash a credential refers to, if any |
| `txCertScriptWitness` | `getScriptWitnessConwayTxCert` |
| `voterScriptWitness` | `getVoterScriptHash` |
| `proposalScriptWitness` | `getProposalScriptHash` |
| `spendingPurposesWitnessed` | one `Spending` per script-addressed input |
| `rewardingPurposesWitnessed` | one `Rewarding` per script-credential withdrawal |
| `mintingPurposesWitnessed` | one `Minting` per policy id in the mint field |
| `certifyingPurposesWitnessed{,From}` | `Certifying`, indexed by position in the **full** certificate list |
| `votingPurposesWitnessed` | one `Voting` per script-credential voter |
| `proposingPurposesWitnessed{,From}` | `Proposing`, indexed by position in the full proposal list |
| `scriptPurposesWitnessed` | the six-way concatenation |

**The rule, in the form `TxInfo` can express:**

* `coveredBy` — every purpose in a list has a redeemer entry;
* `redeemerCoverageAllPlutus` — `MissingRedeemers`;
* `noExtraRedeemersAllPlutus` — `ExtraRedeemers`;
* `redeemersExactAllPlutus` — both halves;
* `redeemerCoverageAllPlutusOf` — the same at a `ScriptContext`.

**The faithful rule, relative to a language oracle**, plus consequence lemmas the
sortedness/coverage proofs need (`isSome_findRedeemer_of_mem_coveredBy`,
`mem_scriptPurposesWitnessed_of_{spending,rewarding}`,
`findRedeemer_{rewarding,spending}_*_of_coverageAllPlutus`, …):

* `coveredByNonNative`, `redeemerCoverageModNative`, `noExtraRedeemersModNative`,
  each parameterised by `isNativeAt : ScriptPurpose → Bool`.

### The honest part: why the names say `AllPlutus`

The ledger's `redeemersNeeded` keeps a needed `(purpose, hash)` pair only if
`Map.lookup hash scriptsProvided` succeeds **and** the script found there satisfies
`not (isNativeScript script)`
(`Alonzo/Rules/Utxow.hs:245-262`; `isNativeScript = isJust . getNativeScript`,
`libs/cardano-ledger-core/src/Cardano/Ledger/Core.hs:586-587`). Of those two filters:

* the **`scriptsProvided`** filter is a **no-op** on any transaction that reaches the
  rule — `babbageMissingScripts`
  (`eras/babbage/impl/src/Cardano/Ledger/Babbage/Rules/Utxow.hs:191-206`, run at `:344`,
  seven lines before `hasExactSetOfRedeemers` at `:351`) already rejects unless every
  needed hash is provided, so the lookup always succeeds. Dropping it costs nothing.
* the **`isNativeScript`** filter is **not recoverable from `TxInfo`**. Every needed
  script *hash* is derivable, but `isNativeScript` is a predicate on a script **body**,
  and `TxInfo` carries no script bodies and no language tags — its only script-shaped
  field is `V2.TxOut.txOutReferenceScript : Option ScriptHash`
  (`CardanoLedgerApi/V2/Tx.lean:78-83`), a bare `ByteString`
  (`V1/Scripts.lean:15-16`), and the witness script set has no `TxInfo` field at all.
  **The missing information is exactly one bit per needed script, and `TxInfo` does not
  contain it.**

So the predicates this PR can offer unconditionally are the **all-Plutus specialisation**
of the rule, and they are named for it rather than for the rule. **Both directions of
the discrepancy are theorems in this PR, not comments** — all at `[propext, Quot.sound]`,
no axioms, no `sorry`:

| theorem | says |
|---|---|
| `coveredByNonNative_allPlutus` | `coveredBy` **is** the all-Plutus instance of the faithful predicate |
| `redeemerCoverageModNative_allPlutus` | so is `redeemerCoverageAllPlutus` |
| `coveredByNonNative_of_coveredBy`, `redeemerCoverageModNative_of_allPlutus` | **positive**: ours implies the true rule for **every** language assignment — i.e. it is safe to *assume* |
| `coveredByNonNative_strictly_weaker` | **negative, by counterexample**: the converse fails, so it is not safe to *refute* with |
| `noExtra_not_conservative` | **negative, by counterexample**: `noExtraRedeemersAllPlutus` is *not* conservative in the other direction |

Read plainly: **`redeemerCoverageAllPlutus` is too strong to use negatively and exactly
right to use positively; `noExtraRedeemersAllPlutus` is the mirror.** Anyone who wants
the faithful rule can instantiate `…ModNative` with a real language oracle. That is the
best a V3 `TxInfo` admits, and the types now say so.

## Evidence

* **Fix 1, before/after on real transaction contexts** (13 exported production
  transaction contexts, decoded and checked against `validScriptContext`): two
  contexts carrying both a spending and a minting redeemer went from
  `["txInfoFee > 0", "validRedeemerMap"]` failing to `["txInfoFee > 0"]` — i.e. the
  order violation is gone and only an unrelated harness artefact (a zero fee) remains.
  The other eleven are unchanged. `validRedeemerMap` now fails in 3 contexts rather than
  5, and every remaining violation is **inside one purpose kind**, which is a different
  and separately-diagnosed harness defect.
* **Fix 1, the `Credential` half, changes no verdict** on those contexts — every
  withdrawal credential in them is a *script* credential, the case where old and new
  orders agree. That is the right control: it confirms the remaining failures are not
  attributable to this change.
* **Fix 2, differential against the real node**: the rule reproduces the node's own
  answer on 13/13 exported contexts —
  `#redeemers = #script-inputs + #mint-policies + #script-withdrawals` exactly, with the
  purpose multiset matching. All 13 satisfy `redeemerCoverageAllPlutus`; all 9 accepting
  ones satisfy `redeemersExactAllPlutus`; and 5 contexts built before the harness was
  fixed all fail `redeemerCoverageAllPlutus`. **The rule is checked in both directions.**
* `lake build CardanoLedgerApi` green.

## Caveats

* The two defects were found by a downstream Lean formalization of these contexts, which
  is **not part of this PR** and is not public yet. The differential evidence above was
  produced there; the tests in this PR are self-contained restatements of it (see
  `Tests/…`). Nothing in this PR references that work by path.
* Fix 1 removes vacuity; it does **not** make the affected minting-purpose obligations
  easier to *discharge*. Measured downstream: an SMT obligation that was `Undetermined`
  before the fix is still `Undetermined` after it, at the same wall clock. The upside is
  narrower and worth stating precisely: **no earlier `Undetermined` in that area was a
  disguised vacuity artefact.**
* `noExtraRedeemersModNative` is stated with `List.all`/`List.any` rather than this
  repository's `Recursor.all`/`Recursor.any`, so it is **not** proved defeq to
  `noExtraRedeemersAllPlutus`; its discrepancy is witnessed by the standalone
  counterexample `noExtra_not_conservative` instead. If you would rather it be stated on
  `Recursor.*` and related by `rfl`, that is a reasonable ask.
* Pre-existing and untouched: the `Recursor.all` macro emits a `panic!` surfaced as an
  `info:` diagnostic with a C++ backtrace (`invalid Name.append, both arguments have
  macro scopes`) at each of the new `noExtraRedeemersAllPlutus`-style definitions. The
  definitions elaborate and the build exits 0. It reproduces at the same macro on `main`,
  so it is not introduced here — but this PR adds definitions that trip it, so the number
  of such lines in the build log goes up. Worth fixing separately in `Recursor`.

---
---

# PART 2 — HOW TO CUT THIS BRANCH, AND WHAT MUST BE WRITTEN FIRST (do not submit)

## 2.1 Do not submit `wsc-containment-proofs`

That branch carries 137 Lean modules of application-specific proof, an absolute-path
`require`, a rewritten `lake-manifest.json`, `WSC.lean`, and `.gitignore` entries for a
local build helper. **None of that belongs in this PR and all of it is a hard blocker**
(`00-PLAN.md` §4.0).

Cut a fresh branch and take **only** the three files under `CardanoLedgerApi/`:

```bash
git checkout -b fix/ledger-map-order-and-exact-redeemers main
git checkout wsc-containment-proofs -- \
    CardanoLedgerApi/V1/Contexts.lean \
    CardanoLedgerApi/V1/Credential.lean \
    CardanoLedgerApi/V3/Contexts.lean
```

Then verify **nothing else came along**:

```bash
git status --porcelain            # expect exactly those three paths
git diff --stat --cached main     # expect 3 files, +686/-19
git grep -n '/home/gumbo\|/tmp/claude'   # expect NOTHING
git grep -n 'WSC/'  -- CardanoLedgerApi  # expect NOTHING — see 2.2
```

## 2.2 The three files currently reference `WSC/` paths — those must be scrubbed

Measured: `grep -n WSC` over the three files returns **12 lines**, of two kinds.

*Dangling file paths* (4) — must be rewritten to state the fact instead of the pointer:

| line | reference |
|---|---|
| `V1/Contexts.lean:142` | `defect D1 (WSC/LR-CTX-AUDIT.md row M)` |
| `V1/Credential.lean:77` | `defect D2; see WSC/LR-CTX-AUDIT.md row L` |
| `V3/Contexts.lean:86` | `WSC/LR-CTX-AUDIT.md row M` |
| `V3/Contexts.lean:1230` | `WSC/Honest.lean row S / LR_REDEEMER_COVERAGE` |
| `V3/Contexts.lean:1565, 1578` | `WSC/Props/Shaped/…` module paths |

*Application-specific narrative* (6) — `V3/Contexts.lean:1212, 1223, 1393, 1400, 1557,
1608`: "the WSC deployment", "every WSC witness", "the consequence the WSC realizability
proofs need". These are not dangling, but they name a consumer the maintainer has never
heard of, in the *docstrings of a general-purpose library*. Rewrite to
consumer-neutral wording ("a caller whose witness is all-Plutus", "the consequence a
realizability proof needs"). Keep **every** `cardano-ledger` citation verbatim — those
are the valuable part.

## 2.3 THE REAL WORK ITEM — this PR has no tests, and it needs them

Verified in this task: `git grep` finds **no** reference to `ltCredential`,
`ltScriptPurpose`, `redeemerCoverageAllPlutus` or `redeemersExactAllPlutus` anywhere
under `Tests/`. **Every piece of empirical evidence quoted in Part 1 lives in the
downstream proof library** — the 13/13 differential is
`WSC/Goldens/Audit.lean::every_golden_is_redeemer_covered`, the both-directions check is
`RealizableShapes.all_recut_witnesses_redeemersExact` and
`all_old_witnesses_fail_c3_coverage`. None of it can ship in this PR.

A reviewer will, correctly, not merge a 686-line change to the core context predicates
on the strength of prose. **Write `Tests/Contexts/LedgerOrder.lean` and
`Tests/Contexts/ExactRedeemers.lean` before opening.** Minimum content, all
`native_decide` on small literal values — no solver, no fixtures:

1. **the two order flips, directly**: `ltCredential (.ScriptCredential "aa")
   (.PubKeyCredential "00") = true`, and the four/six-kind `ScriptPurpose` chain in both
   V1 and V3;
2. **the fix's point**: one literal `Withdrawals` mixing a script and a key credential
   that `validWithdrawals` now accepts and previously rejected (state the old verdict in
   a comment — the old function is gone, so this is a comment, not a theorem);
3. **the vacuity that was fixed**: one literal `TxInfo` carrying a spending *and* a
   minting redeemer, in ledger order, that now satisfies `validRedeemerMap`;
4. **the redeemer rule, positively**: two or three literal `TxInfo`s with
   `redeemersExactAllPlutus = true`, covering the spending / minting / rewarding arms;
5. **the redeemer rule, negatively**: one missing redeemer (`redeemerCoverageAllPlutus =
   false`) and one extra (`noExtraRedeemersAllPlutus = false`);
6. **the two negative-direction theorems re-exported** — `coveredByNonNative_strictly_weaker`
   and `noExtra_not_conservative` are already theorems in `V3/Contexts.lean`; a one-line
   `#print axioms` or `example` in the test file makes them visible to a reviewer reading
   `Tests/` rather than the 1,500-line context module.

Estimate: **2–4 hours**, mostly constructing literal `TxInfo` values. This is the gating
item for submission 2 and it is not optional.

## 2.4 Commit structure

Two commits, one per defect. Do **not** replay the four upstream commits
(`d853256`, `755d75e`, part of `1f6c760`, part of `9e5d417`) — three of them touch
`lakefile.lean` or the downstream library, and one of them *renames* predicates that
this PR introduces already-named. Squash to:

1. `fix: compare ScriptPurpose and Credential in the ledger's order, not Plutus's`
   — V1/Contexts, V1/Credential, V3/Contexts (the order part), + `Tests/Contexts/LedgerOrder.lean`
2. `feat: the Conway exact-redeemer rule (MissingRedeemers / ExtraRedeemers)`
   — V3/Contexts (the rule part), + `Tests/Contexts/ExactRedeemers.lean`

Commit 1 is a **behaviour change** to existing predicates and commit 2 is **additive**.
Keeping them apart lets a maintainer merge 1 fast and take longer over 2.

## 2.5 Checklist before opening

- [ ] fresh branch from `main`; only the three `CardanoLedgerApi/` files
- [ ] all `WSC/` cross-references in those files rewritten to state the fact (§2.2)
- [ ] `git grep '/home/gumbo\|/tmp/claude'` → nothing
- [ ] `Tests/Contexts/LedgerOrder.lean` and `Tests/Contexts/ExactRedeemers.lean` written (§2.3)
- [ ] `lake build && lake build Tests` green from a clean `.lake`
- [ ] `git diff --stat main` → 5 files (3 + 2 new tests)
- [ ] body = Part 1, with the `Tests/…` names filled into the first Caveat
