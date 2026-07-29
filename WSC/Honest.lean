-- ⚠️ PRE-#112 (PARTIAL): part of this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Read WSC/IMPACT-PR112.md for the split before quoting anything here.
/-
WSC/Honest.lean — the honest-deployment vocabulary (arch §4.2) and the FULL
assumption base of the WSC containment campaign.

Every axiom is a SIGNATURE ONLY (no proof obligations discharged here); each
carries a plain-English doc comment, a statement of WHY it is unavoidable, and
an audit note naming the real-world audit or future proof that discharges it.
There is no `sorry` anywhere in this library — every stub is either an axiom or
a complete definition.

## Layout (ARCHITECTURE.md §5.3 grouping)

* `§TS` TRUSTED-SETUP — one-time deployment audit of components OUTSIDE the four
  imported validators.
* `§LR` LEDGER-RULE — facts guaranteed by Cardano ledger rules about every real
  invocation.
* `§Dir` DIRECTORY — directory-linked-list well-formedness (`DirWF`, ADDENDUM
  E4). Escape-critical; U10 (`mkDirectoryNodeMP` at UPLC) is what discharges it.

## NUMBERING COLLISION (read this before citing an axiom name)

The names `TS1…TS5` and `LR1…LR7` in THIS FILE do **not** mean the same things
as `TS1…TS5` / `LR1…LR7` in ARCHITECTURE.md §5.3. The collision is historical
and is recorded rather than silently "fixed", because P3_Base.lean, the goldens
docs and K-MEASUREMENTS.md already cite the file-local names. Mapping:

| §5.3 name | this file | note |
|---|---|---|
| TS1 `ts_params_authentic` | `TS1` | same fact |
| TS2 `ts_script_hash_binding` | *not an axiom* — see `TS_SCRIPT_HASH_BINDING` note | CHECKED (E7, `WSC/flats/PROVENANCE.md`), not assumed |
| TS3 `ts_genesis` | **absent** — belongs in `Composition.lean` | needs a `Ledger` type that does not exist yet; deliberately NOT invented here |
| TS4 `ts_minting_identity` | `TS_MINTING_IDENTITY` | added by this task |
| TS5 `ts_singleton_config` | `TS2` (params-NFT uniqueness) + `TS5` (directory-NFT custody) | split |
| — | `TS3`, `TS4`, `TS5` | DIRECTORY facts; filed under §Dir below, NOT trusted-setup |
| LR1 `lr_mint_runs_policy` | `LR_MINT_RUNS_POLICY` | added by this task |
| LR2 `lr_withdrawal_runs_validator` | `LR_WDRL_RUNS_VALIDATOR` | added by this task |
| LR3 `lr_spend_runs_validator` | `LR_SPEND_RUNS_VALIDATOR` | added by this task |
| LR4 `lr_value_conservation` | `LR7` (per-tx `isBalanced`) | chain-step form belongs in `Composition.lean` |
| LR5 `lr_utxo_semantics` | **absent** — belongs in `Composition.lean` | needs a `Ledger` type; NOT invented here |
| LR6 `lr_scriptcontext_faithful` | `LR_CTX` + `OnChain` | `OnChain` IS the faithfulness bridge |
| LR7 `lr_collateral_pubkey_only` | **NOT EXPRESSIBLE** | PlutusV3 `TxInfo` has no collateral field (see `V3/Contexts.lean` `TxInfo`); the collateral exit route must be closed by a ledger-level argument outside this model |
| DirWF `directory_partition` | `DirWF` / `DIRWF` | three conjuncts per ADDENDUM E4 |
| LR1…LR7 (this file) | per-tx `valid*` conjuncts | consequences of `LR_CTX`; kept named so each proof cites exactly the rule it needs |

## CORRECTION LOG (task Y3, 2026-07-25)

1. `LR_BUDGET_*` restated: the bound is on **CEK STEPS** (not `txSize`, which was
   a proxy with no proven relation to step count) and the constants are
   PUBLISHED per-validator `def`s (ADDENDUM E1 requires published constants; the
   old `∃ K` form was unauditable). `def txSize` deleted — it had no other user.
2. Stale budget docstrings ("budget 2000" / "budget 9000") removed; the
   authoritative budgets live in `WSC/Prep/*.lean` and are referenced, never
   duplicated, from here.
3. `LR_CTX` (E5) stated with the clause-by-clause AUDIT TABLE. It was once
   **weakened** by a `CLABMapOrderAgrees` side condition, because two of
   `validScriptContext`'s conjuncts (rows L, M) were not entailed by any ledger
   rule — CLAB compared `ScriptPurpose`s and `Credential`s in the PLUTUS
   constructor order, not the ledger's. That was CLAB defect D1/D2 and task Z1
   **fixed it at the source**, so rows L and M are now JUSTIFIED and the side
   condition has been DELETED (see `LR_CTX`'s docstring for the full record).
   `LR4`/`LR5` remain in the weakened, justified-core form: it is all the proofs
   need, and a weaker axiom is a smaller trust surface.
4. `NONNEG` (E6) restated as non-negativity of held amounts (`0 ≤ valueOf …`),
   the form the Preservation reduction consumes, instead of re-asserting
   `validTxOutValue` (which duplicated LR1/LR2).
5. `DirWF` given all three ADDENDUM-E4 conjuncts, quantified over inputs,
   reference inputs AND outputs (was: reference inputs only), with the NFT-name
   binding stated as "exactly one directory token, named `key`".
6. Added the missing §5.3 ledger-trigger axioms and `TS_MINTING_IDENTITY`;
   recorded the three §5.3 items that are deliberately NOT stated here.

## CORRECTION LOG (task V4, 2026-07-25)

7. `DirWF` gained its FOURTH conjunct, `(iv) dirNoOverlap … (dirPreState ctx)` —
   the interval-partition property of ARCHITECTURE.md §5.3's
   `directory_partition` / ADDENDUM E4, whose absence was reported (not patched)
   by `WSC/Props/P1_Transfer.lean`'s `DirWF_partition_conjunct_missing`. With it,
   `covering_node_excludes_registration` (ADDENDUM E3's required bridge) is a
   **THEOREM** in this file rather than a missing link, and the
   `coveringNodeExists … = false` hypothesis P1/P6 carry explicitly becomes
   derivable from "`cs` is registered". FINDING recorded in `dirPreState`'s
   docstring: the conjunct must be stated over the PRE-STATE snapshot (refs +
   spent inputs); over `dirCandidates` (which includes outputs) it would be FALSE
   for every directory insert. Escape-critical; same discharge (U10).
   Ledger-level counterpart: `DIRWF_L` in `WSC/Composition.lean`.

## CORRECTION LOG (task A1, 2026-07-25)

8. **The four `LR_BUDGET_*` axioms are restated against `Runs.XRun K`**
   (`WSC/Runs.lean`) instead of `appliedX_K.prop`. This is audit finding **F3**'s
   repair and task U1's own top recommendation; the full rationale, the four
   consequences and — importantly — the four things that did NOT change are in the
   §LR-BUDGET RESTATEMENT block below. Read that block before citing any of them.
9. **`GlobalPreppedAt` DELETED** (it was U2's abstract "this term really is the
   prep of that flat at that budget" side condition; a `Runs.XRun K` right-hand
   side makes it vacuous). This file's `axiom` count goes **38 → 37** and the
   library's **51 → 50** (`grep -c '^axiom ' WSC/**/*.lean`).
   MEASUREMENT NOTE, reported not silently corrected: `WSC/AUDIT.md` §2 publishes
   "47 `axiom` declarations … `WSC/Honest.lean` (35) … `P1_Transfer.lean` (1)". At
   the audited revision `grep -c '^axiom '` gives 51 / 38 / 2. The audit's split by
   FILE and its conclusion ("no `axiom` hides in any `Prep/*`, `Shaped/*` or
   `Props/Shaped/*` module") both reproduce; only the totals are 4 low.
10. **All four `*NonVacuous` predicates restated on `Runs.XRun K` and made
    `K`-parametric, and ALL of them are now DISCHARGED as theorems** at every
    published budget — including `GlobalNonVacuous` (audit **F7**) and
    `SeizeNonVacuous`, which the previous revision recorded as unreachable at any
    affordable budget. Nothing in this file's non-vacuity set is open.
11. **Three new published constants**: `K_mint_custody = 2500`,
    `K_global_member = 3300`, `K_seize = 3800`, each ≥ the measured accepting step
    count of a named in-library witness. `K_seize` reverses a "DELIBERATELY
    UNAVAILABLE" entry; the reasoning that made it unavailable was about
    `#prep_uplc` cost and does not apply to a run term. Both halves are recorded
    at the constant.
12. Prep-cost figures quoted in this file's docstrings were RE-MEASURED under
    `lake build` (audit **F5**): base 1.35 s, minting@900 1.53 s,
    global@1600 37.8 s — against 11 s / 27.6 s / 2,143 s as published. Never quote
    K-MEASUREMENTS §5.1's original table.

RECONSTRUCTION FLAG (retained from the previous revision): the binding
`arch-final.md` was not available when the axiom STATEMENTS were first drafted.
`WSC/ARCHITECTURE.md` (base document + ADDENDUM v3, canonical on
`wsc-containment-proofs`) is now the reference used by this revision, and the
E1/E4/E5/E6 allocations below were re-read from it verbatim.
-/
import CardanoLedgerApi.V3
import WSC.Imports
import WSC.Runs
import WSC.Redeemer
import WSC.Spec

namespace WSC

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo ScriptPurpose TxInInfo TxOut
                          ScriptHash
                          hasCurrencySymbol valueOf validTxOutValue
                          credentialInWithdrawals isBalanced
                          validInputs validOutputs validScriptInfo
                          validScriptContext validRewardingContext
                          validMintingContext validSpendingContext)
open CardanoLedgerApi.V3.Contexts (validMintValue validWithdrawals validRedeemerMap
                          findRedeemer redeemerCoverageAllPlutus noExtraRedeemersAllPlutus redeemersExactAllPlutus
                          findRedeemer_rewarding_ne_none_of_coverageAllPlutus
                          findRedeemer_spending_ne_none_of_coverageAllPlutus)
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
Ada first — LR2/`validTxOutValue`) and directory-NFT custody (TS5) the two
coincide for directory UTxOs; the ground-truth definition here is membership,
and the equivalence is discharged in the proof tasks, not assumed. -/
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

/-- The token map that policy `cs` carries inside a Data-level value, if any.
Ground-truth helper: used to say "EXACTLY ONE directory state token, named
`key`" without appealing to any validator internals. -/
def csTokens (cs : CurrencySymbol) : Value → Option (List (Data × Data))
  | [] => none
  | (Data.B cs', Data.Map m) :: rest => if cs' == cs then some m else csTokens cs rest
  | _ :: rest => csTokens cs rest

/-- Policy `cs` is REGISTERED in the directory view visible to a transaction:
some reference input resolves to an authentic directory node whose datum key
is `cs`.

AUDIT NOTE (P5 caveat, binding — ADDENDUM E3): P5's postcondition must use the
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

/-- Every `TxOut` a transaction lets us see: resolved reference inputs, resolved
spent inputs, and produced outputs. `DirWF` quantifies over this list, because
ADDENDUM E4(iii) is about ANY UTxO carrying a genuine directory token, not only
the ones referenced. -/
def dirCandidates (ctx : ScriptContext) : List TxOut :=
  (ctx.scriptContextTxInfo.txInfoReferenceInputs.map (·.txInInfoResolved)) ++
  (ctx.scriptContextTxInfo.txInfoInputs.map (·.txInInfoResolved)) ++
  ctx.scriptContextTxInfo.txInfoOutputs

/-! ## Modelling predicates (declared, never defined — the trust boundary) -/

/-- `OnChain ctx`: the script context arises from a REAL Cardano mainnet
transaction that reached phase-2 validation (i.e. was produced by the ledger,
not synthesised). All LR-axioms condition on this.

WHY UNAVOIDABLE: it is the bridge between the model and the chain — the
proposition "this Lean value is what the node actually built". It also carries
ARCHITECTURE.md §5.3's `lr_scriptcontext_faithful` (LR6 there): the fields of
`ctx` faithfully reflect the transaction's inputs/refs/outputs/mint/wdrl.
Declared abstract; it is never discharged in Lean. AUDIT: the golden vectors
(`WSC/goldens/`) are the empirical stand-in — and note they are NOT captured
from a running chain (MANIFEST.md "Extraction provenance"), so they corroborate
shape, not `OnChain`. -/
axiom OnChain : ScriptContext → Prop

/-- `Deployed hp`: `hp` are the parameters of the audited production
deployment (protocol-params NFT minted by the hardened anchor policy, §4.1;
directory/base/global/seize credentials as published). All TS-axioms condition
on this.

WHY UNAVOIDABLE: "which deployment" is an extra-logical fact about the chain.
AUDIT: the deployment audit checklist — one-shot params mint, published
credentials, flat-hash equality (E7, `WSC/flats/PROVENANCE.md`). -/
axiom Deployed : HonestParams → Prop

/-! # §TS — TRUSTED-SETUP axioms

Facts about protocol components OUTSIDE the four imported validators (the
protocol-params anchor policy, the token-specific minting-logic scripts).
Highest-value follow-on: discharge them by UPLC-level proofs over those
scripts. -/

/-- **TS1 (params-anchor integrity)** = §5.3 `ts_params_authentic`. *Any
reference input of an on-chain transaction whose value carries the deployed
protocol-params state token really does carry the honest params datum.*

WHY UNAVOIDABLE: the four validators read every credential they trust
(base/global/seize/directory) out of this datum; nothing in the four validators
constrains what that datum says. It is the anchor policy's job.

AUDIT / DISCHARGE: audit the hardened one-shot anchor policy (§4.1) — NFT is
unique and its datum is immutable and well-formed. A UPLC formalization of that
policy would discharge this.

MINIMALITY NOTE: the validators additionally authenticate the params UTxO
positionally via `pparamsAtRefIdx`/`phasCSH` (ProgrammableLogicBase.hs:824-838),
so a wrong index fails on its own; TS1 therefore only needs to pin the datum
carried by the already-authenticated UTxO. -/
axiom TS1 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      hasCurrencySymbol hp.protocolParamsCS t.txInInfoResolved.txOutValue →
      paramsDatum t.txInInfoResolved = some hp.datum

/-- **TS2 (params-NFT uniqueness)** ⊂ §5.3 `ts_singleton_config`. *At most one
reference input of an on-chain transaction carries the deployed
protocol-params state token.*

WHY UNAVOIDABLE: without it a transaction could show two params UTxOs and
different validators in the same transaction could read different configs
(shadow config). Delegates to the anchor policy's one-shot mint.

AUDIT / DISCHARGE: same as TS1 (one-shot mint ⟹ global uniqueness ⟹ per-tx
uniqueness). -/
axiom TS2 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t₁ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
    ∀ t₂ ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      hasCurrencySymbol hp.protocolParamsCS t₁.txInInfoResolved.txOutValue →
      hasCurrencySymbol hp.protocolParamsCS t₂.txInInfoResolved.txOutValue →
      t₁ = t₂

/-- The policy id of the `programmableTokenMinting` instance at
`(protocolParamsCS, mintingLogicHash)`. Abstract: it is the blake2b-224 hash of
the applied UPLC script, which this model does not compute.

AUDIT NOTE: this is deliberately abstract rather than wrong. Making it concrete
requires script-hashing inside Lean (`ScriptEncoding` + blake2b), which is the
same machinery E7's flat-provenance gate performs OUT of band. -/
axiom mlhPolicyId : CurrencySymbol → ScriptHash → CurrencySymbol

/-- **TS_MINTING_IDENTITY** = §5.3 `ts_minting_identity`. *Every registered
programmable policy id `cs` is the script hash of a
`mkProgrammableLogicMinting` instance parameterized by the deployed
`protocolParamsCS` and some token-specific minting-logic hash.*

WHY UNAVOIDABLE: it is what ties the abstract set of "registered policies" to
the real policy scripts the ledger runs. Without it, `LR_MINT_RUNS_POLICY`
("the ledger ran *some* script for `cs`") cannot be upgraded to "the ledger ran
*our issuance policy* for `cs`", and P4 could not be instantiated at all.

AUDIT / DISCHARGE: deployment audit — the directory insert path only ever
registers policy ids derived from the issuance policy (a `mkDirectoryNodeMP`
UPLC proof, U10, is the natural discharge). Stated as an implication so that a
FORGED directory entry stays inside the theorem's universe rather than being
excluded by fiat. -/
axiom TS_MINTING_IDENTITY :
  ∀ (hp : HonestParams) (ctx : ScriptContext) (cs : CurrencySymbol),
    Deployed hp → OnChain ctx →
    IsRegistered hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoReferenceInputs cs →
    ∃ mlh : ScriptHash, cs = mlhPolicyId hp.protocolParamsCS mlh

/-! ### TS_SCRIPT_HASH_BINDING (§5.3 TS2) — CHECKED, NOT ASSUMED

ADDENDUM E7 makes the flat-provenance gate a *check*: each imported
`WSC/flats/*.flat` is sha256-recorded and its script hash compared against the
deployment suite's export (`WSC/flats/PROVENANCE.md`;
`WSC/goldens/MANIFEST.md` re-verifies byte-identity against
`generated/scripts/unapplied/prod/*.json` at wsc-poc
`97160f894a8e1d3194ef9bec309094f762497c77`). It is therefore deliberately NOT
an axiom in this file. If that check ever lapses, this comment — not a Lean
`axiom` — is what has to change. -/

/-! # §LR — LEDGER-RULE axioms

Facts guaranteed by Cardano ledger rules (phase-1 validation and script-context
construction) about every REAL script invocation. CLAB encodes them as the
`valid*` Boolean predicates (`[LEDGER-RULE]` docs in
`CardanoLedgerApi/V3/Contexts.lean`); the axioms assert that on-chain contexts
satisfy them.

Ledger source of truth used for the citations below is the `cardano-ledger`
checkout at `/home/gumbo/playground/cardano-ledger` @ `cd8b7fab8` (Conway era,
V3 context construction in
`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs`). -/

/-- **LR1**: transaction inputs are non-empty, sorted by `TxOutRef`, and every
resolved input value is canonical (`validInputs`,
`CardanoLedgerApi/V3/Contexts.lean:1021-1030`).

WHY UNAVOIDABLE / LEDGER RULE: non-emptiness is the Shelley-and-later
`InputSetEmptyUTxO` predicate failure
(`eras/allegra/impl/src/Cardano/Ledger/Allegra/Rules/Utxo.hs:71,178`);
sortedness holds because `txInfoInputs` is built by
`mapM (transTxInInfoV3 ltiUTxO) (Set.toList txInputs)`
(`Conway/TxInfo.hs:490`) over an ordered `Set TxIn`, and the ledger's `TxIn` Ord
is `(TxId, TxIx)` lexicographic — matching CLAB's `ltTxOutRef`
(`CardanoLedgerApi/V3/Tx.lean:62-64`); value canonicity is `validTxOutValue`,
see LR2. -/
axiom LR1 : ∀ (ctx : ScriptContext), OnChain ctx → validInputs ctx

/-- **LR2**: every transaction output value is canonical — Ada entry first and
strictly positive, policies sorted, token names sorted, quantities strictly
positive (`validOutputs` over `validTxOutValue`,
`CardanoLedgerApi/V3/Contexts.lean:1072-1073`,
`CardanoLedgerApi/V1/Contexts.lean:769-784`).

WHY UNAVOIDABLE / LEDGER RULE: sortedness and positivity come from the ledger's
`MultiAsset = Map PolicyID (Map AssetName Integer)` being translated with
`Map.foldrWithKey'` into an ascending assoc list
(`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Plutus/TxInfo.hs:327-334`);
"Ada first, strictly positive" is the min-ada rule
(`validateOutputTooSmallUTxO`,
`eras/babbage/impl/src/Cardano/Ledger/Babbage/Rules/Utxo.hs:303`) plus the fact
that ada is the least currency symbol. -/
axiom LR2 : ∀ (ctx : ScriptContext), OnChain ctx →
  validOutputs ctx.scriptContextTxInfo.txInfoOutputs

/-- **LR3**: the mint value is canonical — NO Ada entry, policies sorted, token
names sorted, quantities non-zero (`validMintValue` [V3],
`CardanoLedgerApi/V3/Contexts.lean:801-813`).

WHY UNAVOIDABLE / LEDGER RULE: `txInfoMint` for V3 is
`transMintValue = PV3.UnsafeMintValue . PV1.getValue . transMultiAsset`
(`Conway/TxInfo.hs:540-541`), i.e. a `MultiAsset` — which by construction has
no ada entry and no zero quantities — rendered in ascending key order.

WHY IT MATTERS: the positional mint-proof classification
(`WSC/Spec.lean` `mintProofFor`, ADDENDUM E8) is meaningful only because the
mint entries are sorted and ada-free.

CAVEAT (protocol version): the ada entry was present in V3's mint field before
the protocol version at which `MintValue` was introduced; the goldens are PV11
(`WSC/goldens/MANIFEST.md`). LR3 is a PV11-and-later statement. -/
axiom LR3 : ∀ (ctx : ScriptContext), OnChain ctx →
  validMintValue ctx.scriptContextTxInfo.txInfoMint

/-- **LR4 (weakened, see the FLAG below)**: the withdrawal map is
duplicate-free — no credential appears twice.

WHY UNAVOIDABLE / LEDGER RULE: `txInfoWdrl` is
`transMap transAccountAddress transCoinToLovelace (unWithdrawals …)`
(`Conway/TxInfo.hs:544-546`), i.e. the image of a `Map AccountAddress Coin`; a
`Map` has no duplicate keys, and `transAccountAddress` is injective on a fixed
network.

WHY IT MATTERS: the withdrawal-index witnesses in the WSC redeemers resolve
unambiguously.

WHAT WAS REMOVED AND WHY: the previous revision asserted CLAB's
`validWithdrawals` (strict credential ASCENT). At the time that was
order-convention dependent and not entailed by any ledger rule; since task Z1
fixed `ltCredential` to the ledger's `ScriptHashObj < KeyHashObj` (defect D2) it
IS entailed (audit row L), but this axiom is deliberately left in the weaker
duplicate-freeness form — it is all the proofs consume. -/
axiom LR4 : ∀ (ctx : ScriptContext), OnChain ctx →
  ∀ w₁ ∈ ctx.scriptContextTxInfo.txInfoWdrl,
  ∀ w₂ ∈ ctx.scriptContextTxInfo.txInfoWdrl,
    w₁.1 = w₂.1 → w₁ = w₂

/-- **LR5 (weakened, see the FLAG below)**: `validScriptInfo` holds — the
running script's own (purpose, redeemer) pair is the one recorded in the
transaction's redeemer map, and the purpose is internally consistent with the
transaction (own input exists and is script-addressed / own policy is in the
mint / own rewarding credential is a script credential present in `wdrl`) —
`CardanoLedgerApi/V3/Contexts.lean:979-1002` — and the redeemer map is
duplicate-free on purposes.

WHY UNAVOIDABLE / LEDGER RULE: the redeemer handed to a script IS its entry in
`Redeemers` (`transTxRedeemers`,
`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, used for V3 at
`Conway/TxInfo.hs:499,512`); duplicate-freeness holds because `Redeemers` is a
`Map`. The purpose-consistency clauses are the UTXOW script-needed rules
(a spending script runs only for an input it is the payment credential of; a
minting policy only when its policy id is in the mint field; a stake-script
only when its reward account is withdrawn from).

WHY IT MATTERS: the issuance `DelegateSeize` arm indexes the redeemer map
(Issuance.hs:231-240) and the withdraw-zero forwarding pattern relies on the
rewarding clause.

WHAT WAS REMOVED AND WHY: the previous revision also asserted
`validRedeemerMap` (strict ASCENT of purposes). That was REFUTED for WSC's own
transactions by CLAB defect D1; task Z1 fixed `ltScriptPurpose` to the ledger's
`ConwayPlutusPurpose` order, so it IS now entailed (audit row M), but this axiom
is deliberately left in the weaker duplicate-freeness form.

NOTE (ADDENDUM E9): `validScriptInfo` DOES read `scriptContextRedeemer`, but
only for consistency with the redeemer map, never to constrain its content —
the attacker-controlled redeemer stays free. -/
axiom LR5 : ∀ (ctx : ScriptContext), OnChain ctx →
  validScriptInfo ctx ∧
  (∀ r₁ ∈ ctx.scriptContextTxInfo.txInfoRedeemers,
   ∀ r₂ ∈ ctx.scriptContextTxInfo.txInfoRedeemers,
     r₁.1 = r₂.1 → r₁ = r₂)

/-- **LR6**: a rewarding invocation's own credential is a script credential and
appears in the withdrawal map (rewarding conjunct of `validScriptInfo`,
`CardanoLedgerApi/V3/Contexts.lean:988-990`).

WHY UNAVOIDABLE / LEDGER RULE: the ledger runs a stake-script exactly when the
transaction withdraws from that script-credential reward account.

WHY IT MATTERS: the withdraw-zero forwarding pattern (base → global/seize) is
sound because of this; it is the ledger half of P3's conclusion. -/
axiom LR6 : ∀ (ctx : ScriptContext) (cred : Credential), OnChain ctx →
  ctx.scriptContextScriptInfo = ScriptInfo.RewardingScript cred →
  credentialInWithdrawals cred ctx.scriptContextTxInfo.txInfoWdrl

/-- **LR7** = §5.3 `lr_value_conservation` (per-transaction instance): the
transaction is balanced — value in inputs + mint = value in outputs + fee
(`isBalanced`, `CardanoLedgerApi/V3/Contexts.lean:1150-1154`).

WHY UNAVOIDABLE / LEDGER RULE: the Conway `UTXO` value-conservation rule
(`ValueNotConservedUTxO`).

WHY IT MATTERS: containment arguments convert "does not remain at base outputs"
into "escapes to a non-base output" through this.

SCOPE NOTE: the CHAIN-STEP form of conservation (over a growing UTxO set)
belongs in `Composition.lean` and is not stated here. -/
axiom LR7 : ∀ (ctx : ScriptContext), OnChain ctx → isBalanced ctx

/-! ### Ledger triggers (§5.3 LR1/LR2/LR3) — what forces a validator to run

These are the axioms the composition uses to say "and therefore validator X ran
on the SAME transaction" (ARCHITECTURE.md Tier 5.1: one shared `TxInfo`, never
independently quantified contexts). Each is stated as "there is a context with
the SAME `txInfoTxInfo` and the matching `scriptInfo` which the node accepted". -/

/-- The real node (mainnet cost-model budget, no baked step cap) accepts this
invocation of the base validator with these parameters. Abstract — the
chain-side truth the budgeted model is bridged to (see §LR-BUDGET). -/
axiom NodeAcceptsBase : Credential → Credential → ScriptContext → Prop

/-- The real node accepts this invocation of the issuance minting policy. -/
axiom NodeAcceptsMinting : CurrencySymbol → ScriptHash → ScriptContext → Prop

/-- The real node accepts this invocation of the global (transfer) validator. -/
axiom NodeAcceptsGlobal : CurrencySymbol → ScriptContext → Prop

/-- The real node accepts this invocation of the seize validator. -/
axiom NodeAcceptsSeize : CurrencySymbol → ScriptContext → Prop

/-- Re-purpose a context: same transaction, different script purpose. This is
how the "one shared `TxInfo`" discipline is enforced syntactically. -/
def withPurpose (ctx : ScriptContext) (r : Data) (si : ScriptInfo) : ScriptContext :=
  { scriptContextTxInfo := ctx.scriptContextTxInfo
  , scriptContextRedeemer := r
  , scriptContextScriptInfo := si }

/-- **LR_MINT_RUNS_POLICY** = §5.3 LR1 `lr_mint_runs_policy`. *If a transaction
mints or burns anything under policy `cs`, the ledger runs `cs`'s minting
policy on that same transaction with `scriptInfo = MintingScript cs`, and the
transaction is only valid if that run succeeded.* Combined with
`TS_MINTING_IDENTITY` this forces P4 on every entrance of a programmable token.

WHY UNAVOIDABLE / LEDGER RULE: Conway UTXOW "scripts needed" — every policy id
in the mint field contributes a required script witness, and a failing Plutus
script makes the transaction invalid (phase-2).

AUDIT: it is trusting the Cardano ledger; there is nothing to prove in Lean. -/
axiom LR_MINT_RUNS_POLICY :
  ∀ (hp : HonestParams) (ctx : ScriptContext) (cs : CurrencySymbol) (mlh : ScriptHash),
    Deployed hp → OnChain ctx →
    hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint →
    cs = mlhPolicyId hp.protocolParamsCS mlh →
    ∃ r : Data,
      OnChain (withPurpose ctx r (.MintingScript cs)) ∧
      NodeAcceptsMinting hp.protocolParamsCS mlh (withPurpose ctx r (.MintingScript cs))

/-- **LR_WDRL_RUNS_VALIDATOR** = §5.3 LR2 `lr_withdrawal_runs_validator`. *A
script-credential entry in the withdrawal map (including a withdraw-ZERO entry)
means that stake validator ran on this transaction and succeeded.* This is what
makes P3's conclusion ("`globalCred` or `seizeCred` is in `wdrl`") mean "the
global or the seize validator actually ran".

WHY UNAVOIDABLE / LEDGER RULE: Conway UTXOW/DELEG — a withdrawal from a
script-credential reward account requires that script's witness, and Plutus
witnesses are executed; amount zero is permitted and still witnessed. -/
axiom LR_WDRL_RUNS_VALIDATOR :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    (credentialInWithdrawals hp.globalLogicCred ctx.scriptContextTxInfo.txInfoWdrl →
       ∃ r : Data,
         OnChain (withPurpose ctx r (.RewardingScript hp.globalLogicCred)) ∧
         NodeAcceptsGlobal hp.protocolParamsCS
           (withPurpose ctx r (.RewardingScript hp.globalLogicCred))) ∧
    (credentialInWithdrawals hp.seizeLogicCred ctx.scriptContextTxInfo.txInfoWdrl →
       ∃ r : Data,
         OnChain (withPurpose ctx r (.RewardingScript hp.seizeLogicCred)) ∧
         NodeAcceptsSeize hp.protocolParamsCS
           (withPurpose ctx r (.RewardingScript hp.seizeLogicCred)))

/-- **LR_SPEND_RUNS_VALIDATOR** = §5.3 LR3 `lr_spend_runs_validator`. *Spending
a UTxO whose payment credential is the base script credential runs the base
spending validator on this transaction and it must succeed.* This is what
forces P3 on every exit from the mini-ledger.

WHY UNAVOIDABLE / LEDGER RULE: Conway UTXOW — a script-payment-credential input
requires that script's witness and it is executed.

NOTE: the base validator's own parameters are the deployed global/seize
credentials, supplied by `hp` (via TS1 the params datum names exactly those). -/
axiom LR_SPEND_RUNS_VALIDATOR :
  ∀ (hp : HonestParams) (ctx : ScriptContext) (t : TxInInfo),
    Deployed hp → OnChain ctx →
    t ∈ ctx.scriptContextTxInfo.txInfoInputs →
    payCred t.txInInfoResolved = hp.progLogicCred →
    ∃ (r : Data) (d : Option Data),
      OnChain (withPurpose ctx r (.SpendingScript t.txInInfoOutRef d)) ∧
      NodeAcceptsBase hp.globalLogicCred hp.seizeLogicCred
        (withPurpose ctx r (.SpendingScript t.txInInfoOutRef d))

/-! ### LR-CTX (ADDENDUM E5) — the master context bridge, WITH its audit table

E5: *"For every real script invocation, the ledger-constructed ScriptContext
satisfies the matching `validXContext`; plus a clause-by-clause audit table
mapping each conjunct to the Cardano ledger rule entailing it."*

`validSpendingContext / validMintingContext / validRewardingContext ctx`
(`CardanoLedgerApi/V3/Contexts.lean:1231-1246`) each unfold to
`<purpose match> && validScriptContext ctx`, and
`validScriptContext = validScriptInfo && validTxInfo` (`:1225-1227`).

### AUDIT TABLE — conjunct ⟶ entailing Cardano ledger rule

CLAB line numbers are `CardanoLedgerApi/V3/Contexts.lean` unless prefixed;
ledger line numbers are the `cardano-ledger` checkout @ `cd8b7fab8`.

| # | CLAB conjunct (file:line) | Entailing ledger rule (file:line) | Verdict |
|---|---|---|---|
| A | purpose match, `.SpendingScript/.MintingScript/.RewardingScript` (:1231-1246) | the ledger only invokes a script under the purpose that required it (Conway UTXOW scripts-needed); `toPlutusArgs`/`toPlutusV3Args` builds exactly that purpose (`Conway/TxInfo.hs:527`) | **JUSTIFIED** |
| B | `validScriptInfo`: own (purpose, redeemer) ∈ redeemer map (:1001) | the redeemer passed to a script IS its `Redeemers` entry — `transTxRedeemers` (`Babbage/TxInfo.hs:217-221`) | **JUSTIFIED** (see also E9: consistency only, content unconstrained) |
| C | `validScriptInfo` spending clause: own outRef resolves to a script-addressed input, datum consistent (:982-986) | UTXOW: a spending script runs only for an input whose payment credential is its hash; `validInputDatum` mirrors the V3 "datum may be absent" rule (:815-833) | **JUSTIFIED** |
| D | `validScriptInfo` minting clause: own `cs` ∈ `txInfoMint` (:987) | UTXOW: a policy is witnessed exactly when its policy id occurs in the mint field | **JUSTIFIED** |
| E | `validScriptInfo` rewarding clause: own cred is a SCRIPT credential and is in `wdrl` (:988-990) | UTXOW/DELEG: a script-credential withdrawal requires and executes that script | **JUSTIFIED** |
| F | `validInputs`: ≥ 1 input (:1029) | `InputSetEmptyUTxO` (`Allegra/Rules/Utxo.hs:71,178`) | **JUSTIFIED** |
| G | `validInputs`: inputs strictly ascending in `TxOutRef` (:1025) | `Set.toList txInputs` over an ordered `Set TxIn` (`Conway/TxInfo.hs:490`); ledger `TxIn` Ord = (`TxId`,`TxIx`) = CLAB `ltTxOutRef` (`V3/Tx.lean:62-64`) | **JUSTIFIED** |
| H | `validInputs`/`validReferenceInputs`/`validOutputs`: `validTxOutValue` on every value — ada-first, ada > 0, policies+names strictly ascending, quantities > 0 (`V1/Contexts.lean:769-784`) | ascending order from `Map.foldrWithKey'` in `transMultiAsset` (`Alonzo/Plutus/TxInfo.hs:327-334`); ada > 0 from min-ada (`validateOutputTooSmallUTxO`, `Babbage/Rules/Utxo.hs:303`); quantities > 0 because a UTxO cannot hold a non-positive amount | **JUSTIFIED** |
| I | `validReferenceInputs`: refs ascending, may be empty (:1052-1061) | `Set.toList refInputs` (`Conway/TxInfo.hs:491`) | **JUSTIFIED** |
| J | `txInfoFee > 0` (:1201) | `FeeTooSmallUTxO` (`Conway/Rules/Utxo.hs:85`) with mainnet `minFeeB = 155381 > 0` | **JUSTIFIED, PARAMETER-DEPENDENT** — it is a protocol-parameter fact, not a pure rule. No WSC proof uses it. (An earlier revision of this row said "all 13 goldens have `fee = 0`, so no golden satisfies `validXContext`". **That is STALE and was corrected by task C3**: the builder fix re-dumped every golden with a positive fee — measured `500000` or `2000000` on all 13 — and all 9 accepting goldens now satisfy `validXContext` verbatim. See the corrected empirical row-set below.) |
| K | `validMintValue`: ada-free, ascending, quantities ≠ 0 (:801-813) | `transMintValue` over `MultiAsset` (`Conway/TxInfo.hs:540-541`) | **JUSTIFIED at PV11+** (ada-freeness is version-dependent) |
| L | `validWithdrawals`: withdrawals strictly ASCENDING in CLAB's `Credential` order (`validWithdrawals`, V3/Contexts) | `transMap … (unWithdrawals …)` = `unsafeFromList ∘ map ∘ Map.toList` — NO re-sorting (`Conway/TxInfo.hs:544-546, 692-694`); the ledger's key order is `AccountAddress` = (`Network`, `Credential`) with **`ScriptHashObj < KeyHashObj`** (`libs/cardano-ledger-core/src/Cardano/Ledger/Credential.hs:96-99`, `Address.hs:183-191`); `ltCredential` (`V1/Credential.lean`) was **FIXED to that order by task Z1** (it previously had the Plutus order `PubKeyCredential < ScriptCredential`) | **JUSTIFIED** (was ⚠ REFUTED for mixed maps — defect D2, now repaired). Side fact, itself a ledger rule: Plutus' key drops the `Network` component, harmless because `validateWrongNetworkWithdrawal` (`Shelley/Rules/Utxo.hs:181,384`) admits only one network per transaction, on which (`Network`,`Credential`) order restricts to `Credential` order. |
| M | `validRedeemerMap`: redeemers strictly ASCENDING in CLAB's `ScriptPurpose` order (`validRedeemerMap`, V3/Contexts) | `transTxRedeemers = unsafeFromList ∘ mapM … ∘ Map.toList` over `Redeemers` keyed by `PlutusPurpose AsIx` — NO re-sorting (`Babbage/TxInfo.hs:217-221`, used for V3 at `Conway/TxInfo.hs:499,512`); ledger tag order is **`ConwaySpending < ConwayMinting < ConwayCertifying < ConwayRewarding < ConwayVoting < ConwayProposing`** (`Conway/Scripts.hs:202-213`, derived `Ord`); `ltScriptPurpose` (`V3/Contexts.lean`) was **FIXED to that order by task Z1** (it previously had the Plutus constructor order `Minting < Spending < Rewarding < Certifying < …`) | **JUSTIFIED** (was ⚠⚠ REFUTED for every WSC issuance transaction — defect D1, now repaired; that defect is why every `validMintingContext` theorem was vacuous on its own class). Side fact: INTRA-kind, the ledger's `AsIx` index enumerates an already-sorted collection and each Plutus key's leading component sorts the same way (inputs by `TxIn`≡`ltTxOutRef`; policies by `PolicyID`≡`CurrencySymbol`; withdrawals by `Credential` per row L; `Certifying`/`Proposing` compare the index itself; `Voting` by `Voter`, whose ledger `Ord` (`Conway/Governance/Procedures.hs:338-342`) matches `ltVoter`). |
| N | `validTxRange`: validity range non-empty (:1204, `V1/Contexts.lean:964-967`) | `OutsideValidityIntervalUTxO` (`Alonzo/Rules/Utxo.hs:124,519`) — the current slot lies inside, hence non-empty | **JUSTIFIED** |
| O | `validSigners`: required signers strictly ascending (:1205, `V1/Contexts.lean:977-984`) | `Set.toList` of `KeyHash` (`transTxBodyReqSignerHashes`, `Alonzo/Plutus/TxInfo.hs:312`) | **JUSTIFIED** |
| P | `validDatumMap`: datum witnesses ascending by hash (:1207, `V1/Contexts.lean:995-1002`) | `Map.toList` of `TxDats` (`transTxWitsDatums`, `Alonzo/Plutus/TxInfo.hs:316`) | **JUSTIFIED** |
| Q | `validVoterMap`, `validTreasuryAmount`, `validTreasuryDonation` (:1208-1210) | `transVotingProcedures` over ordered maps (`Conway/TxInfo.hs:696-699`); treasury fields are `Maybe Coin` and `Nothing`/positive by construction (`:518-523`) | **JUSTIFIED**; unused by WSC |
| R | `isBalanced` (:1211, :1150-1154) | Conway `UTXO` `ValueNotConservedUTxO` | **JUSTIFIED** |
| **S** | **NOT A CONJUNCT OF `validScriptContext`** — the redeemer map covers EVERY script the transaction needs, not only the running one. CLAB states it separately as `redeemerCoverageAllPlutus` / `noExtraRedeemersAllPlutus` / `redeemersExactAllPlutus` (`CardanoLedgerApi/V3/Contexts.lean`, added by task C3) and it is assumed here as `LR_REDEEMER_COVERAGE` below | `hasExactSetOfRedeemers` (`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`), spec comment at `:237-238`: `dom (txrdmrs tx) = { rdptr txb sp ∣ (sp,h) ∈ scriptsNeeded utxo tx, h ↦ s ∈ txscripts txw, s ∈ Scriptph2 }`. Reached from Conway via `ConwayUTXOW.transitionRules = [Babbage.babbageUtxowTransition]` (`Conway/Rules/Utxow.hs:195`) → `Babbage/Rules/Utxow.hs:351`. **EXACT SET EQUALITY**, both halves enforced by `extSymmetricDifference` (`Utxow.hs:378-383`): `ExtraRedeemers` and `MissingRedeemers` (`:259-262`). `scriptsNeeded = getConwayScriptsNeeded` (`Conway/UTxO.hs:63-74`) quantifies over SIX sources — spending inputs at script addresses (`Alonzo/UTxO.hs:360-373`), script-credential withdrawals (`:375-384`), **every** mint policy id (`:386-394`), script-witnessed certificates (`Conway/TxCert.hs:736-758`), script-credential voters, guardrails-carrying proposals | **THE ROW THAT WAS MISSING.** Its absence is audit finding **F2**: a shape with two script-credential withdrawals and a ONE-entry redeemer map satisfies `validRewardingContext` (rows A–R) while being unbuildable, because rows B/E constrain only the RUNNING script's entry. Now stated. **NOT** folded into `validScriptContext` on purpose: the ledger filters `scriptsNeeded` to non-native scripts (`Utxow.hs:247-251`) and `TxInfo` does not record a script's language, so a coverage CONJUNCT would be over-strong — it would reject a genuine transaction witnessed by a native timelock, for which the rule requires no entry and the `ExtraRedeemers` half forbids one. See the `redeemerCoverageAllPlutus` section header in CLAB for the full argument |

MISSING-BUT-SOUND (ledger rules CLAB does NOT assert; omitting them only
weakens the precondition, which strengthens the theorems):
* from PV11, `txInfoInputs ∩ txInfoReferenceInputs = ∅` —
  `checkReferenceInputsNotDisjointFromInputs` (`Conway/TxInfo.hs:492, 811-822`).
* collateral inputs must be pubkey-addressed (§5.3 LR7): **not expressible** —
  PlutusV3 `TxInfo` carries no collateral field at all.

EMPIRICAL CORROBORATION (task Y3, this session). All 13 golden
`scriptContextHex` values were CBOR-decoded into Lean `ScriptContext`s and every
`validTxInfo` conjunct evaluated (`#eval`, probe generators committed at
`WSC/goldens/ctx-audit/GenCtxAudit.py` and
`WSC/goldens/ctx-audit/GenCtxAuditDetail.py`; each writes a Lean file to run
with `lake env lean`):

**THIS BLOCK WAS STALE AND IS CORRECTED BY TASK C3.** It described the goldens as
they stood BEFORE task Z1 fixed CLAB (defects D1/D2) and before the wsc-poc
builder fix re-dumped every vector (positive fee, ledger-ordered withdrawals,
min-ada on every output). Every bullet below is re-measured at this revision and
names the `WSC/Goldens/Audit.lean` theorem that pins it. The four superseded
claims are listed at the end so the record is not silently rewritten.

* `validXContext` = **true for 10 of 13, including all 9 ACCEPTING goldens**, with
  every conjunct checked verbatim — no relaxation, no artifacts
  (`every_accepting_golden_satisfies_its_precondition`,
  `verdicts_are_exactly_as_tabulated`). The 3 remaining FALSE verdicts are
  tamper-intrinsic to rejecting vectors
  (`remaining_failures_are_tamper_intrinsic`). **LR-CTX therefore has direct
  empirical support for all four validator shapes**, and the goldens — not only
  the hand-built `WSC.P3Witness.ctx` — now serve as `validXContext` anti-vacuity
  witnesses.
* **Row S, re-measured (task C3).** All 13 goldens satisfy `redeemerCoverageAllPlutus`
  (`every_golden_is_redeemer_covered`), and all 9 accepting goldens satisfy the
  FULL exact-set rule `redeemersExactAllPlutus` — the needed-purpose multiset matches
  `txInfoRedeemers` entry-for-entry, at 2–5 entries, across `Spending`,
  `Rewarding` and `Minting` purposes
  (`every_accepting_golden_has_exact_redeemers`,
  `redeemer_needed_and_present_counts`). **This is the evidence that row S is not
  over-strong: the real vectors are redeemer-covered, while every shape in
  `WSC/Shaped/` is not.**
* **NEW FINDING (task C3), and it is the reason row S matters beyond the shapes.**
  `mint-local-empty-withdrawals-REJECT` violates `ExtraRedeemers`: its tamper
  empties `txInfoWdrl` but leaves the `Rewarding` redeemer entry behind, so it
  needs one purpose and carries two
  (`extra_redeemers_in_mint_local_empty_withdrawals`). It passes every conjunct of
  `validScriptContext`, which is why `WSC/Goldens/Audit.lean` previously called it
  *"the suite's only clean negative control"*. **That claim is retracted: with row
  S the suite has NO clean negative control** — no golden is both a well-formed
  ledger context and rejected by the bytecode.
* Row M: `validRedeemerMap` was false for the 2 minting goldens with purposes
  `[Spending, Minting, Rewarding, Rewarding, Rewarding]` — row M's refutation,
  reproduced independently. Since task Z1 fixed `ltScriptPurpose` **both goldens
  PASS**, and post-builder-fix they have **no failing conjunct at all**
  (`fail_mint_burnonly`, `fail_mint_delegate_transfer_topup`,
  `no_purpose_kind_order_violation_remains`).
* Rows L/M order checks: **no order violation of any kind remains in any of the
  13** (`no_order_violations_remain`, `order_failures_are_order_only`).

SUPERSEDED CLAIMS, kept so the correction is auditable — each was true of the
pre-fix vectors under `WSC/goldens/pre-fix/` and is FALSE at this revision:
1. *"`validXContext` = false for all 13 — every golden has `txInfoFee = 0`"* —
   fees are now `500000`/`2000000` on all 13 (row J).
2. *"no golden can serve as a `validXContext` anti-vacuity witness"* — 10 can.
3. *"`validWithdrawals` = false for the 3 seize goldens"* (two script credentials
   emitted DESCENDING) — repaired by the builder's `canonicaliseWdrl`, which also
   fixed their `Rewarding` redeemer entries. The ATTRIBUTION was correct: both
   credentials are SCRIPT credentials, where the old and new `Credential` orders
   agree, so this was a builder artifact and not CLAB's D2.
4. *"`validOutputs` = false for the 2 accepting seize goldens"* (lovelace-free
   residual output) — repaired by the builder's `ensureMinAda`. Again the
   attribution was correct, and row H is the rule that ruled it out.
-/

/-- **LR_CTX (ADDENDUM E5)**: the master context bridge. Every REAL invocation
of one of our validators receives a context satisfying CLAB's full
`validScriptContext`. Every conjunct is a cited Cardano ledger rule — rows A–R of
the table above.

WHY UNAVOIDABLE: it is the axiom that lets theorems proved under
`validXContext` hypotheses apply to real invocations at all.

AUDIT / DISCHARGE: rows A–R of the table are each a cited Cardano ledger rule.

**THE `CLABMapOrderAgrees` SIDE CONDITION IS GONE (task Z1).** Earlier revisions
read `OnChain ctx → CLABMapOrderAgrees ctx → validScriptContext ctx`, where

    CLABMapOrderAgrees ctx :=
      validRedeemerMap …txInfoRedeemers = true ∧ validWithdrawals …txInfoWdrl = true

quarantined rows L and M, the two conjuncts that were then NOT entailed by any
ledger rule because CLAB compared `ScriptPurpose`s and `Credential`s in the
PLUTUS constructor order instead of the ledger's. That was a CLAB defect (D1/D2),
not a gap in the ledger: it made `validMintingContext` UNSATISFIABLE for any
transaction that both spends and mints, i.e. it made every minting-purpose
theorem vacuous on its own target class. It has been REPAIRED at the source —
`ltScriptPurpose` (`CardanoLedgerApi/V3/Contexts.lean`, and the V1/V2 copy in
`CardanoLedgerApi/V1/Contexts.lean`) now uses
`Spending < Minting < Certifying < Rewarding < Voting < Proposing` and
`ltCredential` (`CardanoLedgerApi/V1/Credential.lean`) now uses
`ScriptCredential < PubKeyCredential`, each with the `cardano-ledger` citation in
its docstring. Rows L and M are consequently **JUSTIFIED**, the side condition is
unnecessary, and it has been deleted rather than left as dead weight — a
hypothesis nobody can discharge is exactly what hides vacuity.

RESIDUAL side facts folded into rows L/M (documented there, both ledger rules):
one network per transaction (`validateWrongNetworkWithdrawal`), which is what
lets Plutus' network-less `Credential` key stand in for the ledger's
`AccountAddress` key; and `AsIx`-index order agreeing with the Plutus key order
inside each purpose kind, which holds because the index enumerates an
already-sorted ledger collection.

NOTE: `LR4`/`LR5` are deliberately left in their WEAKENED form (duplicate-freeness
of withdrawal/redeemer keys) even though the full order clauses are now
justified — duplicate-freeness is all any WSC proof consumes, and a weaker axiom
is a smaller trust surface. -/
axiom LR_CTX : ∀ (ctx : ScriptContext),
  OnChain ctx → validScriptContext ctx

/-- **LR_REDEEMER_COVERAGE (ADDENDUM E5, row S)** — the conjunct `LR_CTX` cannot
carry, because `validScriptContext` does not contain it.

Every REAL invocation's transaction has a redeemer-map entry for EVERY script it
needs, not only for the script currently running. This is Conway UTXOW's
`MissingRedeemers` half of `hasExactSetOfRedeemers`; the full citation chain is
row **S** of the audit table above.

WHY IT IS A SEPARATE AXIOM AND NOT A STRONGER `LR_CTX`.
Three reasons, in order of force:

1. **CLAB deliberately does not put it in `validScriptContext`.** The ledger
   filters `scriptsNeeded` to non-native scripts (`Alonzo/Rules/Utxow.hs:247-251`)
   and `TxInfo` never records which language a script is written in, so a
   `validTxInfo` conjunct would be OVER-STRONG — it would reject a genuine
   node-built transaction whose script witness is a native timelock, for which
   the ledger requires no redeemer entry and, by the `ExtraRedeemers` half,
   forbids one. Keeping the rule as a named assumption puts it where the audit
   can see it instead of hiding an unsound strengthening inside a `Bool`.
2. **A conjunction would silently break consumers.** `LR_CTX` is applied at
   `WSC/Composition.lean` and `WSC/Props/Shaped/ShapeRealizability.lean` as
   `LR_CTX ctx h : validScriptContext ctx`; turning its conclusion into a
   conjunction changes every such site. Two axioms compose, one conjunction does
   not.
3. **It keeps the trust surface honest and countable.** This is a genuinely NEW
   assumption — the library did not have it before task C3 — and it should appear
   in the axiom census as one, not be absorbed into an existing name.

WHAT IT IS ASSUMED FOR: `WSC/Props/Shaped/ShapeRealizability.lean` states the
emptiness of SHAPES L1/M1/G1/S1/DT1/DS1 under a `RedeemerCoverageAllPlutus` HYPOTHESIS
because no axiom supplied the rule. This axiom supplies it, so those results can
become unconditional. `redeemerCoverageAllPlutus_wdrl` / `redeemerCoverageAllPlutus_spend` below are
the two forms those proofs consume.

EMPIRICAL SUPPORT — stronger than for most rows in the table, and it is the
check that the rule is not over-strong. All 13 goldens satisfy
`redeemerCoverageAllPlutus` and all 9 ACCEPTING goldens satisfy the full exact-set rule
`redeemersExactAllPlutus`, with the needed-purpose multiset matching `txInfoRedeemers`
entry-for-entry (2–5 entries, `Spending`/`Rewarding`/`Minting`, all four
validators): `WSC/Goldens/Audit.lean`'s `every_golden_is_redeemer_covered`,
`every_accepting_golden_has_exact_redeemers`,
`redeemer_needed_and_present_counts` — all `native_decide` on the CBOR-decoded
real contexts.

SCOPE, stated as narrowly as the measurement warrants: this is the
`MissingRedeemers` half only. The `ExtraRedeemers` half is CLAB's
`noExtraRedeemersAllPlutus` and is **not** assumed here, because nothing needs it — and
because it is the direction that would be WEAKER than the ledger rule in the
presence of a native script witness, not stronger. Assume it separately if a
proof ever wants it.

**KNOWN OVER-STRENGTH — audit finding F18. READ BEFORE USING THIS AXIOM.**
This axiom is **NOT** the Conway rule; it is the Conway rule read at an
ALL-PLUTUS transaction, and its conclusion is literally
`redeemerCoverageAllPlutus`, which
`CardanoLedgerApi.V3.Contexts.coveredByNonNative_strictly_weaker` proves is
strictly stronger than `hasExactSetOfRedeemers`' `MissingRedeemers` half. The
ledger filters `scriptsNeeded` by `not (isNativeScript script)`
(`Alonzo/Rules/Utxow.hs:247-251`), and `TxInfo` cannot express that filter — it
carries no script bodies and no language tags, only hashes
(`CardanoLedgerApi/V2/Tx.lean:78-83`, `V1/Scripts.lean:15-16`). **A real Conway
transaction with a script-credential withdrawal witnessed by a native timelock
satisfies `OnChain` and FALSIFIES this axiom's conclusion**, because the ledger
requires no redeemer entry for it and the `ExtraRedeemers` half forbids one.

CONSEQUENCE FOR CONSUMERS, and it splits by direction:
* Used to DISCHARGE coverage about a transaction the campaign is constructing
  (every realizability inhabitant) the all-Plutus reading is conservative and
  the axiom is not needed at all — those go through `native_decide`.
* Used to ASSUME coverage about an arbitrary on-chain transaction — which is
  what `redeemerCoverageAllPlutus_wdrl`/`_spend` and hence
  `WSC.g6_class_is_empty` do — the emptiness conclusion is established only for
  members whose uncovered withdrawal/input is NON-NATIVE. The per-use audit and
  the re-established, explicitly-conditioned versions are in
  `WSC/Props/Shaped/ShapeRealizability.lean` §2.2.

The axiom is retained under its original name (renaming it would silently
renumber the campaign's axiom census) but its statement now reads
`redeemerCoverageAllPlutus`, which is the point: the over-strength is visible at
the axiom and at every use site. -/
axiom LR_REDEEMER_COVERAGE : ∀ (ctx : ScriptContext),
  OnChain ctx → redeemerCoverageAllPlutus ctx.scriptContextTxInfo

/-- **The form `ShapeRealizability` consumes.** A script-credential withdrawal in
an on-chain transaction forces a `Rewarding` redeemer-map entry for that
credential. This is literally the statement of that module's `RedeemerCoverageAllPlutus`
`Prop`, so a proof that took `rc : RedeemerCoverageAllPlutus` can be closed by passing
`WSC.redeemerCoverageAllPlutus_wdrl` instead — making the shape-emptiness results
unconditional. -/
theorem redeemerCoverageAllPlutus_wdrl (ctx : ScriptContext) (h : ScriptHash) (n : Integer)
    (hoc : OnChain ctx)
    (hw : (Credential.ScriptCredential h, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl) :
    findRedeemer (.Rewarding (.ScriptCredential h))
      ctx.scriptContextTxInfo.txInfoRedeemers ≠ none :=
  findRedeemer_rewarding_ne_none_of_coverageAllPlutus (LR_REDEEMER_COVERAGE ctx hoc) hw

/-- Companion for the spending side: spending a script-addressed input in an
on-chain transaction forces a `Spending` entry for that input's `TxOutRef`.
`WSC/Props/Shaped/ShapeRealizability.lean`'s `t1_class_is_empty` reaches the same
conclusion through `LR_SPEND_RUNS_VALIDATOR` + `LR_CTX` for the RUNNING script;
this covers every script-addressed input, running or not. -/
theorem redeemerCoverageAllPlutus_spend (ctx : ScriptContext) (t : TxInInfo) (sh : ScriptHash)
    (hoc : OnChain ctx)
    (ht : t ∈ ctx.scriptContextTxInfo.txInfoInputs)
    (hsc : t.txInInfoResolved.txOutAddress.addressCredential = .ScriptCredential sh) :
    findRedeemer (.Spending t.txInInfoOutRef)
      ctx.scriptContextTxInfo.txInfoRedeemers ≠ none :=
  findRedeemer_spending_ne_none_of_coverageAllPlutus (LR_REDEEMER_COVERAGE ctx hoc) ht hsc

/-- **NONNEG (ADDENDUM E6)**: non-negativity of held amounts. Every UTxO a
transaction touches holds a non-negative amount of every asset.

E6 verbatim: `∀ u ∈ L, ∀ cs tn, valueOf cs tn u.value ≥ 0`.

WHY UNAVOIDABLE / WHY IT MATTERS: the Preservation reduction needs it to turn
`OutOfBase(L, cs) = 0` into "no out-of-base INPUT holds `cs`" — without
non-negativity a zero total could hide a positive and a negative holding.

WHY IT IS NOT JUST LR1/LR2: those give strict positivity of the entries that
are PRESENT in a canonical value, which is a statement about the encoding;
`valueOf` returns 0 for absent assets, so this is the (weaker, and directly
usable) arithmetic form. The previous revision re-asserted `validTxOutValue`
here, which duplicated LR1/LR2 without providing the arithmetic fact.

SCOPE NOTE (honest): this is the PER-TRANSACTION projection of E6. The
ledger-wide statement quantifies over the whole UTxO set `L` and must be
restated in `Composition.lean` once a `Ledger` type exists; it is NOT implied by
the version below. -/
axiom NONNEG : ∀ (ctx : ScriptContext), OnChain ctx →
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs, ∀ (cs : CurrencySymbol) (tn : TokenName),
     0 ≤ valueOf cs tn t.txInInfoResolved.txOutValue) ∧
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs, ∀ (cs : CurrencySymbol) (tn : TokenName),
     0 ≤ valueOf cs tn t.txInInfoResolved.txOutValue) ∧
  (∀ o ∈ ctx.scriptContextTxInfo.txInfoOutputs, ∀ (cs : CurrencySymbol) (tn : TokenName),
     0 ≤ valueOf cs tn o.txOutValue)

/-! ### LR-BUDGET (ADDENDUM E1) — the boundedness caveat, quantified

E1, binding: *"`#prep_uplc … n` bakes a concrete CEK step budget; `runSteps`
returns `State.Error` when the budget is exhausted (`CekMachine.lean:233`), and
`isSuccessful` matches only `.Halt`. Hence every `isSuccessful (prop …) → POST`
theorem constrains ONLY transactions whose validator run halts within the
budget. … New axiom `LR-BUDGET`: for any transaction whose validator execution
halts within K CEK steps, ledger-accept ⟺ `isSuccessful (appliedX.prop …)`. K is
per-validator and must be computed and published (empirically calibrated with
concrete accepting ctxs run through `cekExecuteProgram`)."*

ALL results of this campaign are therefore BOUNDED-TRANSACTION model checking of
the real bytecode. They must never be claimed unbounded.

WHAT WAS WRONG BEFORE (task Y3): the axioms quantified over `txSize ctx ≤ K`
— a transaction-SIZE proxy whose relation to CEK step count is unproven — and
used `∃ K`, which pins nothing and is exactly what a reviewer reads as "any K,
including a vacuous one". The bound is now on CEK steps and the constants are
published `def`s.

## RESTATEMENT (task A1) — READ THIS BEFORE CITING ANY `LR_BUDGET_*`

**What changed.** The four axioms used to name `appliedX_K.prop` — an
`Optimize.main` output produced by `#prep_uplc`, `noncomputable`, not
kernel-reducible, reachable only through a `blaster` verdict. They now name
`Runs.baseRun K` / `Runs.mintingRun K` / `Runs.globalRun K` / `Runs.seizeRun K`
(`WSC/Runs.lean`), which are plain Lean definitions:

    Runs.XRun K params ctx = cekExecuteProgram <imported flat>.script
                               (<WSC/Prep inputs fn> params ctx) K

This was audit finding **F3**'s repair and task U1's own top recommendation
(`WSC/SHAPE-BRIDGE.md` §9). Four consequences, each independently checkable:

1. **The bridge from a shaped theorem to the ledger side is now a kernel-checked
   `rfl`, not a solver verdict.** `WSC/ShapeBridge.lean`'s sixteen `exec_<SHAPE>`
   theorems are `appliedXShaped.exec <leaves> = Runs.XRun K <params> (σ <leaves>)`
   — `rfl`, `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**, and they
   hold at EVERY budget. Before A1 the right-hand side of `LR_BUDGET_*` was a term
   no `rfl` could reach.
2. **`GlobalPreppedAt` is DELETED.** It was the meta-level side condition "the
   term you handed me really is the prep of the right flat at budget `K`", and it
   was an `axiom` because nothing inside Lean can inspect an elaborator's output.
   `Runs.globalRun K` exhibits the flat, the inputs function and the budget in its
   own definition, so the condition is discharged by reading it. The axiom count
   of this file drops by one.
3. **The four bridges are now available at EVERY budget the campaign proves
   things at** — 2500 (P4's custody arms), 3300 (P6), 3800 (P2), 4400 (P1) — not
   only at the three where an unshaped `#prep_uplc` is affordable (600 / 900 /
   1600). This is why `K_mint_custody`, `K_global_member` and `K_seize` can be
   published below at all; before A1 they could not be, for lack of a term to
   name. Each is `K`-parametric for exactly this reason.
4. **`PropExecFaithful` is no longer on the base/keystone path.**
   `WSC/Props/P3_BaseRun.lean` proves P3 with its accept hypothesis on
   `Runs.baseRun K_base`, so `Composition.p3_lifted` — the only consumer of any
   `LR_BUDGET_*` in the library — never mentions `.prop`.

**WHAT DID *NOT* CHANGE, stated so this is not oversold.**

* These are still AXIOMS, and their content is exactly what it was: *for a
  transaction whose real, unmetered validator run halts within `K` CEK steps,
  ledger acceptance coincides with `isSuccessful (Runs.XRun K …)`.* The reason it
  cannot be proved is unchanged: `nodeStepsX` is the unmetered count, the metered
  run returns `Error` on exhaustion, and the needed `runSteps` monotonicity fact
  (terminal states are returned as-is; fuel-0 becomes `Error` only in a
  non-terminal state, `PlutusCore/UPLC/CekMachine.lean:229-241`) is a meta-theorem
  the substrate cannot state (SPIKE-FINDINGS).
* The results are still bounded twice: by `K` **and**, for every P1/P2/P4-arm/P5/P6
  result, by a SHAPE. A1 does nothing about shape coverage (audit **F2**), and
  restating an axiom cannot.
* `PropExecFaithful` is **still a dependency of the shaped layer**, because every
  shaped P-theorem is still stated on `appliedXShaped.prop` and reaches the ledger
  side through `ShapeBridge.bridge_<S>` rather than through `exec_<S>`. A1 removes
  it from ONE path (base/P3) and demonstrates by measurement that the same removal
  is feasible for the rest; it does not perform that removal. See
  `WSC/Props/P3_BaseRun.lean` §FOLLOW-ON.

MEASUREMENT PROVENANCE for every constant below:
`WSC/goldens/K-MEASUREMENTS.md` (task X1) — true CEK step counts of the 13
golden runs, measured on the fully-applied closed programs
(`WSC/goldens/applied/*.flat`) by iterating the real
`PlutusCore.UPLC.CekMachine.step`, cross-checked to the UNIT against the
ledger's `ExBudget` for all 9 accepting goldens — PLUS, for the shaped budgets,
the in-library per-shape witnesses named in each constant's docstring below.
**Do NOT use K-MEASUREMENTS §5.1's prep-cost table for anything**: it was
measured under `lake env lean` without `--load-dynlib` and is 6-58x pessimistic;
§5.1 now carries the superseding `lake build` figures (audit F5). -/

/-- CEK steps the real machine takes on the base validator applied to
`(globalCred, seizeCred, ctx)`. Abstract: this is the same counter
`#prep_uplc`'s budget bounds (`PlutusCore/UPLC/PreProcess.lean:143-153` →
`cekExecuteProgram` → `runSteps`), but the *unbudgeted* count, which the model
cannot compute for a symbolic `ctx`. -/
axiom nodeStepsBase : Credential → Credential → ScriptContext → Nat

/-- CEK steps the real machine takes on the issuance minting policy. -/
axiom nodeStepsMinting : CurrencySymbol → ScriptHash → ScriptContext → Nat

/-- CEK steps the real machine takes on the global (transfer) validator. -/
axiom nodeStepsGlobal : CurrencySymbol → ScriptContext → Nat

/-- CEK steps the real machine takes on the seize validator. -/
axiom nodeStepsSeize : CurrencySymbol → ScriptContext → Nat

/-! #### The published K constants

REPUBLISHED BY TASK A1 against the rule the task set: **every constant is ≥ the
measured accepting step count of a NAMED in-library witness, and that witness is
named in the docstring.** The witnesses are `native_decide` runs of the REAL
imported bytecode through `cekExecuteProgram` — no solver, no prep, no
`PropExecFaithful` — and each is pinned to the step with a `Halt` at `K_witness`
and an `Error` at `K_witness - 1`.

| constant | value | witness | measured K | non-vacuity theorem |
|---|---|---|---|---|
| `K_base` | 600 | `WSC.P3Witness.ctx` (golden: 208) | 208 | `Composition.baseNonVacuous` |
| `K_mint` | 900 | `WSC.P4Witness.ctx` (BurnOnly) | 784 | `Composition.mintingNonVacuous` |
| `K_mint_custody` | 2500 | `WSC.P4LocalShapedWitness.ctx` (SHAPE L1) | 1681 | `NonVacuity.mintingNonVacuous_at_2500` |
| `K_global_nonmember` | 1600 | `WSC.P5ShapedWitness.ctx` (SHAPE G1) | 1541 | `NonVacuity.globalNonVacuous_at_1600` |
| `K_global_member` | 3300 | `WSC.P6ShapedWitness.ctx` (SHAPE G6) | 2837 | `NonVacuity.globalNonVacuous_at_3300` |
| `K_global` | 4400 | `WSC.P1ShapedWitness.ctxOk` (SHAPE T1) | 2603 (T2/T7 3572, T6 3150) | `NonVacuity.globalNonVacuous_at_4400` |
| `K_seize` | 3800 | `WSC.P2ShapedWitness.ctxAccept` (SHAPE S1) | 3004 (residual 3328) | `NonVacuity.seizeNonVacuous_at_3800` |

Every one of those seven non-vacuity theorems is PROVED (`WSC/Composition.lean`
§7 for the first two, `WSC/Props/Shaped/NonVacuity.lean` for the other five).
That is the whole set — no `*NonVacuous` obligation of this file is open. -/

/-- **K_base = 600** — the published CEK step bound of the base validator, and
the prep budget of `WSC/Prep/Base.lean`.

* NON-VACUITY WITNESS: golden `programmableLogicBase.base-spend-transfer-tx`
  halts (accepting) in **208** steps (K-MEASUREMENTS §3), i.e. 2.9× inside the
  bound; and the in-library concrete witness `WSC.P3Witness.ctx`
  (WSC/Props/P3_Base.lean:149) is proved accepted at this very budget
  (`P3Witness.exec_accepts`). The mandatory vacuity probe
  `P3_base_vacuity_probe` is **Falsified** at 600, and so is
  `P3_run_vacuity_probe` at the RUN term `Runs.baseRun 600`
  (`WSC/Props/P3_BaseRun.lean`).
* NON-VACUITY THEOREM: `WSC.Composition.baseNonVacuous : BaseNonVacuous K_base`,
  discharged from `P3Witness.exec_accepts` — which, after A1, is a
  `native_decide` witness rather than a `blaster` one, so `baseNonVacuous` no
  longer carries `sorryAx`.
* PREP COST RE-MEASURED (task A1, `lake build`, cold module): **1.35 s**
  (K-MEASUREMENTS §5.1's superseding table; the old "≈11 s class" figure was a
  `lake env lean` artifact).
* SHAPE COVERED: `K_max` over accepting base goldens is also 208, so 600 covers
  every base-spend shape in the golden suite with margin.

CAVEAT: a bound calibrated on these shapes says nothing about arbitrarily large
transactions; K-MEASUREMENTS §4 is explicit that per-shape K scales with
input/output/policy counts. -/
def K_base : Nat := 600

/-- **K_mint = 900** — the published CEK step bound for the issuance policy on
BURN-ONLY-sized transactions. For the three custody arms use `K_mint_custody`.

* NON-VACUITY WITNESS: golden `programmableTokenMinting.mint-burnonly` halts
  (accepting) in **784** steps (K-MEASUREMENTS §3), so 900 admits an accepting
  run; 600 does NOT (600 < 784), which is why the budget must be raised. The
  in-library witness is `WSC.P4Witness.ctx` (`exec_accepts_at_900`).
* NON-VACUITY THEOREM: `WSC.Composition.mintingNonVacuous : MintingNonVacuous K_mint`.
* PREP COST RE-MEASURED (task A1, `lake build`, cold module): **1.53 s**
  (published as 27.6 s — an 18x overstatement; see K-MEASUREMENTS §5.1).
* SHAPE COVERED: burn-only-sized minting transactions, i.e. SHAPES M1/M2, which
  is exactly what `WSC/Props/P4_Minting.lean` and `Props/Shaped/P4Shaped*.lean`
  are stated at.

PREP THIS CONSTANT WAS MATCHED TO (task U2): `WSC/Prep/Minting900.lean`'s
`appliedMinting900`. AFTER TASK A1 the axiom no longer names a prep at all — it
names `Runs.mintingRun K_mint`, which is the SAME imported flat and the SAME
inputs function under an explicit meter. The budget-600 `appliedMinting` of
`WSC/Prep/Minting.lean` is retained only for the pipeline/decode gate and for the
machine-checked vacuity characterization `WSC.minting600_is_vacuous`. -/
def K_mint : Nat := 900

/-- **K_mint_custody = 2500 — NEW IN TASK A1.** The published CEK step bound for
the issuance policy on the three CUSTODY-FORWARDING arms.

WHY IT COULD NOT BE PUBLISHED BEFORE, and why it can now. P4's `Local`,
`DelegateTransfer` and `DelegateSeize` arms are proved at SHAPES L1/L2/DT1/DS1,
whose preps bake budget **2500**; their concrete accepting witnesses cost
K = 1681 / 1257 / 1466. An UNSHAPED `#prep_uplc` at 2500 is unaffordable
(K-MEASUREMENTS §5.1: minting at 1700 did not finish in 48.6 min), so under the
old `appliedX_K.prop` form there was no term to state a 2500 bridge against — the
gap `WSC/Composition.lean` §9.5 records and audit F12 repeats. `Runs.mintingRun
2500` needs no prep, so the bridge is now statable, and its non-vacuity is a
THEOREM.

* NON-VACUITY WITNESS: `WSC.P4LocalShapedWitness.ctx` (SHAPE L1, a genuinely
  token-CREATING transaction — `ctx_mints_positive`), **K = 1681** to the step
  (`P4LocalShapedWitness.K_is_1681`: `Halt` at 1681, `Error` at 1680). 1681 is
  also the measured step count of the REAL off-chain `Local` golden
  `mint-local-registered-by-ref` (K-MEASUREMENTS §3).
* NON-VACUITY THEOREM: `WSC.NonVacuity.mintingNonVacuous_at_2500`.
* COVERS: the other two arms too — DT1 at K = 1257 (`ctxDT_K_is_1257`) and DS1 at
  K = 1466 (`ctxDS_K_is_1466`) are both < 2500.

NOT YET CONSUMED, and this is a deliberate limit of A1's scope:
`WSC/Composition.lean`'s `WithinBudget` still bounds the minting clause by
`K_mint = 900`. Raising it to `K_mint_custody` would ADMIT more transactions into
`HonestTx`, which STRENGTHENS `top_claim`'s statement and correspondingly
HARDENS its open `LeafSet` obligations — a change to the composition's core
transaction class, not a restatement. It is now unblocked (the axiom exists at
2500); it is not taken here. -/
def K_mint_custody : Nat := 2500

/-- **K_global = 4400** — the published CEK step bound for the global
(transfer) validator, sized for the CONTAINMENT (P1) shapes. **REPUBLISHED FROM
1600 BY TASK U2**; read the CORRECTION paragraph below before citing the old
value.

CORRECTION (task U2). The constant was published at **1600**, calibrated on the
single cheapest accepting global golden (`transfer-nonmember-covering-node`,
K = 1,554 — K-MEASUREMENTS §3), which is P5's subject shape. That value is TOO
TIGHT for the class the library now proves things about: the P1 (containment)
theorems of `WSC/Props/Shaped/P1Shaped.lean` are stated at prep budget **4400**,
and their own concrete accepting witnesses, run through the real CEK, cost

| shape | witness | measured K | source |
|---|---|---|---|
| T1 (pure transfer, Path A) | `P1ShapedWitness.ctxOk` | **2,603** | `P1ShapedWitness.K_T1_is_2603` |
| T2 (symbolic mint/burn) | `P1ShapedWitness.ctxBurn` | **3,572** | `P1ShapedWitness.K_T2_is_3572` |
| T6 (output-side) | `P1ShapedOutWitness` | **3,150** | `P1Shaped.lean` §5 |
| T7 (output-side burn) | `P1ShapedOutWitness` | **3,572** | `P1Shaped.lean` §5 |

and the two containment-carrying off-chain goldens cost **3,262** and **3,726**
(K-MEASUREMENTS §3). At `K_global = 1600` the `WithinBudget` global clause of
`WSC/Composition.lean` EXCLUDED every transaction those theorems are about, so a
leaf instantiated from them could never have been consumed. 4400 is the budget
the shaped preps actually bake
(`WSC/Shaped/GlobalShapedP1Prep.lean`, `…P1MintPrep.lean`, `…P1OutPrep.lean`),
and it is ≥ every measured accepting K for this validator.

* NON-VACUITY WITNESS AT 4400, on the UNSHAPED bytecode:
  `WSC.P1ShapedWitness.exec_accepts_unshaped` — `cekExecuteProgram
  programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxOk) 4400` HALTS
  (`native_decide`, no SMT), where `ctxOk` additionally satisfies CLAB's
  `validRewardingContext` (`P1ShapedWitness.ctxOk_valid`). That term IS
  `Runs.globalRun 4400 ppCS ctxOk`, definitionally — which is why the non-vacuity
  obligation below is now discharged rather than merely "dischargeable".
  Lower bracket: `P1ShapedWitness.exec_rejects_at_600` (budget 600 ⟹ `Error`) and
  `K_T1_is_2603` (`Halt` at 2603, `Error` at 2602).
* NON-VACUITY THEOREM (task A1): `WSC.NonVacuity.globalNonVacuous_at_4400`.
* SECOND WITNESS, at the OLD value: `WSC.P5ShapedWitness.exec_accepts_at_1600_unshaped`
  (theorem-grade) — HALT at 1600 — packaged as the non-vacuity theorem
  `WSC.NonVacuity.globalNonVacuous_at_1600`. The corroborating figure on the real
  off-chain golden flat is K = 1554 (WSC/goldens/K-MEASUREMENTS.md §3); it is a
  measurement, not a Lean term. (`WSC/Props/P5_Witness1600.lean`, whose two
  `#eval`s prompted audit F11 and whose two `native_decide` theorems restated the
  same two facts about the applied golden, has been deleted as redundant with the
  theorem named above; nothing in Lean depended on it.)
* PREP COST. Symbolic (fully unshaped) `#prep_uplc` of this validator at budget
  1600 costs **37.8 s** (task A1, `lake build`, cold module — the figure
  K-MEASUREMENTS §5.1 published as 2,143 s = 35.7 min is a 57x overstatement,
  audit F5). Even so there is no unshaped 4400 prep and none is needed: A1's
  restatement puts the ledger side on `Runs.globalRun 4400`, which costs nothing
  to elaborate. SHAPED prep at 4400 is **1.00 s**
  (`WSC/Props/Shaped/P1Shaped.lean` header, measured).

CONSEQUENCE FOR THE BRIDGES — **CHANGED BY TASK A1.** It used to read: "raising
this constant does NOT by itself produce a usable global budget bridge, because
the only global prep at 4400 is SHAPED". That is no longer the binding
constraint: `LR_BUDGET_global` at `K = 4400` names `Runs.globalRun 4400`, whose
non-vacuity is proved and which requires no prep. What a SHAPED leaf still owes
is the SHAPE BRIDGE (`ShapeBridge.bridge_T1`/`T2`/`T6`/`T7`, `blaster`-verified,
Tier B — read `WSC/SHAPE-BRIDGE.md` §5.2's health warning) and, above all, shape
COVERAGE, which nothing in this library supplies (audit F2). -/
def K_global : Nat := 4400

/-- **K_global_nonmember = 1600** — the covering-node / NonMember SUB-BOUND of
the global validator: the budget `WSC/Prep/Global1600.lean` preps at, the budget
P5 is stated at (`WSC/Props/P5_NonMember.lean`, `WSC/Props/Shaped/P5Shaped.lean`
SHAPE G1), and the smallest round budget above the cheapest accepting global
golden's K = 1,554.

Kept as a SEPARATE constant by task U2 rather than folded into `K_global`,
because a budget bridge is only sound at the budget its RIGHT-HAND SIDE actually
meters: a transaction taking 3,000 CEK steps satisfies `nodeStepsGlobal … ≤
K_global` but `Runs.globalRun 1600` returns `Error` on it, so quoting the 1600
run at the 4400 bound would assert `NodeAcceptsGlobal ↔ False`. This is exactly
why `LR_BUDGET_global` is `K`-parametric.

* NON-VACUITY WITNESS: `WSC.P5ShapedWitness.ctx` (SHAPE G1), **K = 1541** to the
  step (`K_is_1541`), `validRewardingContext`-true with zero failing conjuncts
  (`ctx_valid`), accepted at 1600 on the UNSHAPED bytecode
  (`exec_accepts_at_1600_unshaped`).
* NON-VACUITY THEOREM (task A1): `WSC.NonVacuity.globalNonVacuous_at_1600`. This
  CLOSES audit finding **F7**. Note that A1's discharge is strictly cleaner than
  the one F7 pointed at (`ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600`, a
  `blaster` verdict on `appliedGlobal1600.prop`, hence `sorryAx`): stated on
  `Runs.globalRun 1600` the obligation is closed by `native_decide` on the real
  CEK, with no solver and no `sorryAx`. The `ShapeBridge` version is retained as
  independent corroboration on the `prop` term. -/
def K_global_nonmember : Nat := 1600

/-- **K_global_member = 3300 — NEW IN TASK A1.** The MEMBER-claim sub-bound of
the global validator: the budget `WSC/Shaped/GlobalMemberShaped.lean` preps at
and the budget P6 is stated at (SHAPE G6).

Published as its own constant for the same reason `K_global_nonmember` is: P6's
class costs 2837 steps where P5's costs 1541, and the 1,296-step gap IS the
containment scan a `Member` claim switches on (`P6ShapedWitness.K_is_2837`
docstring). Quoting either bound at the other's run term would be unsound.

* NON-VACUITY WITNESS: `WSC.P6ShapedWitness.ctx` (SHAPE G6), **K = 2837** to the
  step (`K_is_2837`: `Halt` at 2837, `Error` at 2836), `validRewardingContext`-true
  in full (`ctx_valid`).
* NON-VACUITY THEOREM: `WSC.NonVacuity.globalNonVacuous_at_3300`.
* THE REASON THE BUDGET IS 3300 AND NOT 2500 is the most instructive negative
  result in the campaign and must travel with this constant: task V3 first stated
  P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and the mandatory vacuity probe
  then showed the accept class was UNSAT — the theorem was EMPTY. Preserved as
  `WSC/Shaped/Probe/G6Vacuous2500.lean`. 2500 < 2837 is exactly why. -/
def K_global_member : Nat := 3300

/-- **K_seize = 3800 — NEW IN TASK A1. The previous revision of this file said a
`K_seize` DELIBERATELY DID NOT EXIST; that reasoning was sound for the axiom form
it applied to and does not survive A1's restatement. Both halves are recorded
here, because the old warning is the more important of the two.**

WHAT THE OLD ENTRY SAID, and it was correct: there is no affordable UNSHAPED
`#prep_uplc` for this validator above ~1,000 steps (K-MEASUREMENTS §4/§5.2:
symbolic prep at 2,000 never completed in 77 min; 3,002 extrapolates to ≥ 15
days), the cheapest accepting seize run costs **3,002** steps, and therefore every
affordable prep budget is PROVABLY VACUOUS — the E2 spike's probes at 600 and
1,000 returned `Valid` for "no accepting context exists". Stating a bridge over
`appliedSeize.prop` at any affordable `K` would have been a vacuous theorem, and
inventing a constant for it would have been the single easiest way to publish one.

WHAT CHANGED: `Runs.seizeRun K` is not a prep. It has no elaboration cost at any
budget, so the obstacle above — which was entirely about `#prep_uplc` cost —
does not apply to it, and the vacuity question becomes an empirical one with a
measured answer.

* NON-VACUITY WITNESS: `WSC.P2ShapedWitness.ctxAccept` (SHAPE S1), **K = 3004**
  to the step, and `ctxResidual` at **K = 3328** (`K_is_3004_and_3328`: `Halt` at
  K, `Error` at K-1). Both satisfy `validRewardingContext` IN FULL, including
  `isBalanced` (`all_four_valid`). For comparison the two accepting seize GOLDENS
  cost **3,002** and **5,079** steps (re-measured by task C3 on the current
  applied flats; the figures 2,570 / 4,647 published before it are the pre-fix
  vectors' — `K-MEASUREMENTS.md` Appendix A′), so 3800 covers the 1-input
  golden's regime (3,002 ≤ 3800) and NOT the 2-input one (5,079 > 3800) — a real
  limit of this constant, stated. **The correction does not move the limit:** it
  held before and holds after, on both sides.
* NON-VACUITY THEOREM: `WSC.NonVacuity.seizeNonVacuous_at_3800`. So
  `LR_BUDGET_seize` is, for the first time, a bridge that can be applied to
  something.
* STILL NOT CONSUMED: `WSC/Composition.lean` has no seize clause in
  `WithinBudget` and calls `LR_BUDGET_seize` nowhere; P2's leaf (`LeafSet.p2`) is
  untouched (audit F1). Publishing this constant does not close that gap, and the
  shape bound on P2 is the essential one (audit F2 / §5.2 of the audit). The
  parenthetical here used to add "P2b is FALSE-in-general on the source model and
  closes at SHAPE S1 only"; **that was wrong and is retracted** — see AUDIT.md
  §5.2. `WSC.P2.tokensContain_sound` proves the obligation that claim rested on,
  and `WSC/Props/Shaped/P2ShapedR2.lean` closes P2b over a strictly larger shape.
  The shape bound is real; "false in general" was not. -/
def K_seize : Nat := 3800

/-- Non-vacuity of the base validator at budget `K`: some ledger-normalized
context is ACCEPTED by `Runs.baseRun K`.

**RESTATED BY TASK A1** from `isSuccessful (appliedBase.prop g s ctx)` to the run
form, and made `K`-parametric. DISCHARGED at `K_base` by
`WSC.Composition.baseNonVacuous` from `WSC.P3Witness` — and note what the
restatement bought: the old discharge went through `P3Witness.prop_accepts`
(`by blaster`, hence `sorryAx`), the new one goes through
`P3Witness.exec_accepts` (`native_decide` on the real CEK), so `baseNonVacuous`
is now free of `sorryAx`. -/
def BaseNonVacuous (K : Nat) : Prop :=
  ∃ (g s : Credential) (ctx : ScriptContext),
    validSpendingContext ctx = true ∧ isSuccessful (Runs.baseRun K g s ctx)

/-- Non-vacuity of the issuance policy at budget `K`: some ledger-normalized
minting context is ACCEPTED by `Runs.mintingRun K`.

**RESTATED BY TASK A1** from `appliedMinting900.prop` to the run form, and made
`K`-parametric so the custody budget can be reached. HISTORY, kept because it is
the sharpest vacuity lesson in the minting class: the predicate once named
`appliedMinting.prop` (budget 600), whose negation is MACHINE-CHECKED — see
`WSC.minting600_is_vacuous` (`WSC/Props/P4_Minting.lean:380-386`, `✅ Valid` for
"no accepting context exists inside 600 steps"), predicted by the cheapest
accepting run costing 784 steps. So the statement was FALSE and
`LR_BUDGET_minting` could not be applied to anything.

DISCHARGED at BOTH published budgets:
* `K_mint = 900` — `WSC.Composition.mintingNonVacuous`, from the concrete
  `BurnOnly` witness `WSC.P4Witness` (`ctx_valid` + `exec_accepts_at_900`, both
  `native_decide`). Also free of `sorryAx` after A1, for the same reason
  `baseNonVacuous` is: the old proof used `blaster` on `appliedMinting900.prop`.
* `K_mint_custody = 2500` — `WSC.NonVacuity.mintingNonVacuous_at_2500`, from
  `WSC.P4LocalShapedWitness` (SHAPE L1, K = 1681). NEW; there was previously no
  term at 2500 to state it over. -/
def MintingNonVacuous (K : Nat) : Prop :=
  ∃ (pcs : CurrencySymbol) (mlh : ScriptHash) (ctx : ScriptContext),
    validMintingContext ctx = true ∧ isSuccessful (Runs.mintingRun K pcs mlh ctx)

/-- Non-vacuity of the global (transfer) validator at budget `K`: some
ledger-normalized rewarding context is ACCEPTED by `Runs.globalRun K`.

**RESTATED BY TASK A1.** Task U2 made this predicate parametric over the PREPPED
TERM (`globalProp : CurrencySymbol → ScriptContext → State`) because the global
theorems live at three different budgets and hard-wiring one prep would either
pin the axiom to a single budget or keep a known-vacuous statement. That was the
right move for the prep form, but it cost a new abstract declaration
(`GlobalPreppedAt`) to stop a caller passing an arbitrary function. Parametrising
over `K` instead of over the term removes that cost: `Runs.globalRun K` fixes the
flat and the inputs function by construction, so there is nothing left to
constrain and `GlobalPreppedAt` is DELETED.

DISCHARGED AT ALL THREE PUBLISHED GLOBAL BUDGETS (this closes audit **F7**, which
recorded the 1600 case as open in this file):
* `K_global_nonmember = 1600` — `WSC.NonVacuity.globalNonVacuous_at_1600`, from
  `WSC.P5ShapedWitness` (SHAPE G1, K = 1541), `native_decide`.
* `K_global_member = 3300` — `WSC.NonVacuity.globalNonVacuous_at_3300`, from
  `WSC.P6ShapedWitness` (SHAPE G6, K = 2837).
* `K_global = 4400` — `WSC.NonVacuity.globalNonVacuous_at_4400`, from
  `WSC.P1ShapedWitness.ctxOk` (SHAPE T1, K = 2603).

WHAT THE OLD STATUS BLOCK SAID, and what of it still stands: it recorded the
symbolic vacuity probe over `appliedGlobal1600.prop` as OPEN (no verdict in 87
minutes, `WSC/Props/P5_NonMember.lean:548`) and correctly refused to let `exec`
acceptance discharge a `prop`-level claim, since `#prep_uplc` emits the two as
separate terms with no proved equality. Both facts are UNCHANGED. They no longer
block this predicate because the predicate no longer mentions `prop`: the
witnesses and the statement are now about the same term, which was the entire
content of the mismatch. The `prop`-level claim itself is separately available as
`ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600` (`blaster`, `sorryAx`). -/
def GlobalNonVacuous (K : Nat) : Prop :=
  ∃ (pcs : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx = true ∧ isSuccessful (Runs.globalRun K pcs ctx)

/-- Non-vacuity of the seize validator at budget `K`: some ledger-normalized
rewarding context is ACCEPTED by `Runs.seizeRun K`.

**RESTATED BY TASK A1, and DISCHARGED — reversing a "MEASURED FALSE" entry.**
The previous form named `appliedSeize.prop` (budget 600) and was MEASURED FALSE
there and at 1,000 (E2 spike vacuity probes returned `Valid` for the negation),
with no affordable prep budget able to reach the cheapest accepting run of 3,002
steps (2,570 as published pre-fix; re-measured by task C3). Task U2
recorded the resulting prep-naming defect and deliberately left it
alone, since the seize bridge was unusable by design and had no consumer.

Both of those facts were about `#prep_uplc` cost, and neither survives the move
to `Runs.seizeRun K`, which is not a prep. DISCHARGED at `K_seize = 3800` by
`WSC.NonVacuity.seizeNonVacuous_at_3800`, from `WSC.P2ShapedWitness.ctxAccept`
(SHAPE S1, K = 3004, `validRewardingContext` in full).

STILL TRUE, and the reason this is a smaller win than it looks: nothing consumes
`LR_BUDGET_seize`, `WithinBudget` has no seize clause, and P2's leaf obligation
is open (audit F1). See `K_seize`'s docstring. -/
def SeizeNonVacuous (K : Nat) : Prop :=
  ∃ (pcs : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx = true ∧ isSuccessful (Runs.seizeRun K pcs ctx)

/-- **LR_BUDGET_base**: for a transaction on which the base validator's real run
halts within `K` CEK steps, ledger acceptance is EQUIVALENT to
`isSuccessful (Runs.baseRun K …)`.

**RESTATED BY TASK A1** — see this section's RESTATEMENT block. The right-hand
side is now a plain Lean definition (imported flat + audited inputs function +
`cekExecuteProgram`), so nothing on this path passes through `Optimize.main`,
`#prep_uplc` or `PropExecFaithful`. `K` is explicit rather than hard-wired to
`K_base`, for uniformity with the other three; the only use site
(`Composition.p3_lifted`) instantiates it at `K_base` and its non-vacuity
hypothesis is `Composition.baseNonVacuous`.

WHAT IS KERNEL-CHECKED vs WHAT THIS AXIOM ASSERTS — the distinction a reviewer
must keep:
* KERNEL-CHECKED, no axiom and no solver: that `Runs.baseRun 600` is the imported
  `programmableLogicBase` flat applied to `baseInputs` under a 600-step meter
  (read the definition), and that the shaped base prep's executable term equals
  it on the denoted context (`ShapeBridge.exec_B1`, `rfl`).
* MACHINE-CHECKED by `blaster` (verdict, `admit`-closed): that an accepting
  `Runs.baseRun 600` implies P3's postcondition
  (`WSC.P3_base_requires_global_or_seize_run`, `WSC/Props/P3_BaseRun.lean`).
* ASSERTED HERE, and not provable in this substrate: that ledger acceptance
  (`NodeAcceptsBase`) coincides with the METERED run halting, for transactions
  whose UNMETERED run halts within `K`. The gap is `runSteps` monotonicity —
  terminal states are returned as-is; fuel-0 becomes `Error` only in a
  non-terminal state (`PlutusCore/UPLC/CekMachine.lean:229-241`). Formalizing
  that inside Lean would discharge this axiom; it is not available today
  (SPIKE-FINDINGS: "budget monotonicity is a meta-theorem SMT doesn't have").
  `nodeStepsBase` is the same counter `#prep_uplc` bounds, which is what makes
  the hypothesis the right one. -/
axiom LR_BUDGET_base :
  ∀ (K : Nat),
    BaseNonVacuous K →
    ∀ (g s : Credential) (ctx : ScriptContext),
      OnChain ctx → nodeStepsBase g s ctx ≤ K →
      (NodeAcceptsBase g s ctx ↔ isSuccessful (Runs.baseRun K g s ctx))

/-- **LR_BUDGET_minting**: same statement shape, over `Runs.mintingRun K`.

**RESTATED BY TASK A1** from `appliedMinting900.prop` (task U2's repointing, which
itself corrected a bridge that named the machine-checked-vacuous budget-600 prep)
to the run form, and made `K`-parametric.

USABLE AT TWO PUBLISHED BUDGETS, both with a PROVED non-vacuity hypothesis:
* `K := K_mint = 900` — burn-only-sized minting, i.e. SHAPES M1/M2 and
  `WSC/Props/P4_Minting.lean`. Hypothesis: `Composition.mintingNonVacuous`.
* `K := K_mint_custody = 2500` — the `Local` / `DelegateTransfer` /
  `DelegateSeize` arms (K = 1,681 / 1,257 / 1,466), i.e. SHAPES L1/L2/DT1/DS1.
  Hypothesis: `NonVacuity.mintingNonVacuous_at_2500`. **This is the bridge that
  did not exist before A1** (`WSC/Composition.lean` §9.5, audit F12's last
  bullet): the shaped modules prep at 2500 and no unshaped 2500 prep is
  affordable, so there was no term to state it over.

SCOPE, unchanged and still binding: the bound is per-transaction-shape and says
nothing about arbitrarily large minting transactions. `WithinBudget`'s minting
clause is still `K_mint = 900` — see `K_mint_custody`'s docstring for why raising
it is a composition-core change and not part of A1.

AUDIT / DISCHARGE of the axiom itself: identical to `LR_BUDGET_base`. -/
axiom LR_BUDGET_minting :
  ∀ (K : Nat),
    MintingNonVacuous K →
    ∀ (pcs : CurrencySymbol) (mlh : ScriptHash) (ctx : ScriptContext),
      OnChain ctx → nodeStepsMinting pcs mlh ctx ≤ K →
      (NodeAcceptsMinting pcs mlh ctx ↔ isSuccessful (Runs.mintingRun K pcs mlh ctx))

/-- **LR_BUDGET_global**: same statement shape, over `Runs.globalRun K`.

**RESTATED BY TASK A1, AND SIMPLIFIED.** The history matters because two separate
defects were fixed by two separate tasks:

1. The ORIGINAL axiom read `GlobalNonVacuous → ∀ …, nodeStepsGlobal pcs ctx ≤
   K_global → (NodeAcceptsGlobal … ↔ isSuccessful (appliedGlobal.prop pcs ctx))`:
   it named the **budget-600** prep while quoting `K_global`. Its non-vacuity
   hypothesis is MEASURED FALSE at 600 (`WSC.global_vacuity_probe_600`,
   `WSC/Prep/Global.lean:70-84`), so it applied to nothing; and worse, for
   `K > 600` the right-hand side is `Error` (budget exhaustion) on every
   transaction costing more than 600 steps, so the equivalence would have
   asserted `NodeAcceptsGlobal … ↔ False`.
2. Task U2 fixed that by making the PREPPED TERM and its budget explicit
   parameters, with a `GlobalPreppedAt globalProp K` side condition — a NEW
   abstract declaration — to stop a caller substituting an arbitrary function for
   `globalProp`.
3. Task A1 parametrises over `K` ONLY. `Runs.globalRun K` pins the flat and the
   inputs function in its own definition, so the side condition has nothing left
   to say and **`GlobalPreppedAt` is deleted**. The prep/budget mismatch of (1)
   is still excluded by construction, since the `K` in the step bound is the same
   `K` the run meters.

USABLE AT ALL THREE PUBLISHED GLOBAL BUDGETS, each with a PROVED non-vacuity
hypothesis (`NonVacuity.globalNonVacuous_at_{1600,3300,4400}`): 1600 for P5 /
SHAPE G1, 3300 for P6 / SHAPE G6, 4400 for P1 / SHAPES T1/T2/T6/T7.

**THE OLD `LR_BUDGET_global_shaped` TODO IS WITHDRAWN, and what replaced it is
NOT as strong as that TODO's name suggests.** The TODO said a shaped leaf needed
this axiom at the shaped prep's budget, which did not exist. It now exists at
every budget. What a shaped leaf still owes is (i) `ShapeBridge.bridge_<S>` to get
from `appliedXShaped.prop` to `Runs.globalRun K` — `blaster`-verified, Tier B,
carrying `WSC/SHAPE-BRIDGE.md` §5.2's health warning and `PropExecFaithful` — and
(ii) shape COVERAGE, which nothing in this library supplies (audit F2). Neither
is provided by this axiom and neither is closed by A1.

AUDIT / DISCHARGE of the axiom itself: identical to `LR_BUDGET_base`. -/
axiom LR_BUDGET_global :
  ∀ (K : Nat),
    GlobalNonVacuous K →
    ∀ (pcs : CurrencySymbol) (ctx : ScriptContext),
      OnChain ctx → nodeStepsGlobal pcs ctx ≤ K →
      (NodeAcceptsGlobal pcs ctx ↔ isSuccessful (Runs.globalRun K pcs ctx))

/-- **LR_BUDGET_seize**: same statement shape, over `Runs.seizeRun K`.

**RESTATED BY TASK A1, and the accompanying "READ THIS AS UNAVAILABLE" warning is
WITHDRAWN — with a replacement warning that is narrower but still real.**

The previous entry said: "There is no `K_seize`: the statement is quantified over
an arbitrary `K` and gated on a non-vacuity hypothesis that is MEASURED FALSE at
every affordable prep budget. Read this as 'the seize bridge is UNAVAILABLE'."
That was accurate for a right-hand side of `appliedSeize.prop` — see
`SeizeNonVacuous` for the measurements. It listed three routes to availability,
of which A1 takes the second in a stronger form than anticipated: shaped contexts
with per-shape measured K, but with the LEDGER side stated on `Runs.seizeRun K`
so no seize prep is needed at all.

STATUS NOW: `K_seize = 3800` is published, `SeizeNonVacuous K_seize` is a THEOREM
(`NonVacuity.seizeNonVacuous_at_3800`, from SHAPE S1's K = 3004 witness), and this
assumption can be applied.

THE REPLACEMENT WARNING: nothing applies it. `WSC/Composition.lean` has no seize
clause in `WithinBudget` and never invokes this axiom; `LeafSet.p2` is open
(audit F1); and 3800 does NOT cover the 2-input accepting seize golden
(**5,079** steps; 4,647 pre-fix). Read this as "the seize bridge now exists and is non-vacuous, and
is not yet wired into anything".

AUDIT / DISCHARGE of the axiom itself: identical to `LR_BUDGET_base`. -/
axiom LR_BUDGET_seize :
  ∀ (K : Nat),
    SeizeNonVacuous K →
    ∀ (pcs : CurrencySymbol) (ctx : ScriptContext),
      OnChain ctx → nodeStepsSeize pcs ctx ≤ K →
      (NodeAcceptsSeize pcs ctx ↔ isSuccessful (Runs.seizeRun K pcs ctx))

/-! # §Dir — DIRECTORY well-formedness (ADDENDUM E4)

The single named top trust assumption, ESCAPE-CRITICAL: P5's strength is exactly
DirWF's strength. `U10` — formalizing `mkDirectoryNodeMP` at UPLC and proving
DirWF preservation per insert, then lifting over history — is what converts this
from ASSUMED to PROVEN, and is the highest-assurance-ROI follow-on in the plan
(ARCHITECTURE.md §5.4 DEFERRED-2, §7 U10). -/

/-- Key-uniqueness among the authentic directory nodes of one `TxOut` list.

LIMITATION (stated, not hidden): outputs carry no `TxOutRef`, so for outputs
this is the weaker "equal as `TxOut`" form — two byte-identical authentic
outputs would satisfy it. The `TxOutRef`-keyed statement belongs in
`Composition.lean` over a `Ledger`. For inputs and reference inputs the
`TxInInfo` form below is used instead, which does include the `TxOutRef`. -/
def dirKeyUniqueOuts (dirCS : CurrencySymbol) (os : List TxOut) : Prop :=
  ∀ o₁ ∈ os, ∀ o₂ ∈ os,
    authenticDirNode dirCS o₁ → authenticDirNode dirCS o₂ →
    dirNodeKey o₁ = dirNodeKey o₂ → o₁ = o₂

/-- Key-uniqueness among the authentic directory nodes of one `TxInInfo` list
(includes the `TxOutRef`, so this is genuine UTxO-level uniqueness). -/
def dirKeyUniqueIns (dirCS : CurrencySymbol) (ts : List TxInInfo) : Prop :=
  ∀ t₁ ∈ ts, ∀ t₂ ∈ ts,
    authenticDirNode dirCS t₁.txInInfoResolved → authenticDirNode dirCS t₂.txInInfoResolved →
    dirNodeKey t₁.txInInfoResolved = dirNodeKey t₂.txInInfoResolved → t₁ = t₂

/-! ### The interval-partition vocabulary (ADDENDUM E4 conjunct (iv), added by
task V4)

`WSC/Props/P1_Transfer.lean`'s `DirWF_partition_conjunct_missing` recorded the
gap this section closes: without an interval statement, key-uniqueness does NOT
forbid a covering node for a registered `cs` (the two nodes have *different*
keys), so "an authentic node covering `cs` exists ⟹ `cs` is not registered" —
the bridge P5 and P1 both need (ADDENDUM E3) — was not derivable from the axiom
base. -/

/-- An authentic directory node of `os` is keyed exactly `cs` — the ground-truth
"`cs` is registered in the snapshot `os`". -/
def registeredIn (dirCS cs : CurrencySymbol) (os : List TxOut) : Prop :=
  ∃ o ∈ os, authenticDirNode dirCS o = true ∧ dirNodeKey o = some cs

/-- Some authentic directory node of `os` STRICTLY covers `cs`
(`key < cs < next`) — the ground-truth form of the exemption witness that P5's
postcondition produces (ADDENDUM E3). -/
def coveringIn (dirCS cs : CurrencySymbol) (os : List TxOut) : Prop :=
  ∃ o ∈ os, authenticDirNode dirCS o = true ∧
    ∃ k n, dirNodeKey o = some k ∧ dirNodeNext o = some n ∧ k < cs ∧ cs < n

/-- **The interval-partition property, non-overlap half.** No authentic
directory node's KEY lies strictly inside another authentic node's `(key, next)`
interval.

This is the exact strength `covering_node_excludes_registration` consumes, and
nothing more. TWO deliberate scope decisions, both recorded rather than silently
made:

* **The COVERAGE half is not asserted.** ARCHITECTURE.md §5.3's
  `directory_partition` row says the intervals "partition the key space", which
  also asserts that every non-key symbol IS covered by some node. That half is a
  *liveness* fact (it says an honest NonMember proof can always be built); no
  safety obligation in this library consumes it, so asserting it would only
  enlarge the trust surface. U10 would prove both halves at once.
* **Sentinel-boundedness is not asserted** for the same reason: `TS4`
  (`key < next` for every authentic node, itself a consequence of `DIRWF` (iii))
  is all the covering-interval arithmetic needs. -/
def dirNoOverlap (dirCS : CurrencySymbol) (os : List TxOut) : Prop :=
  ∀ o₁ ∈ os, ∀ o₂ ∈ os,
    authenticDirNode dirCS o₁ = true → authenticDirNode dirCS o₂ = true →
    ∀ k₁ n₁ k₂ : CurrencySymbol,
      dirNodeKey o₁ = some k₁ → dirNodeNext o₁ = some n₁ → dirNodeKey o₂ = some k₂ →
      ¬ (k₁ < k₂ ∧ k₂ < n₁)

/-- The UTxOs a transaction shows that are **pre-state** UTxOs: resolved
reference inputs and resolved spent inputs. Both come out of the ledger's UTxO
set as it was *before* the transaction; the produced outputs do NOT.

WHY THE DISTINCTION IS LOAD-BEARING (finding, task V4): stating the non-overlap
conjunct over `dirCandidates` (which includes outputs) would make it **FALSE for
every directory INSERT**. An insert spends the node `(key = k, next = n)` and
produces `(k, cs)` together with `(cs, n)`; the spent input still carries
`next = n`, so `k < cs < n` holds for a visible node while `cs` is the key of
another visible node — precisely the configuration `dirNoOverlap` forbids. A
consistent snapshot is required, and `dirPreState` is the consistent snapshot a
`ScriptContext` actually exposes. -/
def dirPreState (ctx : ScriptContext) : List TxOut :=
  (ctx.scriptContextTxInfo.txInfoReferenceInputs.map (·.txInInfoResolved)) ++
  (ctx.scriptContextTxInfo.txInfoInputs.map (·.txInInfoResolved))

/-- `registeredIn` is monotone in the snapshot. -/
theorem registeredIn_mono {dirCS cs : CurrencySymbol} {os os' : List TxOut}
    (hsub : ∀ o ∈ os, o ∈ os') (h : registeredIn dirCS cs os) :
    registeredIn dirCS cs os' := by
  obtain ⟨o, ho, ha, hk⟩ := h
  exact ⟨o, hsub o ho, ha, hk⟩

/-- `coveringIn` is monotone in the snapshot. -/
theorem coveringIn_mono {dirCS cs : CurrencySymbol} {os os' : List TxOut}
    (hsub : ∀ o ∈ os, o ∈ os') (h : coveringIn dirCS cs os) :
    coveringIn dirCS cs os' := by
  obtain ⟨o, ho, ha, hc⟩ := h
  exact ⟨o, hsub o ho, ha, hc⟩

/-- **THE BRIDGE LEMMA (ADDENDUM E3), snapshot form — A THEOREM, not an axiom.**
*In a snapshot whose authentic directory nodes do not overlap, a node that
strictly covers `cs` witnesses that `cs` is NOT registered in that snapshot.*

Proof: a registration of `cs` is an authentic node keyed `cs`; the covering node
is an authentic node whose interval strictly contains `cs`; `dirNoOverlap`
applied to the pair is the contradiction. -/
theorem covering_excludes_registeredIn
    {dirCS cs : CurrencySymbol} {os : List TxOut}
    (hno : dirNoOverlap dirCS os) (hcov : coveringIn dirCS cs os) :
    ¬ registeredIn dirCS cs os := by
  rintro ⟨o₂, ho₂, ha₂, hk₂⟩
  obtain ⟨o₁, ho₁, ha₁, k, n, hk, hn, hlt, hgt⟩ := hcov
  exact hno o₁ ho₁ o₂ ho₂ ha₁ ha₂ k n cs hk hn hk₂ ⟨hlt, hgt⟩

/-- `IsRegistered` (the tx-visible registry projection, a `Bool` scan of the
reference inputs) implies the ground-truth `registeredIn` over the resolved
reference inputs. -/
theorem registeredIn_of_IsRegistered {dirCS cs : CurrencySymbol} :
    ∀ (refs : List TxInInfo), IsRegistered dirCS refs cs = true →
      registeredIn dirCS cs (refs.map (·.txInInfoResolved))
  | [], h => by simp [IsRegistered] at h
  | t :: rest, h => by
      simp only [IsRegistered, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨ha, hk⟩ | hrest
      · exact ⟨t.txInInfoResolved, by simp, ha, hk⟩
      · obtain ⟨o, ho, hb⟩ := registeredIn_of_IsRegistered rest hrest
        exact ⟨o, by simp only [List.map_cons, List.mem_cons]; exact Or.inr ho, hb⟩

/-- **DirWF (ADDENDUM E4)**: the directory linked list is well-formed in the
view of one transaction. FOUR conjuncts, all binding per the adversarial
review (conjunct (iv) added by task V4 — see the CORRECTION LOG entry 7):

**(i) INSERT-ONLY / NO KEY REMOVAL** (⟹ `L-monotone`; no deregistration
attack; ESCAPE-CRITICAL). Every authentic directory node CONSUMED by the
transaction reappears as an authentic OUTPUT node carrying the same key, so a
key is never deleted or rewritten. Without it, an adversary could spend the node
keyed `cs`, drop it, and then have `cs` classified NonMember by a covering node.

**(ii) GLOBAL KEY-UNIQUENESS** across all authentic nodes. Stated here as its
per-transaction projection: uniqueness within the reference inputs, within the
spent inputs, and within the produced outputs. Without it, one `cs` could have
both a keyed node (Member) and a covering node (NonMember) — the Tier-2.3
minting↔global consistency hazard.

**(iii) NFT-NAME = NODE-KEY DATUM BINDING** (ESCAPE-CRITICAL). Any UTxO the
transaction can see that carries a genuine `directoryNodeCS` token IS an
authentic node: its datum decodes, satisfies `key < next`, and its
`directoryNodeCS` token map is EXACTLY `[(key, 1)]`. This is what makes the
issuance policy's datum-free `hasNodeNFT` check (Issuance.hs:154-157) sound, and
what makes a covering-interval witness (`key < cs < next`) meaningful at all.

**(iv) INTERVAL NON-OVERLAP** (ESCAPE-CRITICAL; ADDENDUM E4's "partition",
§5.3's `directory_partition`; ADDED BY TASK V4). No authentic node's key lies
strictly inside another authentic node's `(key, next)` interval, over the
transaction's PRE-STATE snapshot (`dirPreState`: resolved reference inputs and
resolved spent inputs — NOT the outputs, see `dirPreState`'s docstring for why
including them would make the conjunct false for every insert). This is what
`covering_node_excludes_registration` consumes, and it is the reason
"an authentic node covering `cs` exists ⟹ `cs` is not registered" is now a
THEOREM rather than a missing link. Without it, key-uniqueness (ii) is not
enough: a keyed node and a covering node for the same `cs` have DIFFERENT keys,
so (ii) permits exactly the deregistration-by-covering-proof escape.

WHY UNAVOIDABLE: none of the four imported validators constrains what the
directory looks like; they only authenticate individual nodes by NFT. The
invariant is maintained by the directory minting policy + directory spending
script, which are OUTSIDE this formalization.

AUDIT / DISCHARGE: U10 — import `mkDirectoryNodeMP.flat`, prove per-insert
preservation of (i)+(ii)+(iii)+(iv) at UPLC, lift over history. (i), (iii) and
(iv) are the escape-critical conjuncts and appear in the top-claim docstring
(`WSC/Composition.lean`). -/
def DirWF (hp : HonestParams) (ctx : ScriptContext) : Prop :=
  -- (i) insert-only / no key removal
  (∀ t ∈ ctx.scriptContextTxInfo.txInfoInputs,
     authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
     ∃ o ∈ ctx.scriptContextTxInfo.txInfoOutputs,
       authenticDirNode hp.directoryNodeCS o ∧
       dirNodeKey o = dirNodeKey t.txInInfoResolved) ∧
  -- (ii) global key-uniqueness (per-tx projection)
  dirKeyUniqueIns hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoReferenceInputs ∧
  dirKeyUniqueIns hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoInputs ∧
  dirKeyUniqueOuts hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoOutputs ∧
  -- (iii) NFT-name = node-key datum binding, over EVERY visible UTxO
  (∀ o ∈ dirCandidates ctx,
     hasCurrencySymbol hp.directoryNodeCS o.txOutValue →
     ∃ d, dirNodeDatum o = some d ∧
          d.key < d.next ∧
          csTokens hp.directoryNodeCS o.txOutValue = some [(Data.B d.key, Data.I 1)]) ∧
  -- (iv) interval non-overlap over the PRE-STATE snapshot (task V4)
  dirNoOverlap hp.directoryNodeCS (dirPreState ctx)

/-- Conjunct (iv) of `DirWF`, projected out. -/
theorem DirWF.noOverlap {hp : HonestParams} {ctx : ScriptContext} (h : DirWF hp ctx) :
    dirNoOverlap hp.directoryNodeCS (dirPreState ctx) := h.2.2.2.2.2

/-- **DIRWF**: `DirWF` holds for every on-chain transaction of the audited
deployment. THE single named top trust assumption; ESCAPE-CRITICAL.

WHY UNAVOIDABLE: see `DirWF`. AUDIT / DISCHARGE: U10 (directory minting policy
at UPLC). Until then, published claims must say "P5 is as strong as DirWF". -/
axiom DIRWF :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx → DirWF hp ctx

/-- **`covering_node_excludes_registration` (ADDENDUM E3), per-transaction form
— PROVED AS A THEOREM FROM `DIRWF`.**

*If some pre-state UTxO the transaction shows is an authentic directory node
whose `(key, next)` interval strictly covers `cs`, then `cs` is NOT registered in
the transaction's reference-input view.*

This is the bridge that `WSC/Props/P1_Transfer.lean`'s
`DirWF_partition_conjunct_missing` reported as absent, and it is exactly what
turns P5's postcondition (a covering-node witness, E3) into the composition's
"`cs` cannot be exempted because it is registered" — by contraposition.

SCOPE, stated precisely: the conclusion is about the tx-visible registry
projection `IsRegistered`, which is sound for POSITIVE registration facts only
(see `IsRegistered`'s audit note). The LEDGER-level form — "`cs ∉ R L`" — needs a
`Ledger` type and is proved in `WSC/Composition.lean`
(`covering_excludes_ledger_registration`) from the ledger-level non-overlap
the `DIRWF_L` axiom there. Both bottom out in the SAME conjunct (iv) and the SAME
discharge (U10). -/
theorem covering_node_excludes_registration
    (hp : HonestParams) (ctx : ScriptContext) (cs : CurrencySymbol)
    (hwf : DirWF hp ctx)
    (hcov : coveringIn hp.directoryNodeCS cs (dirPreState ctx)) :
    IsRegistered hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoReferenceInputs cs = false := by
  by_cases h : IsRegistered hp.directoryNodeCS
      ctx.scriptContextTxInfo.txInfoReferenceInputs cs = true
  · exact absurd
      (registeredIn_mono
        (fun o ho => by
          simp only [dirPreState, List.mem_append]; exact Or.inl ho)
        (registeredIn_of_IsRegistered _ h))
      (covering_excludes_registeredIn hwf.noOverlap hcov)
  · simpa using h

/-- The same bridge, taking the deployment axiom instead of a `DirWF` hypothesis:
for a real transaction of the audited deployment, a covering node excludes
registration. -/
theorem covering_node_excludes_registration_onchain
    (hp : HonestParams) (ctx : ScriptContext) (cs : CurrencySymbol)
    (hdep : Deployed hp) (hoc : OnChain ctx)
    (hcov : coveringIn hp.directoryNodeCS cs (dirPreState ctx)) :
    IsRegistered hp.directoryNodeCS ctx.scriptContextTxInfo.txInfoReferenceInputs cs = false :=
  covering_node_excludes_registration hp ctx cs (DIRWF hp ctx hdep hoc) hcov

/-! ### TS3 / TS4 / TS5 — directory facts kept under their historical names

These three are DIRECTORY facts (not trusted-setup — see the numbering-collision
table in the header). TS3 and TS4 are now CONSEQUENCES of `DIRWF` conjunct (iii);
they are retained as separately named axioms so that a proof needing only "the
datum decodes" or only "key < next" cites exactly that, mirroring how LR1–LR7
relate to `LR_CTX`. The redundancy is intentional and harmless — same trust
base, and the same discharge (U10). -/

/-- **TS3 (directory-datum well-formedness)** — DIRECTORY. Every authentic
directory node visible to an on-chain transaction carries an inline datum that
decodes as a `DirectorySetNode`.

Consequence of `DIRWF` (iii). Delegates to the directory node minting policy
(nodes are only created with well-formed datums) and the directory spending
script (shape is preserved). Discharge: U10. -/
axiom TS3 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      (dirNodeDatum t.txInInfoResolved).isSome

/-- **TS4 (linked-list order)** — DIRECTORY. Every authentic directory node's
datum satisfies `key < next` (head sentinel key = "" and tail sentinel
next = 0xff…ff included — PTokenDirectory.hs:216-223).

WHY IT MATTERS: this is what makes a covering-interval witness
(`key < cs < next`) meaningful, i.e. it is load-bearing for P5.

Consequence of `DIRWF` (iii). Delegates to the directory minting policy's insert
rule. Discharge: U10. -/
axiom TS4 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      ∀ d, dirNodeDatum t.txInInfoResolved = some d → d.key < d.next

/-- **TS5 (directory-NFT custody)** — DIRECTORY (⊂ §5.3 `ts_singleton_config`).
Directory state tokens never sit at outputs other than the directory spending
script's; in particular an authentic directory node's FIRST non-Ada policy is
the directory policy, so the validators' cheap `phasCSH` authentication
(ProgrammableLogicBase.hs:754-757) agrees with ground-truth membership
(`authenticDirNode`).

WHY IT MATTERS: it is the bridge between the validators' cheap shape check and
this file's ground-truth `hasCurrencySymbol` definition. NOT a consequence of
`DIRWF` — that constrains WHICH tokens a node holds, this constrains WHERE the
tokens can be.

Delegates to the directory minting policy + directory spending script custody
rules. Discharge: U10. -/
axiom TS5 :
  ∀ (hp : HonestParams) (ctx : ScriptContext),
    Deployed hp → OnChain ctx →
    ∀ t ∈ ctx.scriptContextTxInfo.txInfoReferenceInputs,
      authenticDirNode hp.directoryNodeCS t.txInInfoResolved →
      match t.txInInfoResolved.txOutValue with
      | _ :: (Data.B cs, _) :: _ => cs = hp.directoryNodeCS
      | _ => False

end WSC
