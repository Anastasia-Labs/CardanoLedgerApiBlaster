/-
WSC/Honest.lean — the honest-deployment vocabulary (arch §4.2) and the FULL
axiom base of the WSC containment campaign.

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

RECONSTRUCTION FLAG (retained from the previous revision): the binding
`arch-final.md` was not available when the axiom STATEMENTS were first drafted.
`WSC/ARCHITECTURE.md` (base document + ADDENDUM v3, canonical on
`wsc-containment-proofs`) is now the reference used by this revision, and the
E1/E4/E5/E6 allocations below were re-read from it verbatim.
-/
import CardanoLedgerApi.V3
import WSC.Imports
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
| J | `txInfoFee > 0` (:1201) | `FeeTooSmallUTxO` (`Conway/Rules/Utxo.hs:85`) with mainnet `minFeeB = 155381 > 0` | **JUSTIFIED, PARAMETER-DEPENDENT** — it is a protocol-parameter fact, not a pure rule. No WSC proof uses it. NOTE: all 13 goldens have `fee = 0`, so **no golden satisfies `validXContext`** (see the empirical row-set below). |
| K | `validMintValue`: ada-free, ascending, quantities ≠ 0 (:801-813) | `transMintValue` over `MultiAsset` (`Conway/TxInfo.hs:540-541`) | **JUSTIFIED at PV11+** (ada-freeness is version-dependent) |
| L | `validWithdrawals`: withdrawals strictly ASCENDING in CLAB's `Credential` order (`validWithdrawals`, V3/Contexts) | `transMap … (unWithdrawals …)` = `unsafeFromList ∘ map ∘ Map.toList` — NO re-sorting (`Conway/TxInfo.hs:544-546, 692-694`); the ledger's key order is `AccountAddress` = (`Network`, `Credential`) with **`ScriptHashObj < KeyHashObj`** (`libs/cardano-ledger-core/src/Cardano/Ledger/Credential.hs:96-99`, `Address.hs:183-191`); `ltCredential` (`V1/Credential.lean`) was **FIXED to that order by task Z1** (it previously had the Plutus order `PubKeyCredential < ScriptCredential`) | **JUSTIFIED** (was ⚠ REFUTED for mixed maps — defect D2, now repaired). Side fact, itself a ledger rule: Plutus' key drops the `Network` component, harmless because `validateWrongNetworkWithdrawal` (`Shelley/Rules/Utxo.hs:181,384`) admits only one network per transaction, on which (`Network`,`Credential`) order restricts to `Credential` order. |
| M | `validRedeemerMap`: redeemers strictly ASCENDING in CLAB's `ScriptPurpose` order (`validRedeemerMap`, V3/Contexts) | `transTxRedeemers = unsafeFromList ∘ mapM … ∘ Map.toList` over `Redeemers` keyed by `PlutusPurpose AsIx` — NO re-sorting (`Babbage/TxInfo.hs:217-221`, used for V3 at `Conway/TxInfo.hs:499,512`); ledger tag order is **`ConwaySpending < ConwayMinting < ConwayCertifying < ConwayRewarding < ConwayVoting < ConwayProposing`** (`Conway/Scripts.hs:202-213`, derived `Ord`); `ltScriptPurpose` (`V3/Contexts.lean`) was **FIXED to that order by task Z1** (it previously had the Plutus constructor order `Minting < Spending < Rewarding < Certifying < …`) | **JUSTIFIED** (was ⚠⚠ REFUTED for every WSC issuance transaction — defect D1, now repaired; that defect is why every `validMintingContext` theorem was vacuous on its own class). Side fact: INTRA-kind, the ledger's `AsIx` index enumerates an already-sorted collection and each Plutus key's leading component sorts the same way (inputs by `TxIn`≡`ltTxOutRef`; policies by `PolicyID`≡`CurrencySymbol`; withdrawals by `Credential` per row L; `Certifying`/`Proposing` compare the index itself; `Voting` by `Voter`, whose ledger `Ord` (`Conway/Governance/Procedures.hs:338-342`) matches `ltVoter`). |
| N | `validTxRange`: validity range non-empty (:1204, `V1/Contexts.lean:964-967`) | `OutsideValidityIntervalUTxO` (`Alonzo/Rules/Utxo.hs:124,519`) — the current slot lies inside, hence non-empty | **JUSTIFIED** |
| O | `validSigners`: required signers strictly ascending (:1205, `V1/Contexts.lean:977-984`) | `Set.toList` of `KeyHash` (`transTxBodyReqSignerHashes`, `Alonzo/Plutus/TxInfo.hs:312`) | **JUSTIFIED** |
| P | `validDatumMap`: datum witnesses ascending by hash (:1207, `V1/Contexts.lean:995-1002`) | `Map.toList` of `TxDats` (`transTxWitsDatums`, `Alonzo/Plutus/TxInfo.hs:316`) | **JUSTIFIED** |
| Q | `validVoterMap`, `validTreasuryAmount`, `validTreasuryDonation` (:1208-1210) | `transVotingProcedures` over ordered maps (`Conway/TxInfo.hs:696-699`); treasury fields are `Maybe Coin` and `Nothing`/positive by construction (`:518-523`) | **JUSTIFIED**; unused by WSC |
| R | `isBalanced` (:1211, :1150-1154) | Conway `UTXO` `ValueNotConservedUTxO` | **JUSTIFIED** |

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

* `validXContext` = **false for all 13** — every golden has `txInfoFee = 0`
  (row J). The goldens are builder-produced, not chain-captured
  (`WSC/goldens/MANIFEST.md` "Extraction provenance"), so this is a GOLDEN-SUITE
  GAP, not a ledger finding. **Consequence: no golden can currently serve as a
  `validXContext` anti-vacuity witness; the only such witness in the library is
  the hand-built `WSC.P3Witness.ctx` (WSC/Props/P3_Base.lean:149).**
* `validRedeemerMap` was false for the 2 minting goldens with purposes
  `[Spending, Minting, Rewarding, Rewarding, Rewarding]` — exactly row M's
  refutation, reproduced independently. **Since task Z1 fixed `ltScriptPurpose`
  both goldens PASS `validRedeemerMap`** and their only failing conjunct is the
  zero fee (row J); machine-checked by `WSC/Goldens/Audit.lean`'s
  `fail_mint_burnonly`, `fail_mint_delegate_transfer_topup` and
  `no_purpose_kind_order_violation_remains`.
* `validWithdrawals` = false for the 3 seize goldens: their two script
  credentials are emitted DESCENDING (`0x40…` before `0x14…`), a builder
  artifact (the builder does not sort withdrawals), which also makes their
  `Rewarding` redeemer entries unsorted. This is UNCHANGED by task Z1's D2 fix,
  and necessarily so: both credentials are SCRIPT credentials, the case where the
  old and new `Credential` orders agree, so the attribution of this failure to
  the builder rather than to CLAB is confirmed rather than disturbed by the fix.
* `validOutputs` = false for the 2 accepting seize goldens: the residual
  (seized-tokens) output carries NO ada entry at all
  (`[(cs=1b…, [(tn=3063, 1)])]`), which min-ada forbids on chain — again a
  builder artifact, and it is row H's ledger rule that rules it out.
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

WHAT WAS WRONG BEFORE (fixed here): the axioms quantified over `txSize ctx ≤ K`
— a transaction-SIZE proxy whose relation to CEK step count is unproven — and
used `∃ K`, which pins nothing and is exactly what a reviewer reads as "any K,
including a vacuous one". The bound is now on CEK steps and the constants are
published `def`s.

MEASUREMENT PROVENANCE for every constant below:
`WSC/goldens/K-MEASUREMENTS.md` (task X1) — true CEK step counts of the 13
golden runs, measured on the fully-applied closed programs
(`WSC/goldens/applied/*.flat`) by iterating the real
`PlutusCore.UPLC.CekMachine.step`, cross-checked to the UNIT against the
ledger's `ExBudget` for all 9 accepting goldens. The prep-cost figures are
K-MEASUREMENTS §5.1. -/

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

/-- **K_base = 600** — the published CEK step bound of the base validator, and
the prep budget of `WSC/Prep/Base.lean`.

* NON-VACUITY WITNESS: golden `programmableLogicBase.base-spend-transfer-tx`
  halts (accepting) in **208** steps (K-MEASUREMENTS §3), i.e. 2.9× inside the
  bound; and the in-library concrete witness `WSC.P3Witness.ctx`
  (WSC/Props/P3_Base.lean:149) is proved accepted at this very budget
  (`P3Witness.exec_accepts`, `P3Witness.prop_accepts`). The mandatory vacuity
  probe `P3_base_vacuity_probe` is **Falsified** at 600.
* PREP COST MEASURED: ~11 s class (K-MEASUREMENTS §5.1 "there is a fixed ≈8 s
  floor"; base's own prep is the cheapest of the four).
* SHAPE COVERED: `K_max` over accepting base goldens is also 208, so 600 covers
  every base-spend shape in the golden suite with margin.

CAVEAT: a bound calibrated on these shapes says nothing about arbitrarily large
transactions; K-MEASUREMENTS §4 is explicit that per-shape K scales with
input/output/policy counts. -/
def K_base : Nat := 600

/-- **K_mint = 900** — the published CEK step bound for the issuance policy.

* NON-VACUITY WITNESS: golden `programmableTokenMinting.mint-burnonly` halts
  (accepting) in **784** steps (K-MEASUREMENTS §3), so 900 admits an accepting
  run; 600 does NOT (600 < 784), which is why the budget must be raised.
* PREP COST MEASURED: **27.6 s** at budget 900 (K-MEASUREMENTS §5.1, measured
  this session; 600 = 11.1 s, 1,200 = 131.6 s, 1,700 never completed in
  48.6 min).
* SHAPE COVERED: burn-only-sized minting transactions. The other two accepting
  minting goldens need 1,257 and 1,681 steps and are OUT of this bound; a prep
  at 1,681 is ≥ 45 min and was measured NOT to complete at 1,700.

PREP THIS CONSTANT IS MATCHED TO (task U2 repair): `WSC/Prep/Minting900.lean`'s
`appliedMinting900`, which is what `LR_BUDGET_minting` below now names and what
every P4/P4a theorem is stated against (`WSC/Props/P4_Minting.lean`). The
budget-600 `appliedMinting` of `WSC/Prep/Minting.lean` is retained only for the
pipeline/decode gate and for the machine-checked vacuity characterization
`WSC.minting600_is_vacuous`; NOTHING is bridged through it.

SUPERSEDED STATUS NOTE (kept for the record): an earlier revision of this
docstring said "`WSC/Prep/Minting.lean` preps at 600 … until a parallel task
raises it, `MintingNonVacuous` below is FALSE". That parallel task landed
(`WSC/Prep/Minting900.lean`), but the two budget bridges were never repointed —
they kept naming the 600 prep. Task U2 repointed them, and
`MintingNonVacuous` is now a THEOREM (`WSC.Composition.mintingNonVacuous`). -/
def K_mint : Nat := 900

/-- **K_global = 4400** — the published CEK step bound for the global
(transfer) validator. **REPUBLISHED FROM 1600 BY TASK U2**; read the CORRECTION
paragraph below before citing the old value.

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
  `validRewardingContext` (`P1ShapedWitness.ctxOk_valid`). Lower bracket:
  `P1ShapedWitness.exec_rejects_at_600` (budget 600 ⟹ `Error`) and
  `K_T1_is_2603` (`Halt` at 2603, `Error` at 2602). So 4400 is genuinely
  accept-capable and the bound is doing work.
* SECOND WITNESS, at the OLD value and on the real off-chain golden:
  `WSC.Witness1600` — HALT at 1600, budget-ERROR at 1553 on
  `WSC/goldens/applied/programmableLogicGlobal.transfer-nonmember-covering-node.flat`.
  That witness is why the 1600 sub-bound below is kept as its own constant.
* PREP COST. Symbolic (fully unshaped) `#prep_uplc` of this validator was
  measured at **2,143 s = 35.7 min, 1.55 GB peak RSS at budget 1600**
  (K-MEASUREMENTS §5.1) and extrapolates to 7-182 YEARS at 3,300+
  (§5.2) — which is why there is NO unshaped 4400 prep and never will be.
  SHAPED prep at 4400 is **1.00 s** (`WSC/Props/Shaped/P1Shaped.lean` header,
  measured; shaped prep is essentially budget-independent — SHAPING-RESULTS
  §2.5).

CONSEQUENCE FOR THE BRIDGES, stated so it cannot be misread: raising this
constant does NOT by itself produce a usable global budget bridge. The only
global prep that exists at 4400 is SHAPED, so `LR_BUDGET_global` below is stated
in PREP-PARAMETRIC form and a shaped instantiation additionally owes the SHAPE
BRIDGE (`WSC/Composition.lean` §9.4). What raising it does is stop
`WithinBudget` from excluding, by construction, every transaction P1 talks
about. -/
def K_global : Nat := 4400

/-- **K_global_nonmember = 1600** — the covering-node / NonMember SUB-BOUND of
the global validator: the budget `WSC/Prep/Global1600.lean` preps at, the budget
P5 is stated at (`WSC/Props/P5_NonMember.lean`, `WSC/Props/Shaped/P5Shaped.lean`
SHAPE G1), and the smallest round budget above the cheapest accepting global
golden's K = 1,554.

Kept as a SEPARATE constant by task U2 rather than folded into `K_global`,
because a budget bridge is only sound at the budget its prep actually bakes: a
transaction taking 3,000 CEK steps satisfies `nodeStepsGlobal … ≤ K_global` but
`appliedGlobal1600.prop` returns `Error` on it, so quoting the 1600 prep at the
4400 bound would assert `NodeAcceptsGlobal ↔ False`. Witness:
`WSC.Witness1600` (HALT at 1600, ERROR at 1553). -/
def K_global_nonmember : Nat := 1600

/-! #### K_seize — DELIBERATELY UNAVAILABLE

There is **no published `K_seize`**, and inventing one would be the single
easiest way to publish a vacuous theorem. The measurements
(K-MEASUREMENTS §4, §5.2):

* the cheapest ACCEPTING seize run costs **2,570** CEK steps
  (`programmableSeize.seize-1-input`); the 2-input golden costs 4,647;
* symbolic `#prep_uplc` on this bytecode at budget 2,000 **never completed** in
  77 minutes, and at 9,000 never completed in 62 minutes (SPIKE-FINDINGS);
  budget 2,570 extrapolates to ≥ 15 days on the measured slope;
* consequently every affordable budget (≤ ~1,000) is provably vacuous — the E2
  spike's vacuity probes at 600 and 1,000 returned **Valid** for
  "no accepting context exists", i.e. accept is UNSAT there.

So instead of a constant, the seize bridge below is stated with an explicit
non-vacuity hypothesis that is currently KNOWN FALSE at the prep in use. The
axiom is therefore unusable by construction until either the prep budget is
raised past 2,570 (not affordable today) or the proof moves to shaped contexts
with per-shape measured K / the source-model route. -/

/-- Non-vacuity of the base prep: some ledger-normalized context is ACCEPTED by
`appliedBase.prop`. **DISCHARGEABLE TODAY** — `WSC.P3Witness` supplies the
witness (`ctx_valid` + `prop_accepts`, WSC/Props/P3_Base.lean:180,197); the
proof term is not assembled here only to keep `Honest.lean` free of a dependency
on `WSC/Props/*` (the intended import direction is Props → Honest). -/
def BaseNonVacuous : Prop :=
  ∃ (g s : Credential) (ctx : ScriptContext),
    validSpendingContext ctx = true ∧ isSuccessful (appliedBase.prop g s ctx)

/-- Non-vacuity of the minting prep **at `K_mint = 900`** — some
ledger-normalized minting context is ACCEPTED by `appliedMinting900.prop`.

**REPOINTED BY TASK U2, and now DISCHARGED.** It used to name
`appliedMinting.prop` (budget 600), whose negation is MACHINE-CHECKED — see
`WSC.minting600_is_vacuous` (`WSC/Props/P4_Minting.lean:380-386`, `✅ Valid` for
"no accepting context exists inside 600 steps"), predicted by the cheapest
accepting run costing 784 steps (K-MEASUREMENTS §3). So the old statement was
FALSE and `LR_BUDGET_minting` could not be applied to anything, while every P4
theorem lives on `appliedMinting900`.

DISCHARGE: `WSC.Composition.mintingNonVacuous` — a THEOREM, from the concrete
`BurnOnly` witness `WSC.P4Witness.ctx` (`ctx_valid : validMintingContext ctx`,
`native_decide`) together with `blaster` on the fully concrete accept goal at
this prep, exactly as `WSC.P3Witness.prop_accepts` does for the base validator.
Corroborating executable brackets: `P4Witness.exec_rejects_at_600` /
`exec_accepts_at_800` / `exec_accepts_at_900`, and the REAL off-chain golden
`programmableTokenMinting.mint-burnonly` (`P4Golden.exec_accepts_at_900`, measured
K = 784). -/
def MintingNonVacuous : Prop :=
  ∃ (pcs : CurrencySymbol) (mlh : ScriptHash) (ctx : ScriptContext),
    validMintingContext ctx = true ∧ isSuccessful (appliedMinting900.prop pcs mlh ctx)

/-- Non-vacuity of a global prep, **prep-parametric** (task U2): some
ledger-normalized rewarding context is ACCEPTED by the prepped term
`globalProp`.

**WHY PARAMETRIC.** The old form named `appliedGlobal.prop` — budget 600, whose
own committed probe `WSC.global_vacuity_probe_600` CHARACTERIZES the budget as
vacuous (`WSC/Prep/Global.lean:70-84`) — while every global theorem lives on
`appliedGlobal1600` (P5, budget 1600) or on a SHAPED prep at 4400 (P1 shapes
T1/T2/T6/T7) or 3300 (P6, SHAPE G6). Hard-wiring any ONE of those here would
either keep a known-vacuous statement or pin the axiom to a single budget and
shape; abstracting the prepped term is what lets a caller name the prep it
actually proved something against, at the budget that prep bakes. See
`GlobalPreppedAt` for the side condition that keeps this honest.

NOT DISCHARGED AT ANY GLOBAL PREP, and this is the honest status:
* at 1600 the SYMBOLIC certificate is OPEN — the vacuity probe over
  `appliedGlobal1600.prop` returned no verdict in 87 minutes
  (`WSC/Props/P5_NonMember.lean` "OBLIGATION STATUS", :548);
* what exists at 1600 is EXECUTABLE evidence about the BYTECODE, not about the
  optimized `prop` term: `WSC.Witness1600` (HALT at 1600, ERROR at 1553 on the
  real golden) and `WSC.P5ShapedWitness.exec_accepts…` over
  `appliedGlobal1600.exec`. `#prep_uplc` emits `prop` (optimized, noncomputable)
  and `exec` (executable) as two SEPARATE terms
  (`PlutusCore/UPLC/PreProcess.lean:43-46`) with no proved equality between
  them, so `exec` acceptance does not discharge this;
* at 4400 the SHAPED preps DO carry solver-side non-vacuity (`P1_T1/T2/T6/T7`
  vacuity probes all `Falsified`) plus concrete accepting instances
  (`P1ShapedWitness`), so a shaped instantiation of this predicate is
  dischargeable — at the cost of the SHAPE BRIDGE (`WSC/Composition.lean` §9.4). -/
def GlobalNonVacuous
    (globalProp : CurrencySymbol → ScriptContext → PlutusCore.UPLC.CekMachine.State) :
    Prop :=
  ∃ (pcs : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx = true ∧ isSuccessful (globalProp pcs ctx)

/-- **`GlobalPreppedAt globalProp K`** — the meta-level side condition of the
prep-parametric global bridge: *`globalProp` is the term `#prep_uplc` produces
from the imported `programmableLogicGlobal` flat with the argument convention
`globalInputs` and CEK step budget `K`.*

WHY IT IS AN AXIOM AND NOT A DEFINITION: it is a statement ABOUT an elaborator
(`#prep_uplc` optimizes the applied `cekExecuteProgram` term through
`Blaster.Optimize`, `PlutusCore/UPLC/PreProcess.lean:36-58`), and the optimized
`prop` is deliberately not kernel-reducible. Nothing inside Lean can compute it.

HOW A USE SITE DISCHARGES IT: by INSPECTION of the `#prep_uplc` line it names —
e.g. `WSC/Prep/Global1600.lean:88` for `appliedGlobal1600` at `K = 1600`, or
`WSC/Shaped/GlobalShapedP1Prep.lean:31` for `appliedGlobalShapedT1` at
`K = 4400`. It is a NEW abstract declaration introduced by task U2, and it is
the price of removing the prep/budget mismatch: it makes the coupling that used
to be silent (`LR_BUDGET_global` said `K_global` while naming a budget-600 term)
into an explicit obligation at every use site.

SHAPED PREPS: for a shaped prep, `globalProp` is the shaped term PARTIALLY
APPLIED to a shape's scalars, so an instantiation additionally owes the SHAPE
BRIDGE of `WSC/Composition.lean` §9.4 — `GlobalPreppedAt` alone does not supply
it. -/
axiom GlobalPreppedAt :
  (CurrencySymbol → ScriptContext → PlutusCore.UPLC.CekMachine.State) → Nat → Prop

/-- Non-vacuity of the seize prep. MEASURED FALSE at 600 and at 1,000 (E2 spike
vacuity probes returned `Valid` for the negation) and NOT reachable at any
affordable budget — see "K_seize — DELIBERATELY UNAVAILABLE" above.

NOTE (task U2, reported not patched): this predicate has the SAME prep-naming
defect the minting and global ones had — it names the budget-600
`appliedSeize.prop` while `WSC/Props/Shaped/P2Shaped.lean` proves P2 over SHAPE
S1 at `appliedSeizeShaped3800` (budget 3800, witnesses K = 3,004 / 3,328). It is
deliberately left alone: unlike the other two, the seize bridge is UNUSABLE by
design (there is no `K_seize`), `WSC/Composition.lean` consumes it nowhere, and
the parametric repair applied to `LR_BUDGET_global` would need a
`SeizePreppedAt` companion for no present consumer. The repair, if a consumer
ever appears, is mechanical and identical. -/
def SeizeNonVacuous : Prop :=
  ∃ (pcs : CurrencySymbol) (ctx : ScriptContext),
    validRewardingContext ctx = true ∧ isSuccessful (appliedSeize.prop pcs ctx)

/-- **LR_BUDGET_base**: for a transaction on which the base validator's real run
halts within `K_base` CEK steps, ledger acceptance is EQUIVALENT to
`isSuccessful (appliedBase.prop …)`.

WHY UNAVOIDABLE: the prepped term is the real bytecode run under a *finite*
step budget; budget exhaustion is indistinguishable from validator failure
inside `isSuccessful`. The axiom is what says "within K, the budgeted verdict is
the node's verdict".

AUDIT / DISCHARGE: `nodeStepsBase` is the same counter `#prep_uplc` bounds, so
the fact is a meta-theorem about `runSteps` (terminal states are returned as-is;
fuel-0 becomes `Error` only in a non-terminal state — `CekMachine.lean:229-241`).
Formalizing that monotonicity inside Lean would discharge it; it is not
available in the current substrate (SPIKE-FINDINGS: "budget monotonicity is a
meta-theorem SMT doesn't have"). -/
axiom LR_BUDGET_base :
  BaseNonVacuous →
  ∀ (g s : Credential) (ctx : ScriptContext),
    OnChain ctx → nodeStepsBase g s ctx ≤ K_base →
    (NodeAcceptsBase g s ctx ↔ isSuccessful (appliedBase.prop g s ctx))

/-- **LR_BUDGET_minting**: same statement shape at `K_mint = 900`, over
`appliedMinting900.prop` — **REPOINTED BY TASK U2** from the budget-600
`appliedMinting.prop`, whose non-vacuity is machine-checked FALSE
(`WSC.minting600_is_vacuous`) and on which no theorem lives.

The prep and the constant now agree: `WSC/Prep/Minting900.lean:73` preps at 900
and `K_mint = 900`. The non-vacuity hypothesis is DISCHARGED, as a theorem, by
`WSC.Composition.mintingNonVacuous` (see `MintingNonVacuous`), so unlike before
this bridge is USABLE.

SCOPE, unchanged and still binding: 900 covers burn-only-sized minting
transactions. The `Local` / `DelegateTransfer` / `DelegateSeize` arms cost
K = 1,681 / 1,257 / 1,466 (`WSC/Props/Shaped/P4LocalShaped.lean`,
`P4DelegateShaped.lean`) and are OUTSIDE this bound — the shaped modules prep at
2500 and therefore need a bridge at 2500, not this one. That gap is recorded in
`WSC/Composition.lean` §9.5. -/
axiom LR_BUDGET_minting :
  MintingNonVacuous →
  ∀ (pcs : CurrencySymbol) (mlh : ScriptHash) (ctx : ScriptContext),
    OnChain ctx → nodeStepsMinting pcs mlh ctx ≤ K_mint →
    (NodeAcceptsMinting pcs mlh ctx ↔ isSuccessful (appliedMinting900.prop pcs mlh ctx))

/-- **LR_BUDGET_global — PREP-PARAMETRIC (task U2).** *For a transaction whose
real global-validator run halts within `K` CEK steps, where `globalProp` is the
`#prep_uplc` of that validator at budget `K` and that prep is non-vacuous,
ledger acceptance is EQUIVALENT to `isSuccessful (globalProp pcs ctx)`.*

**WHAT WAS WRONG AND WHY THE SHAPE CHANGED.** The old axiom read
`GlobalNonVacuous → ∀ …, nodeStepsGlobal pcs ctx ≤ K_global → (NodeAcceptsGlobal
… ↔ isSuccessful (appliedGlobal.prop pcs ctx))`: it named the **budget-600**
prep while quoting `K_global`. Two independent defects:

1. its non-vacuity hypothesis is MEASURED FALSE at 600
   (`WSC.global_vacuity_probe_600`, `WSC/Prep/Global.lean:70-84`), so it could
   not be applied to anything; and
2. the budget in the hypothesis and the budget baked into the named term were
   different numbers. That is not a harmless mismatch: for `K > 600` the
   right-hand side is `Error` (budget exhaustion) on every transaction costing
   more than 600 steps, so the equivalence would assert
   `NodeAcceptsGlobal … ↔ False`.

Repointing it to ONE concrete prep cannot work either, because the global
theorems live at three DIFFERENT budgets — `appliedGlobal1600` (P5, 1600),
`appliedGlobalMemberShaped3300` (P6, SHAPE G6), and the four P1 preps at 4400 —
and `K_global` is now 4400. Making the prepped term and its budget explicit
parameters is what removes the mismatch by construction: the caller must exhibit
`GlobalPreppedAt globalProp K` for the SAME `K` that appears in the step bound.

INSTANTIATIONS AVAILABLE TODAY, and what each still owes:
* `globalProp := appliedGlobal1600.prop`, `K := K_global_nonmember = 1600`
  (`GlobalPreppedAt` by inspection of `WSC/Prep/Global1600.lean:88`). Owes
  `GlobalNonVacuous appliedGlobal1600.prop`, which is OPEN — see that
  definition's status block.
* `globalProp := appliedGlobalShapedT1.prop …` partially applied to a SHAPE-T1
  scalar tuple, `K := K_global = 4400`
  (`WSC/Shaped/GlobalShapedP1Prep.lean:31`). Non-vacuity is dischargeable there
  (`P1_T1_vacuity_probe` = `Falsified`, plus `P1ShapedWitness`), but the
  instantiation additionally owes the **SHAPE BRIDGE** of
  `WSC/Composition.lean` §9.4 — which is why `WSC/Composition.lean` still puts
  every leaf trigger at `NodeAccepts*` and does budget plumbing only for the base
  validator.

**NAMED TODO — `LR_BUDGET_global_shaped`.** The instantiation that would let a
`LeafSet` field be discharged from `WSC/Props/Shaped/P1Shaped.lean` is exactly
this axiom at the second bullet, and it is NOT provided here: it requires the
shape bridge, which is a separate work unit. Nothing in this library may claim a
usable global budget bridge until that lands.

AUDIT / DISCHARGE of the axiom itself: unchanged from `LR_BUDGET_base` — the
`runSteps` monotonicity meta-theorem (terminal states are returned as-is; fuel-0
becomes `Error` only in a non-terminal state, `CekMachine.lean:229-241`). -/
axiom LR_BUDGET_global :
  ∀ (globalProp : CurrencySymbol → ScriptContext → PlutusCore.UPLC.CekMachine.State)
    (K : Nat),
    GlobalPreppedAt globalProp K →
    GlobalNonVacuous globalProp →
    ∀ (pcs : CurrencySymbol) (ctx : ScriptContext),
      OnChain ctx → nodeStepsGlobal pcs ctx ≤ K →
      (NodeAcceptsGlobal pcs ctx ↔ isSuccessful (globalProp pcs ctx))

/-- **LR_BUDGET_seize — NO PUBLISHED BOUND.** There is no `K_seize`: the
statement is quantified over an arbitrary `K` and gated on a non-vacuity
hypothesis that is MEASURED FALSE at every affordable prep budget. Read this as
"the seize bridge is UNAVAILABLE", not as "the seize bridge holds for some K".

Making it available requires one of: (i) a prep budget ≥ 2,570 (≥ 15 days of
elaboration on the measured slope — not affordable), (ii) shaped contexts with
concrete redeemer indices and per-shape measured K, or (iii) the source-model
route with a separately argued compilation-fidelity bridge. -/
axiom LR_BUDGET_seize :
  SeizeNonVacuous →
  ∀ (K : Nat) (pcs : CurrencySymbol) (ctx : ScriptContext),
    OnChain ctx → nodeStepsSeize pcs ctx ≤ K →
    (NodeAcceptsSeize pcs ctx ↔ isSuccessful (appliedSeize.prop pcs ctx))

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
axiom `DIRWF_L` there. Both bottom out in the SAME conjunct (iv) and the SAME
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
