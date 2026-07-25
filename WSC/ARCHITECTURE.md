# WSC containment proofs — architecture

> **PLACEHOLDER — READ THIS FIRST.** This file was supposed to be a verbatim
> copy of the binding architecture document (`arch-final.md`, base + ADDENDUM
> v3 after the adversarial review's GO-WITH-CHANGES). That document was lost
> when the orchestrator scratchpad was wiped between sessions and was NOT
> available when the `WSC/` library was created (2026-07-24, task U0). What
> follows is the faithful reconstruction actually implemented, assembled from
> the U0 task brief, the persisted project memory, and the Haskell sources.
> When `arch-final.md` is recovered, replace this file with it and re-audit
> `WSC/Honest.lean`'s axiom statements against it.

## Goal

Formalize P1–P6 ("programmable tokens can't leave the mini-ledger") in
Lean4 + Blaster at **UPLC level**, against the ACTUAL compiled production
validators of the wsc-poc CIP-113 platform (not source models).

## §1 Library layout (as implemented)

- `lakefile.lean` — `lean_lib WSC` (root module `WSC.lean`).
- `WSC/flats/` — raw TextEnvelope `cborHex` of the four unapplied production
  scripts + `PROVENANCE.md` (source JSON, wsc-poc commit
  `7ae0024b185cf16f17e38c20c9ee97ae1410c51f`, sha256 per flat).
- `WSC/Imports.lean` (+ `WSC/Prep/{Base,Minting,Seize}.lean`) —
  `#import_uplc … PlutusV3 double_cbor_hex …` + `#prep_uplc` per validator
  with §3 budgets: base **600**, minting **2000**, seize **9000**. The preps
  live in one module per validator (operational: each `#prep_uplc`
  elaboration is expensive — tens of minutes+ — and per-module `.olean`
  caching keeps completed preps from being redone); `WSC/Imports.lean`
  aggregates them. Global import present but commented (CIP-153 builtin tags
  94–99 missing from PlutusCoreBlaster's flat decoder until U5). Each
  inputs-function documents parameter count/order/types with file:line
  evidence from the Plutarch signatures and offchain application sites.
- `WSC/Redeemer.lean` (E8) — Lean mirrors + `IsData` instances for
  `MintProof`, `PLGRedeemer` (TransferAct/SeizeAct), `RegWitness`,
  `MintRedeemer` (Local/DelegateTransfer/DelegateSeize/BurnOnly),
  `DirectorySetNode` (LIST-encoded, 5 fields incl. `globalStateCS`),
  `GlobalParams` (LIST-encoded, 4 fields). Every tag/field cites source.
- `WSC/Spec.lean` — §3 ground-truth vocabulary (`payCred`, `outAtBase`,
  `inAtBase`, `mintOf`, `mintPos`), pure redeemer projections
  (`isTransferAct`, `isSeizeAct`, `isDelegateSeize`, and POSITIONAL
  `classifiedMember`/`classifiedNonMember` per E8), and the §3-P2
  `seizeStructurePreserved` skeleton. Definitions reference ONLY ledger
  ground truth.
- `WSC/Honest.lean` — §4.2 vocabulary (`authenticDirNode`, `dirNodeKey`,
  `dirNodeNext`, `IsRegistered`, `HonestParams`) + the full axiom base:
  TS1–TS5, LR1–LR7, LR-CTX (E5), NONNEG (E6), DirWF three conjuncts (E4),
  LR-BUDGET (E1) per validator. Axiom signatures only; no `sorry` anywhere.

## §0.1 Proof idiom

```
#import_uplc x PlutusV3 double_cbor_hex "WSC/flats/x.flat"
def xInputs (params…) (ctx : ScriptContext) : List Term := toTerm p₁ :: … :: <purpose>Inputs ctx
#prep_uplc appliedX x xInputs BUDGET
theorem … : valid<Purpose>Context ctx → isSuccessful (appliedX.prop … ctx) → POST := by blaster
```

Our TextEnvelope `cborHex` **is** the `.flat` content; use `double_cbor_hex`.

## Binding caveats (ADDENDUM v3, from the adversarial review)

- **E1 / LR-BUDGET (T1 boundedness)**: `#prep_uplc` bakes a concrete CEK step
  budget; exhaustion → `Error` → `isSuccessful` false → theorems vacuous past
  the bound. All results are **bounded-transaction** model checking of real
  bytecode. Needs the LR-BUDGET axiom + a published per-validator K. Never
  claim unbounded.
- **E4 / DirWF**: exactly three conjuncts — insert-only, key-uniqueness,
  NFT-name=key binding.
- **E5 / LR-CTX**: bridges real invocations to CLAB's `validXContext`.
- **E6 / NONNEG**: strict positivity of carried values (containment
  precondition).
- **E7**: flat extraction must carry provenance (see `flats/PROVENANCE.md`).
- **E8**: redeemer mirrors with EXACT tags/fields; mint classification is
  POSITIONAL (lockstep walk of sorted mint entries and the proof list), never
  "some proof says Member".
- **P5**: postcondition must be the covering-node witness
  (∃ authentic node, key < cs < next), not `¬IsRegistered(ctx)`.
- Governance precedent (4264 B @ budget 9000, 22 thms) is scalar-shape only —
  P1/P2 tractability is gated on an empirical spike, not on size.

## Phasing

- **Phase A** (provable now, dropList-only trio): P2/P3/P4, risk order
  P3 → P4 → P2.
- **Phase B** (after CIP-153 lands in PlutusCoreBlaster, U5): P1/P5/P6 —
  P5/P6 expected direct; P1 algebra-assisted, fallback source-model + one
  `_faithful` axiom.
- Composition: bounded-tx inductive invariant; DirWF discharge (directory MP
  at UPLC) is the highest-value follow-on.

## Fidelity deviations found during U0 (source overrides architecture)

1. `DirectorySetNode` has a **fifth field** `globalStateCS` and is
   **`Data.List`-encoded** (not `Constr`) — PTokenDirectory.hs:144-186.
2. The protocol-params datum has **four** fields (globalLogicCred and
   seizeLogicCred appended) and is also LIST-encoded — ProtocolParams.hs:44-108.
3. The seize validator no longer reads `SeizeAct`'s `inputIdxs` /
   `lengthInputIdxs` (it walks every input structurally) but the redeemer
   encoding keeps both fields — ProgrammableLogicBase.hs:1299-1304.
4. Seize is a STANDALONE rewarding validator (`mkProgrammableSeize`); the
   global validator REJECTS `SeizeAct` — ProgrammableLogicBase.hs:1261-1274.
