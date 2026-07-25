# WSC golden ScriptContexts (task W1)

Concrete (validator, params, redeemer, ScriptContext) vectors for the four WSC
validators, each VERIFIED by executing the ACTUAL production-exported unapplied
script — byte-identical to the flats imported in `WSC/flats/` (sha256 table in
`WSC/flats/PROVENANCE.md`) — at PV11 via the ledger evaluator. Purposes:

1. **Anti-vacuity witnesses** (ARCHITECTURE.md Tier 0.2 / ADDENDUM E9): every
   validator has at least one accepting ctx and one rejecting ctx.
2. **Golden-CBOR redeemer round-trip gates** (ADDENDUM E8): `redeemerHex` is the
   off-chain-produced CBOR (`serialiseData`) of each redeemer.
3. **K-measurement inputs** (SPIKE-FINDINGS open issue 2): the accepting ctxs are
   the concrete inputs on which Lean-side CEK step counts are to be measured
   (NOT measured here); the ledger `ExBudget` of each accepting run is recorded.

## Extraction provenance

- Source repository: `wsc-poc` worktree
  `/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d`
  at git commit `97160f894a8e1d3194ef9bec309094f762497c77` (contains the
  Van Rossem / PV11 adoption commit `f918ec6`; its
  `generated/scripts/unapplied/prod/*.json` cborHex strings are byte-identical
  to the four `WSC/flats/*.flat` files — sha256s re-verified at extraction time,
  matching `WSC/flats/PROVENANCE.md`).
- Contexts: the repo's on-chain benchmark catalogue
  (`src/programmable-tokens-test/exe/BenchmarkOnchainScripts.hs`), which builds
  ledger-shaped `PlutusLedgerApi.V3.ScriptContext` values through
  `ProgrammableTokens.Test.ScriptContext.Builder`
  (`buildBalancedScriptContext`: canonical ada-first sorted values via
  `normalizeValue`, inputs/reference-inputs insertion-sorted by `TxOutRef`,
  value-balancing change output). These are NOT captured from a running
  mockchain; per the W1 fidelity bar, each dumped ctx is instead verified by
  re-running the actual compiled script on the dumped ctx (below). Rejecting
  variants are single-field tampers of accepting ctxs (described per golden in
  `sourceTest`).
- Driver (uncommitted, lives in the wsc-poc worktree):
  `scratch-goldens/{GoldenDump.hs,GoldenCatalogue.hs,BenchmarkOnchain/*,golden-dump.cabal}`
  (GoldenCatalogue.hs = verbatim copy of the benchmark catalogue module minus
  `main`), registered via an (uncommitted, gitignored) `packages:` line in
  `cabal.project.local`.
- Commands:
  ```
  cabal build golden-dump --extra-lib-dirs=/usr/local/lib
  ./dist-newstyle/.../golden-dump generated/scripts/unapplied/prod \
      /home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens
  ```
  Output tail: `all 13 goldens verified against prod-exported scripts at PV11`.

## Verification method (per golden)

1. Read `generated/scripts/unapplied/prod/<validator>.json`, take `cborHex`,
   hex-decode, strip the outer CBOR bytestring wrapper (TextEnvelope double-CBOR,
   same layering `WSC/Imports.lean` handles with `double_cbor_hex`) →
   `SerialisedScript`.
2. Apply the script parameters as `Data` constants with Plutarch's
   `applyArguments` (UPLC `Apply` nodes), reserialise, then
   `PlutusLedgerApi.V3.deserialiseScript vanRossemPV`.
3. `PlutusLedgerApi.V3.evaluateScriptCounting vanRossemPV Verbose evalCtx sfe
   (toData ctx)` with the evaluation context built from
   `PlutusLedgerApi.Test.V3.EvaluationContext.costModelParamsForTesting`
   (plutus-ledger-api 1.63.0.0 testlib default cost model — indicative of, but
   not identical to, whatever params mainnet publishes for PV11).
4. Gate: `Right budget` required for `accepts: true`, `Left CekError` required
   for `accepts: false`. The rejecting controls double as arity proof: an
   under-applied script can never produce `Left` (it evaluates to a lambda),
   so `Right` on the accepting sibling is not vacuous.

## File format

`{validator, scenario, accepts, paramsHex, redeemerHex, scriptContextHex,
exBudgetCpu, exBudgetMem, sourceTest}` — all hex fields are `serialiseData`
output (CBOR of the `Data`), i.e. exactly the bytes the ledger/CEK sees.
`paramsHex` is in application order (see per-validator signatures below).
`redeemerHex` duplicates `scriptContextRedeemer` inside the ctx, exposed
separately for the E8 round-trip gates. `exBudgetCpu/Mem` are `null` for
rejecting goldens (counting evaluation aborts).

## Validator signatures (application order of paramsHex)

| validator | params | source |
|---|---|---|
| programmableLogicBase | globalCred : Credential, seizeCred : Credential | `ProgrammableLogicBase.hs:722` (`PAsData PCredential :--> PAsData PCredential :--> PScriptContext :--> PUnit`) |
| programmableTokenMinting | protocolParamsCS : CurrencySymbol, mintingLogicHash : ScriptHash | `Issuance.hs:132` (`PAsData PCurrencySymbol :--> PAsData PScriptHash :--> PScriptContext :--> PUnit`; prod JSON bound to it at `export-smart-tokens/Main.hs:312`) |
| programmableSeize | protocolParamsCS : CurrencySymbol | `ProgrammableLogicBase.hs:1290` |
| programmableLogicGlobal | protocolParamsCS : CurrencySymbol | `ProgrammableLogicBase.hs:1176` |

## Goldens

| file | accepts | ExBudget CPU / Mem | scenario notes |
|---|---|---|---|
| programmableLogicBase.base-spend-transfer-tx | yes | 4,525,794 / 11,715 | spend of a base UTxO inside the single-policy transfer tx (global cred in wdrl) |
| programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT | no | — | spending ctx whose tx invokes only the minting-logic withdrawal |
| programmableTokenMinting.mint-local-registered-by-ref | yes | 34,116,362 / 92,870 | Local arm, `Local 0 0 (RegisteredByReferenceInput 1)`, registry node by ref |
| programmableTokenMinting.mint-burnonly | yes | 14,215,312 / 43,421 | `BurnOnly 2`, burn −1 alongside global TransferAct |
| programmableTokenMinting.mint-delegate-transfer-topup | yes | 26,455,938 / 69,372 | `DelegateTransfer 2 0 1 0`, top-up mint delegated to global |
| programmableTokenMinting.mint-local-empty-withdrawals-REJECT | no | — | Local-arm ctx with `txInfoWdrl := []` |
| programmableSeize.seize-1-input | yes | 51,571,527 / 140,357 | `SeizeAct` (via `mkSeizeActRedeemerFromAbsoluteInputIdxs 1 [0] 0 0 1`), 1 seized input |
| programmableSeize.seize-2-inputs-partial-with-noise | yes | 96,841,491 / 251,272 | 2 seized inputs, partial seize, non-programmable noise tokens preserved |
| programmableSeize.seize-1-input-missing-residual-output-REJECT | no | — | residual (seized-tokens) output removed |
| programmableLogicGlobal.transfer-member-single-policy | yes | 62,665,145 / 177,810 | `TransferAct [1] [1] [] 0`, registered policy, 2 base outputs |
| programmableLogicGlobal.transfer-nonmember-covering-node | yes | 29,160,036 / 86,035 | non-programmable policy exits via covering (does-not-exist) node proof |
| programmableLogicGlobal.transfer-mixed-many-policies | yes | 78,031,424 / 204,737 | 3 registered + 2 unregistered policies, proofs `[1,2,3,4,1]` |
| programmableLogicGlobal.transfer-containment-violation-REJECT | no | — | base output holding 3 of 5 programmable tokens removed |

## Notes / open issues

- The benchmark catalogue itself has a latent arity bug: its
  `programmableLogicBase` bench case applies only 2 of the base validator's 3
  arguments (`[toData globalCred, toData baseSpendingCtx]`,
  `BenchmarkOnchainScripts.hs:1523`), so that bench "PASS" is a lambda value,
  not a validator run. The goldens here apply the full
  `[globalCred, seizeCred, ctx]` per the source signature and are guarded by
  the rejecting control. Worth reporting upstream.
- ExBudget figures use the plutus-ledger-api 1.63 *testing* cost model (see
  above); re-derive against mainnet PV11 params before quoting on-chain costs.
- Lean-side CEK step counts (per-validator `#prep_uplc` budgets K) are to be
  measured on these ctxs by a later task, per SPIKE-FINDINGS open issue 2.
  **DONE — see `K-MEASUREMENTS.md`** (task X1). Measured K: base 208, minting
  784/1,257/1,681, seize 2,570/4,647, global 1,554/3,262/3,726 CEK steps.

## `applied/` — fully applied programs (task X1 input)

`applied/<golden>.flat` is the same double-CBOR-hex TextEnvelope layering as
`WSC/flats/*.flat` (so `#import_uplc … double_cbor_hex` reads it), but with the
script parameters AND the golden `ScriptContext` already applied as `Data`
constants via Plutarch `applyArguments` — i.e. CLOSED, zero-argument programs
that start the exact computation the ledger ran. Produced by the extended golden
driver described under "Extraction provenance" above (same wsc-poc worktree /
commit, same prod script JSONs).

VERIFIED (not assumed) by `KVerify.lean.disabled` + `verify-applied.py`, both in
this directory:

* PCB's flat decoder reads all 13 files ("Successfully decoded double CBOR hex").
* Each program's `Apply` spine, after the script's own top-level `Force`/let
  application (spine arg 0), carries exactly `paramsHex… ++ [scriptContextHex]`
  from the sibling JSON — **byte-identical** after re-serialisation with PCB's
  `PlutusCore.Cbor.encodeData` (= the `serialiseData` builtin). Result:
  `ALL-MATCH` for all 13, with the documented arities (base/minting 2 params +
  ctx, seize/global 1 param + ctx). No file is a bare top-level lambda, so no
  measurement is arity-vacuous (cf. the upstream benchmark arity bug noted above).
* PCB's budget-metered CEK run of each applied program
  (`cekExecuteProgramWithBudget … .plutusV3 .postConway`) reproduces the
  `exBudgetCpu`/`exBudgetMem` recorded in the JSONs **exactly, to the unit, for
  all 9 accepting goldens** — independent agreement between the Lean CEK machine
  + PCB cost model and Haskell `PlutusLedgerApi.V3.evaluateScriptCounting`.
* Polarity is preserved: the 9 accepting goldens `Halt`, the 4 rejecting goldens
  `Error` (still `Error` at 10× the step budget, so not budget starvation).

Runner provenance: `KMeasure.lean.disabled` / `KVerify.lean.disabled` are run
from a `cp -a` of `/home/gumbo/iohk/PlutusCoreBlaster` @ `9f9ca8c` (branch
`cip153-value-builtins`) — see the header comment in each file and
`K-MEASUREMENTS.md` §6. `prep-probes/*.lean.disabled` are the symbolic-`#prep_uplc`
cost probes (budget sweeps of `WSC/Prep/Minting.lean` and `WSC/Prep/Global.lean`)
behind `K-MEASUREMENTS.md` §5.1.
