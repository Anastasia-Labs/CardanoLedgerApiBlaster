REPORT — TASK U5 COMPLETE

**Commit**: `830819bc74d0846e75262798542b4accf2b5a331` on branch `cip153-value-builtins` in `/home/gumbo/iohk/PlutusCoreBlaster` (author "Philip DiSarro <philipdisarro@gmail.com>", no co-author, not pushed). Diffstat: 16 files, +1002/−6 (tail above; key files below).

**Context recovery (deviations forced by environment)**: All scratchpad context files (arch-final.md, inv-*.md, uplcflats/) were deleted before I started; I reconstructed requirements from the task text + auto-memory + repo sources. The CLAB copy of `programmableLogicGlobal.flat` also vanished mid-session (CLAB is being reorganized by another agent; I never touched it). I regenerated the gate fixture from wsc-poc: `git show feat/van-rossem-bump:generated/scripts/unapplied/prod/programmableLogicGlobal.json` → cborHex (6880 hex chars, `590d6d590d6a0101...` = double-CBOR, UPLC 1.1.0; regenerated on that branch by commit 7ae0024 "regenerate exported scripts... PV11 validators") → `PlutusCore/UPLC/ScriptEncoding/TestsFlat/programmableLogicGlobal.flat`.

**What was built** (partial prior work on the branch reviewed via `git diff`, verified correct, kept, and completed):
- `PlutusCore/UPLC/Term/Basic.lean` — (pre-existing, kept) `BuiltinFun` entries InsertCoin..UnValueData after DropList; `Const.Value : List (ByteString × List (ByteString × Integer))`; (new) `AtomicType.TypeValue`.
- `PlutusCore/UPLC/Builtins.lean` — (kept) arities: InsertCoin 4×ArgV, LookupCoin 3, UnionValue 2, ValueContains 2, ValueData 1, UnValueData 1, all monomorphic.
- `PlutusCore/UPLC/FlatEncoding/Basic.lean` — (kept) builtin tags 94–99 enabled; (new) uni tag 13 → TypeValue in `decodeConstType`; (new) value-constant decoder (list-of-pairs per flat Map encoding, K/Quantity validation, `packValue` normalization).
- `PlutusCore/Value/Basic.lean` (new, 256 lines) — pure model of Value.hs: `ValueRep`, `insertCoin`, `deleteCoin`, `lookupCoin`, `unionValue`, `valueContains`, `valueData`, `unValueData`, `packValue`; all total (termination_by on list lengths), `Option.none` = BuiltinResult failure.
- `PlutusCore/UPLC/BuiltinFunctions/Value.lean` (new) — CekValue wrappers, args reversed per repo convention; dispatched from `Evaluate.lean` (6 new arms).
- `PlutusCore/UPLC/CostModels.lean` (+239) — helpers `argValueTotalSize`, `argValueMaxDepth`, `dataNodeCount`/`argDataNodeCount`; `constSize (.Value v) = totalSize v`; 6 cost arms in all five variants A–E.
- `PlutusCore/UPLC/Term/{Instances,ToExpr}.lean`, `TextEncoding/Basic.lean` — Repr/ToExpr/BEq/name-parse coverage for the new constructors (`"value"` type name parses; value constants fail textual parse like MlResult).
- `PlutusCore/Value/Tests.lean` (new, 331 lines) — ~45 unit tests (native_decide) incl. all specifically requested: unionValue zero-drop, valueContains negative-error (both arms), insertCoin amount-0 delete (incl. no-validation corner), unValueData rejects unsorted/dup/zero/oversized/empty-inner; CEK-dispatch tests through `evaluateBuiltinFunction`; the import gate; six `usesBuiltin` checks proving the decoded script contains InsertCoin/UnionValue/ValueContains/ValueData/UnValueData/DropList (gate non-vacuous); evaluation smoke. Registered in `Tests/Basic.lean`. No `.plutus-conformance` dir exists in PCB (checked), so unit tests per plan fallback.

**ACCEPTANCE**
(a) `~/.elan/bin/lake build` → "Build completed successfully (283 jobs)" (only warning: pre-existing `sorry` at CekMachine.lean:299, runStepsWithBudget termination — predates this work). `lake build Tests` → "Build completed successfully (291 jobs)".
(b) KEY GATE: `#import_uplc wstGlobal PlutusV3 double_cbor_hex ".../programmableLogicGlobal.flat"` guarded by `#guard_msgs` expecting `Successfully decoded double CBOR hex '...'` — `lake env lean PlutusCore/Value/Tests.lean` exits clean (guard matched). Evaluation smoke inside PCB: applied decoded body to two dummy `Data (I 0)` args, `runStepsWithBudget default defaultCekMachineCostsC` with 10¹⁰/10¹⁰ budget → terminal `EvaluationError` ("EvaluationError (expected with dummy args)" via #eval!), i.e. real bytecode runs on the CEK end-to-end, no decode failure, no budget exhaustion, no stuck state.

**Fidelity evidence (all verified in this session)**
- Flat builtin tags 94–99: `plutus/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs:2171-2176` (encode `InsertCoin -> 94` … `UnValueData -> 99`), decode `go 94..go 99` at :2275-2280.
- Arities/signatures: Builtins.hs:1979-2027 — insertCoin `ByteString→ByteString→Integer→ValueMaxDepth→BuiltinResult Value` (4), lookupCoin (3), unionValue/valueContains (2), valueData/unValueData (1).
- Uni tag: Universe.hs:896 `encodeUni DefaultUniValue = [13]`, :920 decode.
- Semantics: Value.hs read in full (564 lines): maxKeyLen=32 (:70), Quantity bounds ±2^127 (Bounded instance), insertCoin amount-0 → deleteCoin with unchecked `UnsafeK` (no validation), replace-not-add via `insertLookupWithKey (\_ _ _ -> qty)`; unionValue overflow fail + zero-drop + empty-inner drop; valueContains fails on negatives in either arg (v1 checked first), `isSubmapOfBy (isSubmapOfBy (<=))`; valueData `Map/B/I` ascending; unValueData rejects non-Map, non-B keys, oversized keys, non-ascending at both levels, empty inner map, zero and out-of-bounds `I` (empty outer map valid); Flat instance = `pack <$> decode` with Map-as-list encoding (flat/src/PlutusCore/Flat/Instances/Containers.hs:73) and validating K/Quantity Flat instances.
- Cost numbers: cost-model/data/builtinCostModel{A,B,C}.json (identical across A/B/C); formulas from CostingFun/Core.hs:527-550 (with_interaction c00+c10x+c01y+c11xy) and :702-709 (const_above_diagonal); size measures ExMemoryUsage.hs:391-446 (DataNodeCount node count, ValueTotalSize, ValueMaxDepth = ⌊log₂m⌋+1 + ⌊log₂k⌋+1) and :405-407 (generic `ExMemoryUsage Value` = totalSize, mirrored in `constSize`).

**Judgment calls / deviations vs Value.hs** (all documented in-code):
1. valueContains `totalSize v1 < totalSize v2 → False` shortcut omitted from semantics (proved-equivalent for normalized non-negative values; kept only in the cost arm's diagonal).
2. unionValue empty-shortcircuits and size-based argument swap omitted (identity/commutativity make them semantically transparent).
3. Error-check *order* within a builtin (e.g. currency-vs-token-vs-quantity in insertCoin) collapses to a single `none`; order preserved anyway where cheap.
4. Cost model: variants D/E reuse the A/B/C numbers (our plutus checkout's D/E JSONs predate CIP-153) — explicitly NOT load-bearing (Blaster budgets by CEK step count).
5. `negativeAmounts` recomputed by scan instead of cached counter (model has no caching; observationally identical).
6. Flat value-constant decode models `Map.fromList` last-wins for duplicate keys + `pack` normalization (`packValue`); tested. Compiled scripts are unlikely to ever contain value constants, but decode is now faithful if they do.

**Open issues**
- CekMachine.lean:299 pre-existing `sorry` (runStepsWithBudget termination) — untouched; it forces `#eval!` for ad-hoc budget runs (native_decide in tests unaffected).
- Textual (`(con value ...)`) constant syntax not parsed (fails like bls12_381_MlResult); not needed for any current gate.
- `#import_uplc` registers `wstGlobal` in the ROOT namespace (elaborator uses the raw ident), not the file's namespace — callers (CLAB WSC work) should reference it unqualified.
- The gate fixture is the *unapplied* prod global validator from wsc-poc `feat/van-rossem-bump` (PR #110); if that branch's redeemer/script layout changes, re-export and refresh the fixture.
- ScaleValue (also CIP-153, tag 100 region) intentionally NOT added — not used by our validator and not in the task's builtin list.