/-
╔══════════════════════════════════════════════════════════════════════════════╗
║  WSC/Benchmark/EqDataTranslationFAILS.lean                                   ║
║                                                                              ║
║  ⛔ THIS MODULE DOES NOT BUILD, ON PURPOSE. It is a 17-SECOND REPRODUCER for   ║
║  the SECOND blocker on the unshaped P1/P2 benchmark, and it is the cheap one.  ║
║                                                                              ║
║  It is IMPORTED BY NOTHING. `lake build WSC WSC.ShapeBridge` does not see it.  ║
║  To run it deliberately:                                                      ║
║                                                                              ║
║      lake build WSC.Benchmark.EqDataTranslationFAILS                          ║
║                                                                              ║
║  MEASURED 2026-07-29 (warm deps, Lean 4.24.0, Blaster @ 4d320dd) — whole       ║
║  module 16.85 s wall, exit 1, BOTH stanzas failing identically:                ║
║                                                                              ║
║      [Start]: Optimization                                                    ║
║      [End]:   Optimization (13.219000s)     <- stanza 1                        ║
║      [Start]: Translation                                                     ║
║      error: translateRecFun: function body expected for                       ║
║        Lean.Expr.const `PlutusCore.Data.PlutusCore.DataInternal.eqData []     ║
║      [End]:   Optimization (12.762000s)     <- stanza 2 (params hyp DELETED)   ║
║      ... same error                                                           ║
║                                                                              ║
║  i.e. the goal OPTIMIZES fine and then cannot be translated to SMT-LIB at all. ║
╚══════════════════════════════════════════════════════════════════════════════╝

════════════════════════════════════════════════════════════════════════════
WHY THIS EXISTS — TWO INDEPENDENT BLOCKERS, AND THIS IS THE AFFORDABLE ONE
════════════════════════════════════════════════════════════════════════════
`WSC/Benchmark/P1Unshaped.lean` asks for an UNSHAPED `#prep_uplc` at budget 4400
and does not terminate; that is blocker **(BLOCKER-PREP)**, the prep-cost wall, and it is
the headline benchmark (`WSC/BENCHMARK-PREP.md`).

But suppose (BLOCKER-PREP) were fixed tomorrow. The goal would still not close, because of
blocker **(BLOCKER-TRANSLATE)**: over a fully symbolic `ScriptContext` the residual retains
applications of `PlutusCore.Data.eqData`, and Blaster cannot translate them.

(BLOCKER-TRANSLATE) is reproducible at budget **1600**, where the unshaped prep DOES terminate,
in about 17 seconds for the whole module (≈13 s per stanza). That is what this
module does. **Fixing (BLOCKER-TRANSLATE) needs no progress on (BLOCKER-PREP) at all**, which is the only
reason this file is worth shipping.

════════════════════════════════════════════════════════════════════════════
THE MECHANISM
════════════════════════════════════════════════════════════════════════════
`PlutusCore.Data.eqData` is declared inside a Lean `mutual` block together with
`eqDataList`, `eqDataMap` and `eqDataConstr`
(`PlutusCore/Data/Basic.lean:73-95`, the `BEq Data` instance at :98-99). The
constant that survives elaboration is therefore the mutual-block internal
`PlutusCore.Data.PlutusCore.DataInternal.eqData`, and
`Blaster/Smt/Translate/Application.lean:672` throws when `getFunBody` returns
`none` for it:

    | throwEnvError "translateRecFun: function body expected for {reprStr instApp}"

**Why the SHAPED goals never hit it.** A shape closes the entire `Data` skeleton,
so every `eqData` application in the residual has constructor-headed arguments and
the optimizer's `reduceApp?` / `normOpaqueAndRecFun` path reduces it away to
`equalsByteString` / `equalsInteger` comparisons on the leaves. With a symbolic
`ScriptContext` the arguments are variables, nothing reduces, and the constant
reaches the translator. This is the same "shaping collapses the `Data` walk"
mechanism `docs/METHOD.md` §2 describes, seen from the translator's side rather
than the solver's.

════════════════════════════════════════════════════════════════════════════
WHAT WAS RULED OUT — read this before assuming it is our statement's fault
════════════════════════════════════════════════════════════════════════════
1. **Not the benchmark's added params hypothesis.** The benchmark statements carry
   one clause the shaped ones do not, `paramsPublishedBy ctx = some (dirCS, …)`,
   whose right-hand side contains a `Data` and so could plausibly be the source of
   the `eqData`. It is not: DELETING that clause leaves the failure identical
   (Optimization 10.453 s, same error). The variant without it is the second
   stanza below, retained as the control.
2. **Not an artefact of `only-smt-lib`.** The same error appears with
   `(only-smt-lib: 1) (dump-smt-lib: 1)` (Optimization 12.346 s) and on the
   NORMAL path with just `(timeout: 240)` (Optimization 11.006 s / 13.219 s over
   two runs — the phase time itself varies by ~20 %).
3. **Not the budget.** At budget 600 the same goal returns `✅ Valid` inside the
   OPTIMIZATION phase in 0.246 s and never reaches translation — because 600 is
   VACUOUS (no accepting context exists inside 600 CEK steps, proved by
   `WSC.global_vacuity_probe_600`) so the optimizer refutes the accept hypothesis
   outright. The failure appears exactly when the accept hypothesis stops being
   trivially false.
4. **Not the postcondition vocabulary.** `WSC.P1R_T1_stmt` — the PROVED shaped
   theorem — uses the very same `Model.outSum` / `Model.inSum` /
   `Model.mintSigned` conclusion, and under `(only-smt-lib: 1)` it optimizes in
   **0.053 s** and translates in **0.008 s**. The difference is the shape, not the
   ground-truth vocabulary.

════════════════════════════════════════════════════════════════════════════
⚠️ NOTHING HERE IS A RESULT, AND BUDGET 1600 IS PROVABLY VACUOUS FOR P1
════════════════════════════════════════════════════════════════════════════
The goals below are stated at budget **1600** ONLY because that is the largest
unshaped prep of this validator that terminates. A P1 statement at 1600 is
VACUOUS: the cheapest accepting registered transfer this library has measured
costs **2288** CEK steps (`WSC.P1RShapedWitness.K_T8R_is_2288`), P1's own four
shapes cost 2343–2777, and a real off-chain golden costs 2782 and provably does
not halt at 1600 (`WSC.GlobalModelRefuted.golden_shows_budget_gap`). **Do not
quote either stanza below as a P1 result at any verdict.** The non-vacuous
statement is `WSC.Benchmark.P1_unshaped_stmt` at budget 4400, in
`WSC/Benchmark/P1Unshaped.lean`.
-/
import WSC.Benchmark.P1UnshapedStatement
import WSC.Prep.Global1600
import Blaster

set_option maxHeartbeats 0

namespace WSC
namespace Benchmark

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext TokenName
                          validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## Stanza 1 — the benchmark statement form, at the budget that preps -/

/-- `P1UnshapedForm_REFUTED_arity` at `appliedGlobal1600.prop`. **PROVABLY
VACUOUS** (see the banner); stated only to reach the translator.

DELIBERATELY STILL THE REFUTED FORM (renamed 2026-07-31, task: P1 formalization
architecture). This module is a TRANSLATOR REPRODUCER, not a claim: its job is to
reproduce, byte for byte, the (BLOCKER-TRANSLATE) measurement recorded in the
banner, and that measurement was taken on THIS goal shape. Repointing it to
`P1UnshapedFormD`/`P1UnshapedFormH` would silently invalidate the recorded 16.85 s
/ 13.219 s figures. `Model.coveringNodeExists` and `Model.mintSigned` below are
likewise the shapes the measurement was taken on. -/
def P1_form_at_1600 : Prop :=
  P1UnshapedForm_REFUTED_arity (fun (ppCS : CurrencySymbol) (ctx : ScriptContext) =>
    isSuccessful (appliedGlobal1600.prop ppCS ctx))

#blaster (timeout: 240) (verbose: 1) (gen-cex: 0) [P1_form_at_1600]

/-! ## Stanza 2 — the CONTROL: the same goal with the params hypothesis deleted

This is what rules out the benchmark's own added clause as the source of the
`eqData` application. It is also, taken as a statement, FALSE — `base` is
unconstrained, so a positive mint at a pubkey address refutes it (see
`WSC/Benchmark/P1UnshapedStatement.lean`'s header). It never gets far enough to be
falsified, and it must never be quoted as anything but a translator reproducer. -/
def FALSE_control_params_hyp_deleted : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx →
    Model.coveringNodeExists dirCS cs
      ctx.scriptContextTxInfo.txInfoReferenceInputs = false →
    isSuccessful (appliedGlobal1600.prop ppCS ctx) →
      Model.outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
        ≥ Model.inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
          + Model.mintSigned cs tn ctx.scriptContextTxInfo.txInfoMint

#blaster (timeout: 240) (verbose: 1) (gen-cex: 0) [FALSE_control_params_hyp_deleted]

end Benchmark
end WSC
