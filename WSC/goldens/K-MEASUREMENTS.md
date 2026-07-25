# K-MEASUREMENTS — true CEK step counts of the 13 WSC golden runs (task X1)

Answers SPIKE-FINDINGS open issue 2 ("the minimum non-vacuous seize budget is
unknown — measure actual CEK steps of a concrete accepting run before choosing
K") and supplies the numbers ARCHITECTURE.md's `LR-BUDGET` axiom quantifies over.

**Headline. The four production validators halt in 208 – 4,647 CEK steps on real
golden transactions — four orders of magnitude below the ceiling we allowed for,
and the measurement itself costs 3 ms per golden. So the numbers are small and
cheap to get; the bad news is on the other side of the ledger. Symbolic
`#prep_uplc` cost is driven by the BUDGET, and it grows exponentially with a
measured marginal doubling every ~113 budget steps — then hits a cliff
(seize: 19 s at budget 900, never completes at 2,000). Consequently:
base is proved and comfortable (K = 208, prep 600 = 11 s); minting has a genuinely
affordable non-vacuous budget (K_novac = 784, prep ≈ 20 s) and should be attacked
next; global's cheapest accept (1,554) is affordable at 26–36 min of prep — and
that accept is the covering-node scenario, i.e. exactly P5's subject, so P5 at
UPLC is newly within reach; while seize (2,570) and the containment-carrying
global transfers (3,262 / 3,726) are out of reach by 3 to 9 orders of magnitude,
so P2 and P1 cannot be done this way. The blocker was never the
validators' step counts — it is symbolic-prep cost as a function of budget.**

---

## 1. Method

Measured on the FULLY APPLIED goldens `WSC/goldens/applied/*.flat` — the
production unapplied script with all script parameters AND the golden
`ScriptContext` baked in as `Data` constants (Plutarch `applyArguments`), i.e.
CLOSED, zero-argument programs. This is therefore **concrete** CEK evaluation,
not symbolic execution.

* Runner: `WSC/goldens/KMeasure.lean.disabled` (the `.disabled` suffix keeps
  `lake` out of it; it is NOT part of any `lean_lib` here).
* Workspace: `<SCRATCH>/pcb-kmeasure`, a `cp -a` of
  `/home/gumbo/iohk/PlutusCoreBlaster` at branch `cip153-value-builtins`
  @ `9f9ca8c` (warm `.lake`; `lake build PlutusCore` replayed 284 jobs in 2.9s),
  with `<SCRATCH>` =
  `/tmp/claude-1000/-home-gumbo-iohk-wsc-poc/7ad8fab7-3c95-4aef-a618-398aa216c728/scratchpad`.
  A copy is used only to avoid `.lake` lock contention with the agent that owns
  this repo's build.
* Command: `cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean`
  → **all 13 measurements in 3.2 s wall** (each `count_ms` ≤ 3 ms). No
  bisection was necessary and nothing came close to the 10-minute per-run
  ceiling the task allowed for.

`countSteps` iterates the real `PlutusCore.UPLC.CekMachine.step` — the very
function `runSteps` / `cekExecuteProgram` / `#prep_uplc` consume — to the
terminal state, counting applications. Because `runSteps`
(`PlutusCore/UPLC/CekMachine.lean:229-241`) returns a terminal state as-is and
turns fuel-0 into `State.Error` only in a NON-terminal state, that count is
exactly the minimal `runSteps`/`#prep_uplc` budget at which the run's outcome
appears.

**Budget starvation vs. genuine evaluation `Error` (the trap the task flags).**
Three independent guards:
1. `countSteps` reaches `.error` only by APPLYING `step` while fuel remains;
   running out of fuel is a distinct `.fuelOut` outcome — which never fired
   (ceiling 50,000,000 steps, i.e. ≥ 10,000× every measured K).
2. For every golden, `runSteps @ K` and `runSteps @ K-1` were executed:
   accepting goldens give `Halt` / `Error`, rejecting goldens `Error` / `Error`.
3. Every rejecting golden was re-run at `10 × K` and still gives `Error` —
   the "same Error at 10× the budget" test the task asks for.

---

## 2. Fidelity evidence (why these numbers describe the real chain)

1. **Byte-exact arguments.** `WSC/goldens/KVerify.lean.disabled` walks each
   applied program's `Apply` spine, checks every argument is a `Const (Data …)`,
   and re-serialises it with PCB's CBOR encoder (`PlutusCore.Cbor.encodeData`,
   the `serialiseData` builtin). `WSC/goldens/verify-applied.py` diffs those
   hexes against the golden JSONs → **ALL-MATCH for all 13**: after the script's
   own top-level `Force`/let application (spine arg 0, part of the compiled
   script, not a user argument) the arguments are exactly
   `paramsHex… ++ [scriptContextHex]`, in the documented application order, with
   the expected arity (base/minting 2 params + ctx; seize/global 1 param + ctx).
   Spine heads are `Lam`, and no applied program is a bare top-level lambda
   awaiting arguments.
2. **Byte-exact cost.** PCB's own budget-metered run of the same applied program
   (`cekExecuteProgramWithBudget … .plutusV3 .postConway`) reproduces the ledger
   `ExBudget` recorded in the golden JSONs **exactly — all 9 accepting goldens,
   CPU and memory, to the unit** (see table). Those JSON figures came from
   Haskell `PlutusLedgerApi.V3.evaluateScriptCounting` at PV11. Two independent
   evaluators (Lean CEK + PCB cost model vs. plutus-ledger-api 1.63) agreeing to
   the unit on 9 programs is strong evidence that (a) the flat decode is faithful,
   (b) the baked-in ctx is the golden ctx, and (c) PCB's CEK is step- and
   cost-exact against the reference machine on this code.
3. **The measured K is the same unit as a `#prep_uplc` budget, applied to the
   same term shape.** `#prep_uplc … n` elaborates to
   `cekExecuteProgram prog (inputsFn args) n` with `n` a raw `Nat`
   (`PlutusCore/UPLC/PreProcess.lean:143-153`), and `cekExecuteProgram` is
   `runSteps ∘ initialState ∘ applyParams` — the same counter this task
   measures. Crucially the ARGUMENT SHAPE also matches: CLAB's
   `spendingInputs`/`mintingInputs`/`rewardingInputs` return exactly
   `[toTerm ctx]` (`CardanoLedgerApi/V3/Contexts.lean:676-691`) and
   `toTerm x = Term.Const (Const.Data (toData x))`
   (`CardanoLedgerApi/IsData/Class.lean:56`) — a SINGLE `Const` node, exactly as
   in the applied flats, with only the `Data` payload symbolic. So a symbolic
   prep does not pay extra steps to *build* the context, and the path
   corresponding to one of these goldens consumes exactly K steps inside it.
   That is what makes the verdict in §5 a valid comparison rather than an
   analogy.
4. **Uniform CPU-per-step.** 18,132–21,759 CPU units per CEK step and
   54.1–56.3 memory units per step across all four validators and all nine
   accepting goldens — the ratio does not drift, so K is a genuine measure of the
   same machine the ledger meters.

---

## 3. The 13 goldens

`K` = minimal CEK step budget at which the outcome appears (= exact step count of
the run). ExBudget columns are the ledger's, from the golden JSONs (testing cost
model, see MANIFEST.md); `PCB budget` is PCB's own metered run of the applied
program.

| golden | accepts | outcome @K | **K (CEK steps)** | ExBudget CPU | ExBudget mem | PCB budget = ledger? | CPU/step | mem/step |
|---|---|---|---|---|---|---|---|---|
| programmableLogicBase.base-spend-transfer-tx | yes | Halt | **208** | 4,525,794 | 11,715 | **exact** | 21,759 | 56.3 |
| programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT | no | Error | 286 | — | — | n/a | — | — |
| programmableTokenMinting.mint-burnonly | yes | Halt | **784** | 14,215,312 | 43,421 | **exact** | 18,132 | 55.4 |
| programmableTokenMinting.mint-delegate-transfer-topup | yes | Halt | **1,257** | 26,455,938 | 69,372 | **exact** | 21,047 | 55.2 |
| programmableTokenMinting.mint-local-registered-by-ref | yes | Halt | **1,681** | 34,116,362 | 92,870 | **exact** | 20,295 | 55.2 |
| programmableTokenMinting.mint-local-empty-withdrawals-REJECT | no | Error | 1,627 | — | — | n/a | — | — |
| programmableSeize.seize-1-input | yes | Halt | **2,570** | 51,571,527 | 140,357 | **exact** | 20,067 | 54.6 |
| programmableSeize.seize-2-inputs-partial-with-noise | yes | Halt | **4,647** | 96,841,491 | 251,272 | **exact** | 20,840 | 54.1 |
| programmableSeize.seize-1-input-missing-residual-output-REJECT | no | Error | 1,938 | — | — | n/a | — | — |
| programmableLogicGlobal.transfer-nonmember-covering-node | yes | Halt | **1,554** | 29,160,036 | 86,035 | **exact** | 18,765 | 55.4 |
| programmableLogicGlobal.transfer-member-single-policy | yes | Halt | **3,262** | 62,665,145 | 177,810 | **exact** | 19,211 | 54.5 |
| programmableLogicGlobal.transfer-mixed-many-policies | yes | Halt | **3,726** | 78,031,424 | 204,737 | **exact** | 20,942 | 54.9 |
| programmableLogicGlobal.transfer-containment-violation-REJECT | no | Error | 2,970 | — | — | n/a | — | — |

Halt values are `VCon`s (the `PUnit` result); applied-program node counts are 145
(base), 1,285 (minting), 1,976 (seize), 3,448 (global) — identical within a
validator family because each whole `Data` argument is a single `Const` node.

Rejecting goldens error at 286 / 1,627 / 1,938 / 2,970 steps, i.e. BEFORE their
accepting siblings finish — as expected for early-exit condition failures — and
they stay `Error` at 10× budget.

---

## 4. Per-validator K for `LR-BUDGET`

Two DIFFERENT numbers, with different jobs. Conflating them is the single
easiest way to publish a vacuous theorem:

* **K_novac (non-vacuity floor)** = MIN over accepting goldens. A prep at budget
  ≥ K_novac provably admits an accepting run (we have the concrete witness), so
  the mandatory vacuity probe will be Falsified. Below it, every `accept → …`
  theorem is vacuous.
* **K_cover (coverage ceiling)** = MAX over accepting goldens × margin. This is
  what `LR-BUDGET_v` must quantify over if the bounded-transaction theorem is to
  cover the transaction shapes the goldens represent.

| validator | K_novac (witness) | K_max (accepting goldens) | K_cover ×1.5 | K_cover ×2 | prep budget in use today |
|---|---|---|---|---|---|
| programmableLogicBase | **208** (base-spend-transfer-tx) | 208 | 312 | 416 | **600 — covers it (2.9× K_max); P3 PROVED, non-vacuous** |
| programmableTokenMinting | **784** (mint-burnonly) | 1,681 | 2,522 | 3,362 | 600 — no accepting witness within it (600 < K_novac = 784) |
| programmableSeize | **2,570** (seize-1-input) | 4,647 | 6,971 | 9,294 | 600/1,000 — VACUOUS, measured (spike vacuity probes returned Valid) |
| programmableLogicGlobal | **1,554** (transfer-nonmember-covering-node) | 3,726 | 5,589 | 7,452 | 600 — VACUOUS, measured (`Prep/Global.lean`'s own probe) |

Caveat, stated precisely: K_novac is an UPPER bound on the true minimum
accepting budget of each validator (a hand-minimised accepting ctx could halt in
fewer steps; e.g. base's bootstrap witness in Props/P3_Base.lean accepts inside
600 and the golden needs only 208). It is exactly what a non-vacuity claim needs
— a witness — not a lower bound on the threshold. K_cover, conversely, covers
only transactions no bigger than these goldens: seize/global cost scales with
input/output/policy counts (seize 1→2 inputs: 2,570→4,647; global 1→5 policies:
3,262→3,726), so a K_cover chosen for a 2-input seize says NOTHING about a
10-input seize. ARCHITECTURE.md's per-shape/bounded-transaction stance is
therefore mandatory, and any published K must name the shape it covers.

---

### 4.1 Consequences for `Honest.lean`'s LR-BUDGET axioms (actionable, not mine to edit)

`WSC/Honest.lean:354-372` currently states the three axioms as
`∃ K : Nat, 0 < K ∧ ∀ …, OnChain ctx → txSize ctx ≤ K → (NodeAccepts… ↔ isSuccessful …)`.
Two mismatches with ADDENDUM E1 ("K is per-validator and must be computed and
published, empirically calibrated with concrete accepting ctxs run through
`cekExecuteProgram`") that these measurements now let you fix:

1. **The bound is on the wrong quantity.** E1's bound is on CEK STEPS; `txSize`
   is a proxy whose relation to step count is unproven. The measurements give the
   step counts directly — state the hypothesis as `cekSteps ctx ≤ K` (or keep
   `txSize` only if a `txSize → steps` bound is separately established; the
   observed 18.1k–21.8k CPU/step gives the ExBudget side of that bridge, not the
   size side).
2. **`∃ K` should be a published constant.** An existential K makes the axiom
   unusable for auditing (nothing pins which transactions are covered) — and it
   is precisely the sort of clause a reviewer will read as "any K, including a
   vacuous one". Replace with the concrete numbers in §4:
   `K_base = 416`, `K_minting = 3362`, `K_seize = 9294`, `K_global = 7452`
   (max accepting golden × 2), each annotated with the shape it was calibrated on
   and the non-vacuity witness that keeps it honest.
3. The docstrings at `Honest.lean:360` and `:367` say "budget 2000" / "budget
   9000" for minting / seize, but `WSC/Prep/Minting.lean` and
   `WSC/Prep/Seize.lean` both prep at 600. Whatever budgets end up being used,
   those comments must be regenerated from the prep modules, and per §5 the 2000
   / 9000 figures are not achievable with fully symbolic contexts anyway.

---

## 5. THE VERDICT — can a NON-VACUOUS symbolic `#prep_uplc` be reached?

### 5.1 The measured prep-cost wall

Symbolic `#prep_uplc` cost is driven by the BUDGET (the symbolic unrolling
depth), and it grows explosively. Nine fresh measurements were taken for this
task, on the same box that produced SPIKE-FINDINGS (32 cores, 61 GB, Lean 4.24.0,
Z3 4.15.2, `maxHeartbeats 0`, `lake env lean` on a prep-only file, warm `.lake`;
in a `cp -a` of this repo at `<SCRATCH>/clab-prep` with the PlutusCore dep
repointed at `<SCRATCH>/pcb-kmeasure`; probe sources in
`WSC/goldens/prep-probes/`):

| validator | budget | prep wall | source |
|---|---|---|---|
| programmableTokenMinting | 600 | **11.1 s** | this task (`prep-probes/Mint600`) |
| programmableTokenMinting | 900 | **27.6 s** | this task |
| programmableTokenMinting | 1,200 | **131.6 s** | this task |
| programmableTokenMinting | 1,700 | **never completed — killed at 48.6 min** | this task |
| programmableLogicGlobal | 600 | **11.8 s** | this task (CIP-153 builtins) |
| programmableLogicGlobal | 900 | **24.3 s** | this task |
| programmableLogicGlobal | 1,600 | **2,143 s = 35.7 min** (completed; max RSS 1.55 GB) | this task |
| programmableSeize | 600 | **12.7 s** | this task (11.1 s in SPIKE-FINDINGS) |
| programmableSeize | 900 | **19.4 s** | this task |
| programmableSeize | 2,000 | never completed (>29 m, then >77 m) | SPIKE-FINDINGS |
| programmableSeize | 9,000 | never completed (>62 m) | SPIKE-FINDINGS |
| governance (repo precedent) | 9,000 | never completed (>29 m) | SPIKE-FINDINGS |

Three facts fall out:

* **Prep cost is driven by the budget, NOT by script size.** At 600: minting
  11.1 s, global 11.8 s, seize 12.7 s. At 900: seize 19.4 s, global 24.3 s,
  minting 27.6 s. Those scripts are 1,285 / 3,448 / 1,976 nodes and global
  additionally carries the CIP-153 `Value` builtins, yet the spread at a fixed
  budget is under 1.5×. Budget is the control variable; the four validators are
  interchangeable to within a small factor.
* **There is a fixed ≈8 s floor plus an exponential term.** Fitting the three
  minting points to `t = c₀ + A·e^{s·b}` gives an exact solution
  c₀ = 7.96 s, ratio ×6.29 per +300 steps, **s = 0.00613 /step — the marginal
  cost doubles every 113 budget steps**. (600→900 and 900→1,200 in raw terms:
  ×2.5 then ×4.8.)
* **The slope STEEPENS, so every fit is optimistic.** Global's slope goes from
  0.00482 /step (600→900) to **0.00696 /step (900→1,600) — doubling every 100
  steps**. Minting @1,700 was predicted at 39–44 min by its own 600–1,200 fit and
  did not finish in **48.6 min**. Seize is the extreme case: its 600→900 slope
  (0.00294) predicts @2,000 ≈ 5 min, but the measured @2,000 never completed in
  77 minutes — ≥ 15× the fit. Somewhere between 900 and 2,000 the symbolic
  execution crosses into path-explosion on symbolic `Data` (SPIKE-FINDINGS:
  fixing list spines does not help, because redeemer/datum/mint fields stay
  symbolic). **Treat every extrapolation below as a LOWER BOUND on cost**, and
  note the practical ceiling observed here: budgets of 1,600–1,700 cost 36–>49
  minutes, and nothing above ~2,000 has ever completed for any WSC validator.

Extrapolation used in the verdict, each validator anchored on its own STEEPEST
measured slope (`t = 8 + A·e^{s·b}`; minting s = 0.00614, global s = 0.00696,
seize taken as global's since seize's own 600→900 slope is empirically refuted by
its @2,000 non-completion):

| target budget | why | smooth-fit cost (lower bound) | measured reality nearby |
|---|---|---|---|
| ~800 | minting K_novac = 784 | **≈ 20 s** | bracketed by 600 = 11 s and 900 = 28 s — **affordable** |
| 1,554 | global K_novac | ≈ 26 min | **bracketed by the measured 1,600 = 35.7 min** |
| 1,681 | minting K_max | ≥ 45 min | **1,700 measured: did NOT finish in 48.6 min** |
| 2,522 | minting K_cover ×1.5 | ≥ 4.8 days | — |
| 2,570 | seize K_novac | ≥ 15 days | seize @2,000 already >77 min, never completed |
| 3,262 / 3,726 | global K_max (P1's real shapes) | ≈ 7 y / 182 y | — |
| 6,971 | seize K_cover ×1.5 (2-input seize) | astronomical | — |

### 5.2 Per-validator verdict

**programmableLogicBase — (a) ALREADY DEMONSTRATED.** K_novac = K_max = 208; the
prep in use is 600, i.e. 2.9× the golden's whole run, and P3 is proved
non-vacuously there (`WSC/Props/P3_Base.lean`, prep 11 s class). Nothing to fix.
Headroom exists for a bigger base prep if some future property needs it
(600 → 900 costs ~28 s).

**programmableTokenMinting — (b) PLAUSIBLY REACHABLE, and the cheap end is
essentially in hand.** A non-vacuous prep needs only ≥ 784 (mint-burnonly), which
sits between the measured 600 (11.1 s) and 900 (27.6 s) → **~20 s: affordable
today**. That budget yields a genuinely non-vacuous P4-class theorem, but one
whose scope is "burn-only-sized minting transactions". Covering all three minting
goldens needs 1,681 (smooth-fit ≈ 39 min; the measured 1,700 run did not finish in
48.6 min — CI-hostile
even in the good case, and only tolerable because `WSC/Prep/*` caches each prep in
its own module), and `K_cover ×1.5 = 2,522` is ≥ 4.7 days — out of reach. **Recommendation:
raise `Prep/Minting.lean` from 600 to ~800–900 and prove P4 there, with the
scope stated as "minting runs halting within 900 steps" and mint-burnonly as the
non-vacuity witness.**

**programmableLogicGlobal — SPLIT VERDICT: (b) REACHABLE for the covering-node
(P5) shape, at 26–36 min of prep; (c) OUT OF REACH for the containment (P1)
shapes by 5–9 orders of magnitude.** K_novac = 1,554 — and that cheapest accept is
`transfer-nonmember-covering-node`, i.e. exactly the scenario ADDENDUM E3 makes
P5's subject ("P5's postcondition is the covering-node witness"). Global prep at
1,600 was MEASURED at 35.7 min / 1.55 GB and completed, so a non-vacuous global
prep covering that shape is genuinely available today as a one-off cached
elaboration — **this is the one new "yes" this measurement unlocks beyond base.**
What it does NOT cover is P1: the containment-carrying member accepts cost 3,262
and 3,726 steps, extrapolating (on global's own steepest measured slope) to ≈ 7
years and ≈ 182 years of prep. **P1 at UPLC over a fully symbolic ctx is dead.**
The CIP-153 `valueContains` route does not rescue it: prep cost is budget-driven,
and the builtin only lowers the ON-CHAIN step count (already counted in §3), not
the symbolic unrolling of the rest of the validator.

**programmableSeize — (c) OUT OF REACH BY ORDERS OF MAGNITUDE.** The smallest
accepting seize run is 2,570 steps. Symbolic prep at 2,000 already never
completed in 77 minutes (≥ 15× above the smooth fit for seize, which is how we
know about the cliff); 2,570 is ≥ 15 days on global's measured slope and realistically
unbounded, and the ×1.5 coverage budget 6,971 is astronomical. Every "seize accept ⟹ …" theorem at any prep budget we
can afford (≤ ~1,000) is provably vacuous — which is exactly what the spike's
vacuity probes at 600/1,000 reported. **P2 over a fully symbolic ScriptContext is
dead at UPLC level**; it needs either shaped contexts with concrete
redeemer/spines (and the spike showed shaped-at-9,000 also never completed, so
shaping must be aggressive: concrete indices AND concrete `Data` scalars), or the
source-model (B3) route.

### 5.3 What this means for the remaining plan

1. **P3 (base) stays the keystone**, and its architectural weight increases: it
   is what forces global/seize to run at all, and it is the only property provable
   over a fully symbolic context at trivial cost.
2. **Move minting up the queue.** Non-vacuous at ~800 for ~20 s of prep — the
   cheapest new UPLC result available. Do it before any further seize/global
   attempt.
3. **Take the one global win that is affordable: P5 at budget ~1,600
   (35.7 min, measured, cached).** The covering-node accept (1,554 steps) is both
   the non-vacuity witness and P5's own subject shape, so P5-at-UPLC is
   reachable — the single most valuable newly-unlocked target. Budget CI for a
   ~40-minute prep in its own module, and do NOT attempt to widen that prep
   toward the member-transfer accepts (3,262+) in the same file.
4. **Stop spending time on fully-symbolic seize preps and on any global prep
   above ~1,700.** The wall is
   exponential-plus-cliff and we are 1.6–2.7× in budget away from the
   non-vacuity floor — which at ~113 steps per doubling is 10–16 doublings, i.e.
   3–5 orders of magnitude in time. Redirect to (i) shaped/partially-concrete
   contexts with measured per-shape K — the numbers in §3 are exactly the
   per-shape budgets to use (2,570 for 1-input seize, 3,262 for single-policy
   transfer, …) — and/or (ii) the source-model route for P1/P2 with a separately
   argued compilation-fidelity bridge.
5. **The LR-BUDGET axiom is now quantitative.** For each validator, state
   `LR-BUDGET_v` as "a real node run of v on a transaction of shape S halts in
   ≤ K_v(S) CEK steps", with K_v(S) taken from §3 × margin, and record that the
   ledger's own ExBudget for those runs is 4.5M–96.8M CPU (≈ 20k CPU/step) —
   i.e. all of the goldens sit far inside the 10^10 CPU per-tx mainnet limit, so
   the axiom is not a hidden restriction on realistic transactions of that shape.
   A prep-side speedup (memoized/opaque recursive-CEK abstraction in Blaster,
   SPIKE-FINDINGS verdict (c)) is the only thing that would change the verdict
   for seize/P1; the required improvement is ≈3 orders of magnitude for seize
   non-vacuity (15 days → 40 min) and 6–9 orders for P1's member-transfer accepts.

---

## 6. Reproduction

Probe files as committed: `prep-probes/{Mint600,Mint900,Mint1200,Mint1700,Global600,Global900,Global1600,Seize600,Seize900}.lean.disabled`
(each is `WSC/Prep/<V>.lean` with a renamed namespace/defs, `set_option
maxHeartbeats 0`, and the prep budget changed; the Global ones drop the trailing
vacuity probe so only the prep is timed). Drop them into a `PrepProbe/`
directory of the CLAB copy, without the `.disabled` suffix.

```
# K measurement + minimality/genuine-Error confirmation (3.2 s)
cp -a /home/gumbo/iohk/PlutusCoreBlaster <SCRATCH>/pcb-kmeasure   # git log -1 == 9f9ca8c
cp WSC/goldens/KMeasure.lean.disabled <SCRATCH>/pcb-kmeasure/KMeasure.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KMeasure.lean

# applied-flat argument fidelity (byte-exact vs the golden JSONs)
cp WSC/goldens/KVerify.lean.disabled <SCRATCH>/pcb-kmeasure/KVerify.lean
cd <SCRATCH>/pcb-kmeasure && lake env lean KVerify.lean > /tmp/kverify.log
python3 WSC/goldens/verify-applied.py /tmp/kverify.log      # → ALL-MATCH

# prep-cost wall (§5.1); each probe is Prep/<V>.lean with a changed budget
cp -a <this repo> <SCRATCH>/clab-prep
#   in <SCRATCH>/clab-prep/lakefile.lean: repoint `require PlutusCore from` to
#   <SCRATCH>/pcb-kmeasure ; probes are WSC/goldens/prep-probes/*.lean.disabled
cd <SCRATCH>/clab-prep && /usr/bin/time -f "WALL=%e" timeout 3000 \
    lake env lean PrepProbe/Mint900.lean
```

## 7. Open issues

1. Both `#eval!`-based files run under the Lean INTERPRETER (PCB has no
   `precompileModules`), so the wall times in §1 are worst-case; a native build
   would be faster still. Irrelevant at these K, relevant if someone measures a
   10^7-step program.
2. PCB's `runStepsWithBudget` carries a `sorry` in its `decreasing_by`
   (`PlutusCore/UPLC/CekMachine.lean:299`), hence `#eval!` rather than `#eval`
   for the budget cross-check. The step-count measurement itself does not touch
   it.
3. The exact ExBudget agreement (§2.2) is against the plutus-ledger-api 1.63
   **testing** cost model (MANIFEST.md). It proves machine/decoder fidelity, not
   that mainnet PV11 publishes those params.
4. Per-shape scaling of K is only sampled (2 points for seize, 3 for global).
   Before publishing per-shape K_cover values for the shaped-prep route, measure
   K on a small grid of shapes (inputs × policies × outputs) — the applied-flat
   pipeline makes this cheap (3 ms per measurement).
5. The prep-cost extrapolations are 2–3-point fits per validator with a
   STEEPENING slope, and both deep probes overshot their own fit (global 1,600:
   36 min vs 18 min predicted; minting 1,700: >48.6 min vs 39–44 min predicted).
   Treat every extrapolated column as a lower bound on cost, not a
   promise.

---

## Appendix A — verbatim output of `lake env lean KMeasure.lean`

(`Successfully decoded double CBOR hex '<file>'` lines from the importer omitted;
one per golden, all 13 successful. Total wall 3.209 s.)

```
programmableLogicBase.base-spend-transfer-tx: K=208 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=145 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=4525794,mem=11715] | count_ms=0 confirm_ms=0 budget_ms=1
programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: K=286 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=145 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=0 confirm_ms=0 budget_ms=1
programmableTokenMinting.mint-local-registered-by-ref: K=1681 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=34116362,mem=92870] | count_ms=2 confirm_ms=0 budget_ms=4
programmableTokenMinting.mint-burnonly: K=784 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=14215312,mem=43421] | count_ms=1 confirm_ms=0 budget_ms=3
programmableTokenMinting.mint-delegate-transfer-topup: K=1257 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1285 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=26455938,mem=69372] | count_ms=0 confirm_ms=0 budget_ms=4
programmableTokenMinting.mint-local-empty-withdrawals-REJECT: K=1627 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1285 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=1 confirm_ms=0 budget_ms=2
programmableSeize.seize-1-input: K=2570 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=51571527,mem=140357] | count_ms=2 confirm_ms=0 budget_ms=7
programmableSeize.seize-2-inputs-partial-with-noise: K=4647 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=1976 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=96841491,mem=251272] | count_ms=3 confirm_ms=0 budget_ms=13
programmableSeize.seize-1-input-missing-residual-output-REJECT: K=1938 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=1976 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=2 confirm_ms=0 budget_ms=2
programmableLogicGlobal.transfer-member-single-policy: K=3262 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=62665145,mem=177810] | count_ms=2 confirm_ms=0 budget_ms=10
programmableLogicGlobal.transfer-nonmember-covering-node: K=1554 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=29160036,mem=86035] | count_ms=1 confirm_ms=0 budget_ms=5
programmableLogicGlobal.transfer-mixed-many-policies: K=3726 outcome=KMeasure.Outcome.halt | runSteps@K=Halt @K-1=Error @10K=Halt | shape=Apply(applied) nodes=3448 halt=PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCo | pcbBudget[cpu=78031424,mem=204737] | count_ms=2 confirm_ms=0 budget_ms=11
programmableLogicGlobal.transfer-containment-violation-REJECT: K=2970 outcome=KMeasure.Outcome.error | runSteps@K=Error @K-1=Error @10K=Error | shape=Apply(applied) nodes=3448 halt=n/a | pcbBudget[n/a(rejecting)] | count_ms=2 confirm_ms=0 budget_ms=4
```

## Appendix B — verbatim prep-probe output

```
$ /usr/bin/time -f "BUDGET=%s ..." timeout … lake env lean PrepProbe/MintB.lean
BUDGET=600  EXIT=0   WALL=11.086
BUDGET=900  EXIT=0   WALL=27.61   CPU=27.33
BUDGET=1200 EXIT=0   WALL=131.57  CPU=131.31
BUDGET=1700 EXIT=124 WALL=2918.66            <- timeout-killed, NEVER COMPLETED
GLOBAL BUDGET=600  EXIT=0 WALL=11.84   CPU=11.76   MAXRSS_KB=1188528
GLOBAL BUDGET=1600 EXIT=0 WALL=2143.40 CPU=2141.09 MAXRSS_KB=1588268
PROBE='Global900' EXIT=0 WALL=24.30 CPU=23.86
PROBE='Seize600'  EXIT=0 WALL=12.71 CPU=12.19
PROBE='Seize900'  EXIT=0 WALL=19.38 CPU=18.62
```

## Appendix C — verbatim applied-flat verification

```
$ lake env lean KVerify.lean > /tmp/kverify.log && python3 verify-applied.py /tmp/kverify.log
OK programmableLogicBase.base-spend-no-global-or-seize-invoked-REJECT: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicBase.base-spend-transfer-tx: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-containment-violation-REJECT: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-member-single-policy: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-mixed-many-policies: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableLogicGlobal.transfer-nonmember-covering-node: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-1-input-missing-residual-output-REJECT: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-1-input: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableSeize.seize-2-inputs-partial-with-noise: nargs_after_head=2 expected=2 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-burnonly: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-delegate-transfer-topup: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-local-empty-withdrawals-REJECT: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
OK programmableTokenMinting.mint-local-registered-by-ref: nargs_after_head=3 expected=3 head0=NOT-A-DATA-CONST(Force)
ALL-MATCH
```
