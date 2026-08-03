# The `#prep_uplc` memory cliff — consolidated hand-off

**Status:** measurement record + upstream ask. Nothing in this document is a
result module; every module cited here is marked ⛔ NOT IMPORTED BY ANYTHING.

**Extends** `WSC/BENCHMARK-PREP.md` §5 (the 2026-07-29 cost curve, which
measured *wall time under a 15-minute `timeout -s KILL` cap*) with the
2026-08-02 campaign, which removed the wall-clock cap, added a hard **memory**
cap, and ran the rungs to their natural death. The headline change to the §5
picture: **the binding wall is memory, not time**, and it is a cliff, not a
slope.

**Substrate for every row below** (unchanged from BENCHMARK-PREP §8 except the
date): measured **2026-08-02**, 32-core / 61 GB WSL2 box, Lean **4.24.0**,
Blaster pin **4d320dd**, warm dependency oleans, `maxHeartbeats 0`, flats from
`input-output-hk/wsc-poc` `main` @ `2306678` (`WSC/flats/PROVENANCE.md`).
Raw logs: `.lake/wsc-probe-logs/{prep2200,prep2300,prepT2400,prepT2400B,probeA,probeB,probeB2}.log`
(one `EXIT=/WALL=/MAXRSS=` line each) and `.lake/wsc-probe-logs/leanmon.log`
(RSS time series, ~28 s sampling).

---

## 1. The five-point measurement table

All five points are the same validator (`programmableLogicGlobal`, the
transfer validator) and the same flat; they differ only in the budget and in
how much of the `ScriptContext` is pinned to a concrete skeleton.

| # | context | budget | outcome | wall | MaxRSS | cap (`ulimit -v`) | log |
|---|---|---:|---|---:|---:|---:|---|
| 1 | UNSHAPED (`globalInputs1600`) | 2200 | `INTERNAL PANIC: out of memory` | **2828.50 s ≈ 47 min** | **21,581,296 kB ≈ 21.6 GB** | 32 GiB | `prep2200.log` |
| 2 | UNSHAPED (`globalInputs1600`) | 2300 | `INTERNAL PANIC: out of memory` | **783.03 s ≈ 13 min** | **27,385,380 kB ≈ 27.4 GB** | 34 GiB | `prep2300.log` |
| 2′ | same module, **UNCAPPED**, earlier the same day | 2300 | **kernel OOM-kill**, `anon-rss:46047640kB` ≈ **46 GB** — **took the WSL VM down** | not recorded (reboot destroyed the log) | ≈46 GB anon-RSS (from the kernel message) | none | — |
| 3 | PARTIAL SKELETON, point 1 (`GPrepT2400`) | 2400 | `INTERNAL PANIC: out of memory` | **1093.32 s ≈ 18 min** | **34,680,000 kB ≈ 34.7 GB** | 42 GiB | `prepT2400.log` |
| 4 | PARTIAL SKELETON, point 2 (`GPrepT2400B`) | 2400 | `INTERNAL PANIC: out of memory` | **6808.70 s ≈ 113 min** | **32,548,552 kB ≈ 32.5 GB** | 42 GiB | `prepT2400B.log` |
| 5 | **SHAPED CONTROL** — SHAPE T1R, closed `Data` skeleton (`WSC.Shaped.GlobalShapedP1RPrep`) | **4400** | **completes** | **1.51 s** | — | — | BENCHMARK-PREP §5.3 (2026-07-29) |

What each context pins:

* **rows 1–2, unshaped** — nothing pinned; the `ScriptContext`, redeemer and
  purpose are fully symbolic. `WSC/Benchmark/CostG2200.lean`,
  `WSC/Benchmark/CostG2300.lean`.
* **row 3, lattice point 1** — redeemer pinned to the raw 5-field `TransferAct`
  spine `Constr 0 [f1,f2,f3,f4, I 0]` (fields symbolic, `paramsRefIdx = 0`
  literal), `txInfoMint := []` (mint walk never starts), purpose
  `RewardingScript cred` with `cred` symbolic. Every transaction list spine
  still symbolic. `WSC/Shaped/Probe/GPrepT2400.lean`.
* **row 4, lattice point 2** — point 1's pins **plus all four transaction list
  spines closed at the T1R topology** (`txInfoInputs`, `txInfoOutputs`,
  `txInfoReferenceInputs`, `txInfoWdrl` each 2 elements); every value, datum,
  credential and redeemer field inside them still symbolic.
  `WSC/Shaped/Probe/GPrepT2400B.lean`.
* **row 5, control** — the closed T1R skeleton, ~40 scalar leaves; the prep the
  four proved shaped P1 theorems are stated over.

### 1.1 The cliff shape (RSS time series, `leanmon.log`)

The trajectories are the diagnostic, not the peaks. Two phases every time: a
long **gentle** phase, then an **explosive** endgame that ends in the
allocator failing within a couple of samples.

| run | gentle phase | explosive phase |
|---|---|---|
| unshaped @2300 | 1.2 GB → 3.9 GB over 13:17→13:24 (≈0.25 GB/min), then 6.2→7.2 GB 13:24→13:29 | **7.2 GB @13:29:01 → 14.8 GB @13:29:29 → 26.5 GB @13:29:57**, panic — ≈**19 GB in 56 s** |
| unshaped @2200 | reaches ≈5.0 GB by 13:37, then **flat 5.02→5.31 GB for ~38 min** (13:37→14:15), i.e. ≈7 MB/min | **5.2 GB @14:16:45 → 7.5 @14:17:13 → 10.2 @14:17:42 → 17.8 GB @14:18:10**, panic — >15 GB in ≈3 min |
| partial @2400 (pt 1) | 1.4 GB @10:18 → 5.3 GB @10:33 | **5.3 GB @10:33:39 → 15.7 @10:34:39 → 26.5 GB @10:35:38**, panic — ≈21 GB in 2 min |
| partial @2400 (pt 2) | **no time series** — the monitor was not running for this build; only the `WALL`/`MAXRSS` line in `prepT2400B.log` exists. Stated rather than invented. |

Two honesty notes on the series:

* the sampler's last observation is always *below* the `MAXRSS` figure (e.g.
  26.5 GB sampled versus 27.4 GB `MAXRSS` at 2300) — the final seconds outrun
  a 28 s sampling interval. Use `MAXRSS` for the peak and the series only for
  the shape.
* the 2300 run and the `GDestructure1600B` probe overlapped in `leanmon.log`
  (13:17→13:30, pids 14237 and 14288). That violates the one-heavy-build-at-a-time
  rule stated in §5 below; the 2300 figures should be read as an upper bound on
  the time-to-death, not a clean isolated row. 2200 and T2400 were isolated.

---

## 2. What the lattice says

Read rows 1–4 as a bisection over *which symbolic dimension drives the
blow-up*, and the answer falls out of the deltas:

1. **Removing dispatch and mint-walk forking buys a later death, not
   survival.** Point 1 (row 3) pins the redeemer spine, empties the mint and
   fixes the purpose, and at a *higher* budget (2400 vs 2300) it survives 18
   min / 34.7 GB against unshaped's 13 min / 27.4 GB. The forking those pins
   remove is real but is not the driver.
2. **Closing every list spine buys a 6× longer runway and the same cliff.**
   Point 2 (row 4) adds 2/2/2/2 spine closure at the identical budget:
   113 min against 18 min, and it still detonates (32.5 GB). Spine-length
   forking is likewise real, likewise not the driver.
3. **Therefore the driver is the last symbolic dimension standing** — the CEK
   unrolling's recursion over the symbolic **`Value` maps and datum `Data`**
   inside the (now spine-pinned) entries: the CIP-153 union/lookup/aggregation
   loops forking per map slot. Every further lattice point from here converges
   to SHAPE T1R itself, which is row 5 and costs 1.51 s at budget 4400.

**The cliff shape is itself the most useful signal for upstream.** A workload
whose genuine state grows would show growth roughly proportional to progress;
these runs sit *flat* for the overwhelming majority of their life (2200 spends
~94% of 47 minutes pinned at ≈5.2 GB) and then gain 7–19 GB in under three
minutes. That signature — a stable working set followed by a terminal
super-linear burst — reads much more like **lost term sharing** (a DAG being
materialised as a tree as the residual is normalised/copied) than like real
state growth. We are not claiming to have proven that; it is the hypothesis
the profile should test first.

**The middle regime is empty on this hardware.** Between "closed `Data`
skeleton, 1.51 s" and "anything symbolic below the values, OOM" there is no
measured intermediate that survives — checked three ways (unshaped @2200,
@2300; partial skeleton @2400 twice). There is no partial-shaping ladder to
climb on 61 GB.

---

## 3. Consequence for P1

* P1's non-vacuity floor is **2288 CEK steps** — `WSC.P1RShapedWitness.K_T8R_is_2288`,
  the cheapest measured accepting *registered* transfer. Below it, any
  P1-class statement over a real prep is empty (BENCHMARK-PREP §4, §7.3).
* Prep cost is monotone in the budget. Row 1 shows **2200 already dies**, and
  2200 < 2288.
* Therefore: **no P1-class unshaped statement, and no P1-class partial-skeleton
  statement, is stateable against a real prep of this validator on this class
  of hardware — at any budget at which it would be non-vacuous.** Not "slow":
  not stateable. The 2400 rows close the partial-skeleton escape hatch that
  BENCHMARK-PREP §5 had not yet tested.
* Gating is consequently **100% upstream**. No amount of proof engineering,
  statement restructuring, wall-clock patience or lattice search on our side
  moves this rung; see §6.

---

## 4. What IS attainable today

The same-day campaign also established a technique that *does* work at the one
unshaped budget where the prep completes (1600, the only accept-capable
unshaped prep of this validator — accepting runs exist at K = 1402 post-#112,
pinned two-sided by `P5ShapedWitness.K_is_1402`;
`WSC.NonVacuity.globalNonVacuous_at_1600`): **statement-level destructuring**,
i.e. putting the concrete `Data` skeleton inside the `prop` application in the
theorem, so `blaster` sees one goal with the tag already concrete, rather than
`cases`-ing in tactic mode and multiplying the 1600-step residual per branch.

| module | claim | outcome | wall | MaxRSS |
|---|---|---|---:|---:|
| `WSC/Shaped/Probe/GDestructure1600.lean` (stanza A) | `SeizeAct` arm of the global validator is rejected at 1600 | **✅ Valid** | module **4.7 s**, whole build **5.11 s** (`probeA.log`) | 1,159,284 kB ≈ 1.16 GB |
| `WSC/Shaped/Probe/GDestructure1600B.lean` (stanza B) | an accepting run forces the validator's own params authentication (`phasCSH` mirror `P5.dirNodeAuthH`) on the reference input the redeemer names | **✅ Valid** | module **≈37 min**; the log's whole-build line reads **2088.37 s ≈ 34.8 min** (`probeB2.log`) — the module header quotes 2210 s; the two disagree by ~2 min and we have not reconciled them, so read "≈35–37 min" | 4,920,036 kB ≈ 4.9 GB |

| `WSC/Shaped/Probe/GDestructure1600C.lean` (stanza C) | an accepting run whose redeemer positionally claims `NonMember` for its one minted policy (node index 1 literal, params index 0 literal) really references an authenticated covering directory node — P5's escape-critical postcondition, `P5.dirNodeAuthH` ∧ `P5.coversCS` | **✅ Valid** | module **90–102 s** across four runs (`g1600C-run*.log`) | ≈7.4 GB |

**The per-leaf cost rule this table teaches (added 2026-08-02, after stanza C
landed):** leaf cost is NOT monotone in claim strength — stanza C proves a
strictly stronger claim than stanza B over a more constrained skeleton and is
**~21× faster** (≈100 s vs ≈35 min). What dominates is how much of the
1600-step residual the skeleton folds away *before* the SMT query forms:
pinning `txInfoMint` to a single entry and the purpose to `.RewardingScript`
collapses the mint walk and the purpose dispatch, which stanza B's wider class
leaves symbolic. Practical rule for future stanzas: **cut the narrowest
statement-level skeleton that still carries the content first; widen
afterwards, one dimension at a time, re-measuring each step.** (Whether this
rescues an UNPINNED redeemer index — shape G3's `⚠️ Undetermined` at 906 s,
SHAPING-RESULTS.md §2.4 — is an open, cheap-to-run question.)

Both A and B were run under `ulimit -v` (14 GiB for A, 28 GiB for B run 2). Stanza B's
**run 1 at a 14 GiB cap OOM-panicked at 1374 s / 5.17 GB RSS** (`probeB.log`,
`EXIT=1 WALL=1374.09s MAXRSS=5166404kB`): the *virtual*-memory cap fired in the
post-Z3 phase at only ~5 GB resident, because lean's virt runs 2–3× RSS there.
That is a cap-sizing failure, not a workload wall — do not cite it as a cliff
data point. (Also: the `Name.append`/`EnvExtension` panic texts in these logs
are replayed stored messages from `Contexts.olean` and appear identically in
the *successful* stanza-A log. Not failures.)

Price of the technique: ≈4.7 s for a content-free leaf, ≈35–37 min / ≈5 GB for
a content-carrying one — roughly three orders of magnitude above the issuance
policy's ≈2 s leaves at budget 900 (`P4_MintingIdx`), the scaling being
residual size. Finite, but it prices a multi-leaf P4-style case tree out:
**one statement-level stanza per module.**

Separately, the **translation** blocker of BENCHMARK-PREP §6.4
(`translateRecFun: … eqData`) now has a repair in hand:
`WSC/Benchmark/P1LkVocab.lean` supplies `inSumLk` (the input-side twin of
`WSC/Model/Ground.lean`'s `outSumLk`, computed via PCB's `lookupDataOuter`,
which destructures the key before comparing and so never forms an `eqData`
application) plus the kernel bridge back to the published `Model.Contained`.
So the conclusion vocabulary for an unshaped P1 stanza is ready and
kernel-related to the published model — it is only the *prep* that cannot be
built. Worth stating plainly for the hand-off: **two of P1-unshaped's three
walls (translate, and — at 1600 — solve) now have answers; the prep wall is
the one that is upstream.**

---

## 5. Reproduction — and the mandatory safety discipline

⚠️ **An uncapped run of these preps took the whole 61 GB WSL VM down** (row 2′:
kernel `Out of memory: Killed process … (lean) … anon-rss:46047640kB`, box
restarted, logs of the concurrent session destroyed). Every rule below exists
because of that event. They are not optional.

1. **Always `ulimit -v`.** Set it in the same subshell as the build, never
   rely on cgroups or on watching the run. Sizes actually used:
   32 GiB (@2200), 34 GiB (@2300), 42 GiB (@2400 ×2), 14/28 GiB (probes).
   A cap that fires produces `INTERNAL PANIC: out of memory` from lean itself
   — a clean, attributable, box-preserving death. Prefer a cap that is too
   small (you get a re-run) to no cap (you get a reboot).
   Note the corollary from §4: `ulimit -v` bounds **virtual**, and lean's virt
   runs 2–3× its RSS in the post-Z3 phase, so size the cap against ~3× the RSS
   you expect, not against the RSS.
2. **One heavy build at a time.** The 2300 row is contaminated by an
   overlapping probe (§1.1) and the 46 GB kill's victim is unattributable
   *because* two heavy builds were live. Serialise.
3. **Redirect to a durable log file directly** (`> …/prep2300.log 2>&1`), not
   through a pager or a terminal buffer — the VM can die mid-run and take
   scrollback with it. `.lake/wsc-probe-logs/` is the campaign's log dir.
4. **Record `EXIT`/`WALL`/`MAXRSS`** by wrapping in `/usr/bin/time`; that trailing
   line is the only figure that survives a partial log.
5. **Explicit `timeout:` on every `blaster` call, ≤ 900 s** (house rule for the
   probe modules; `maxHeartbeats 0` at the module level, so the blaster timeout
   is the only bound on the solver phase).
6. **Run an RSS sampler** alongside (`leanmon.log` format: timestamp, pid, RSS,
   module) — the *shape* of the curve is the finding, and `MAXRSS` alone
   cannot show a cliff.

Shape of the invocation used for the rows above:

```bash
( ulimit -v $((34*1024*1024))            # KiB; 34 GiB — size per §5.1
  /usr/bin/time -f 'PREP2300 EXIT=%x WALL=%e MAXRSS=%MkB' \
    lake build WSC.Benchmark.CostG2300 \
) > .lake/wsc-probe-logs/prep2300.log 2>&1
```

Substitute per row: `WSC.Benchmark.CostG2200` (32 GiB),
`WSC.Shaped.Probe.GPrepT2400` / `…GPrepT2400B` (42 GiB),
`WSC.Shaped.Probe.GDestructure1600` (14 GiB),
`WSC.Shaped.Probe.GDestructure1600B` (**28 GiB — 14 GiB is known to fire**).
Each is a `⛔ NOT IMPORTED BY ANYTHING` module built deliberately by name;
nothing in the live build depends on them.

---

## 6. The upstream ask — for `input-output-hk/Lean-blaster#138`

The issue already records the symbolic CEK unroller's **time** curve on a
synthetic workload (fuel 51 → 5.5 s, 501 → 171 s, 10000 → killed at 628 s, hot
path `CekMachine.runSteps.match_1`, `step.match_3`, `evalBuiltin.match_1`).
BENCHMARK-PREP §7 corroborated it with a production validator and a real proof
obligation. **This document adds the memory dimension, and it is the binding
one.**

Concretely, what we are asking for:

> **Memory and term sharing in `Optimize.main`'s symbolic CEK unroll.** The
> workload is `#prep_uplc` over `programmableLogicGlobal` (3444 term nodes, 282
> builtin occurrences, 46 of them CIP-153 `Value` builtins) with a symbolic
> `ScriptContext`. Profile target: the **terminal burst**, not the steady state.
> Reproduce with `WSC/Benchmark/CostG2200.lean` — it sits flat at ≈5.2 GB for
> ~44 minutes and then gains >15 GB in the final ~3 minutes before the allocator
> fails at 21.6 GB. That profile is cheap to attach a heap profiler to (the
> interesting window is the last 5% of the run) and the flat prefix strongly
> suggests residual **sharing loss** — a shared DAG being copied out as a tree —
> rather than genuine state growth. If that is right, the fix is a
> representation/hash-consing change in the unroll, not a constant-factor tune.

Supporting data to attach: the five-point table of §1, the cliff trajectories of
§1.1, and the bisection of §2 (which localises the driver to the recursion over
symbolic `Value` maps / datum `Data`, since pinning dispatch, the mint walk and
all four list spines each only *delays* the same death).

**The size of the improvement required is unchanged from BENCHMARK-PREP §4 —
roughly two orders of magnitude** (unshaped prep dies at ≈2200–3300; the goal
rung, the mainnet ex-unit ceiling, is 300,000) — **but it now has a second
axis.** Time alone is not the constraint: 2200 would have been affordable at 47
minutes had it not needed 21.6 GB, and 2400-with-spines-pinned ran happily for
113 minutes before detonating. A fix that only makes the unroll faster, without
changing its allocation behaviour, moves nothing here.

Finally, the non-vacuity floor from BENCHMARK-PREP §7.3 still bounds what is
worth optimising *for*: an unroller improvement that lands below **2288** buys
this artifact literally nothing, because the P1 theorem would remain vacuous.
The first meaningful milestone is unchanged — **make anything at or above 2288
prep at all** — and §1's table is now the evidence that it cannot be reached by
shaping cleverness on our side.
