# WSC containment campaign — FINAL AUDIT (sealed at E5, re-sealed at G3)

> # ⚠️ REVISION N6 (2026-07-28) — RE-BASED ON wsc-poc `main` @ **2306678** (PR #112)
>
> **EVERYTHING BELOW THIS BANNER WAS WRITTEN AGAINST THE PRE-#112 BYTECODE.**
> wsc-poc PR #112 ("Seize path: per-pair value delta via CIP-153 builtins,
> witnessed base delegation") is a SEMANTIC change to three of the four
> validators. Measured `sha256` of the exported `cborHex`, `f918ec6` → `2306678`:
>
> | validator | before | after | |
> |---|---|---|---|
> | `programmableLogicBase` | `1881821b7a2c…` | `a9e7364b519a…` | **CHANGED** — new redeemer TYPE (`BaseSpendRedeemer`), scan → index |
> | `programmableLogicGlobal` | `ddd6f7df4278…` | `eed62d595f56…` | **CHANGED** — `PTransferAct` gained `ownerWdrlIdxs` |
> | `programmableSeize` | `289e9e8d18b8…` | `350b58d7b322…` | **CHANGED** — per-pair delta via CIP-153 builtins |
> | `programmableTokenMinting` | `7274240514ff…` | `7274240514ff…` | **byte-identical** |
>
> Tasks N1–N6 re-based the substrate, regenerated the goldens, re-measured K, and
> re-proved P1, P2, P3, P5, P6 and both composed results. **The current numbers
> are these; the ones in the body are the pre-#112 record and are kept so the
> history is visible:**
>
> | measurement | pre-#112 (H2/G3) | **post-#112 (N6, two clean-room runs)** |
> |---|---|---|
> | exit status | 0 — 431 jobs | **0 — 440 jobs, both runs** |
> | solver verdicts | 162 = 103 V + 59 F | **170 = 108 `✅ Valid` + 62 `✅ Expected Falsified`**, identical both runs |
> | `⚠️ Undetermined` / `❌` | 0 | **0** |
> | `error:` lines | 0 | **0** |
> | `declaration uses 'sorry'` | 20 | **20** |
> | `unused variable` | 5 | **5** |
> | WSC modules re-elaborated | 93 | **102** |
> | user + sys CPU | 466–515 + 64–70 s | **1205.8 + 127.8 / 1197.1 + 121.2 s** |
> | shapes in `recutFamily` | 13 | **14** — SHAPE T8R joined (N6); every `not_covers_*` is now over a strictly larger family |
> | free leaves across the family | 458 | **500** |
> | wall clock | 1:46 – 2:10 | **10:36.40 / 10:33.89** ⚠ — ~9 min of it is `WSC.Prep.Global1600` alone (measured live at 94 % CPU, 4.2 GB RSS) |
> | max RSS | 1.65 GB | **4.34 / 4.26 GB** ⚠ — plan for 5 GB |
> | project axioms under each composed result | 28 | **28 — UNCHANGED** |
> | leaves discharged BY THE BYTECODE | 1 of 4, each side | **1 of 4, each side — UNCHANGED** |
>
> **THE SEVEN THINGS A READER MUST TAKE FROM THIS BANNER**
>
> 1. **Both composed results survive**, over the same classes, with the same
>    1-of-4-by-bytecode ratio and the same 28 project axioms — but `top_claim` now
>    carries **one new hypothesis**, `WdrlPairShaped Shape`: *every transaction of
>    the class has a two-entry, both-script withdrawal map*. #112 made the base
>    validator index into `txInfoWdrl` instead of scanning it, and a symbolic index
>    into a symbolic-LENGTH list does not close. Both composed classes satisfy the
>    new hypothesis by `rfl`, so nothing was lost at the instantiation — but the
>    reduction itself is narrower and the narrowing is in the type.
> 2. **P3 lost its special status and got most of it back.** §7 of `COVERAGE.md`'s
>    "the only property proved over a covering class" is FALSE of production. What
>    replaced it is SHAPE **B1W** — P3 over `WSC.WdrlPair` with the redeemer, both
>    script parameters and every other `TxInfo` field still symbolic — and that
>    class is the ONLY one in the campaign with a complete both-directions
>    ledger-vocabulary characterisation (`Coverage.wdrlPair_char`). Measured
>    boundary: withdrawal maps of length 1 and 2 close; length 3 returns no verdict
>    at a 900 s cap.
> 3. **One result was genuinely REFUTED, and it is not a regression in the proof —
>    it is a behaviour change in the code.** #112 deliberately legalised an ada
>    top-up on the seize path's continuing output. P2's structure conjunct as
>    previously stated ("every non-seized policy equal, ada included") is now FALSE
>    of production; task N5 restated it over `seizeStructurePreservedAdaTopUp` and
>    proved the relaxation is one-directional (`P2a_R_ada_only_tops_up`: acceptance
>    forces `i0Ada ≤ o0Ada`). `WSC/Props/Shaped/P2Shaped.lean` was DELETED for the
>    same reason and `WSC/Model/SeizeModel.lean`'s `seizeModel_faithful` is
>    **refuted by computation** (`WSC/Model/SeizeModelRefuted.lean`), which costs
>    the library its only UNBOUNDED seize result.
> 4. **The substrate pin got worse, not better — and BOTH dependencies are now
>    unpublished local paths.** Pre-#112 only `programmableLogicGlobal` needed the
>    unpublished `cip153-value-builtins` PlutusCoreBlaster branch, and Blaster was
>    a public git rev. Post-#112 **`programmableSeize` needs PCB too** — and needs
>    a builtin (`ScaleValue`, flat tag **100**) that was not in the branch until
>    task N5 added it — while **Blaster moved to an unpublished local branch** for
>    the D6 fix. Two of four production validators fail to DECODE on stock PCB, and
>    three of six properties are **unstatable** without the Blaster commit. Neither
>    pin is machine-enforced: `lake` does not verify the `rev` key on a `path`
>    entry. Task N6 added the missing offline artifacts (`WSC/substrate/`
>    previously had NONE for Blaster, so it did not in fact reconstruct the
>    substrate); both were verified against local repos only, never against a fresh
>    clone. See `WSC/pr/01-pcb-cip153-value-builtins.md` and `WSC/REPRODUCE.md` §1b.
> 5. ~~**NEW FINDING F23: SHAPE T8R is below the four-point bar**~~ — **CLOSED at
>    task H1 (2026-07-28); the strike-through is the correction, and the finding as
>    stated at N6 was accurate when written.** T8R had its theorem and its vacuity
>    probe and no CEK witness and no realizability certificate; it now has both, so
>    the campaign is at **14 of 14** on the four-point bar and the objection "the one
>    shape that exercises the line #112 added is also the least evidenced one" is
>    answered. Numbers, all measured at H1:
>    * acceptance `P1RShapedWitness.exec_accepts_T8R_at_4400`
>      (`WSC/Props/Shaped/P1ShapedR.lean:1011`), through the SAME applied term
>      `P1R_T8` quantifies over — sameness proved twice by `rfl`, class level
>      (`p1SOwnInputs_eq_globalInputs`, `:970`, every leaf assignment) and point
>      level (`ctxSOwn_is_the_exec_argument`, `:989`);
>    * **K = 2288, pinned TWO-SIDED** (`K_T8R_is_2288`, `:1036`) — **55 steps BELOW
>      T1R's 2343** at otherwise identical leaves, so #112's indexed owner lookup is
>      CHEAPER than the signature check beside it despite one more withdrawal entry;
>    * realizability `WSC.t8R_realizable`
>      (`WSC/Props/Shaped/GlobalRealizability.lean:939`) — `validRewardingContext` ∧
>      `redeemersExactAllPlutus` (BOTH halves of Conway's rule; 4 entries = 1 script
>      input + 0 mint policies + 3 script withdrawals, exact) ∧ `RedeemerCovered` ∧
>      real-CEK acceptance — with class-level `t8R_class_covered` (`:508`) and
>      `t8R_class_coverage` (`:728`);
>    * and TWO rejecting siblings that make `ownerWdrlIdxs` EARN its theorem:
>      `exec_rejects_T8R_misindexed_owner` (`:1059`) and `…_unwitnessed_owner`
>      (`:1077`). Both differ from the accepted witness in the SINGLE leaf `sOwn`,
>      both are `validRewardingContext` AND `redeemersExactAllPlutus`
>      (`t8R_rejected_members_are_ledger_legal`, `GlobalRealizability.lean:977`),
>      and the real bytecode refuses both. The first is the sharp one: its owner's
>      stake script IS invoked, at withdrawal entry 1, while the redeemer names
>      entry 2 — which is exactly what the pre-#112 membership scan accepted.
>
>    0 project axioms on all of it, **0 new solver verdicts** (every new result is
>    `native_decide` or `rfl`), verdict total unchanged at **170**. See
>    `WSC/STATUS.md` §6 T8R stanza and §7 row F23;
>    `WSC/status-fragments/N6-compose-and-reaudit.md` §1 for the original finding.
>
> 5b. **NEW FINDING F24, found while closing F23 — `globalModel_faithful` is FALSE
>    of the post-#112 program and now has an executable counterexample.**
>    `WSC/Model/GlobalModel.lean:668-676` already stated in a COMMENT that the model
>    binds `ownerWdrlIdxs` as `_ownerWdrlIdxsUnmodelled` and still transcribes the
>    pre-#112 withdrawal-map SCAN (`gateInput`, `:231-233`).
>    `P1RShapedWitness.model_is_stale_at_ownerWdrlIdxs` (`P1ShapedR.lean:1110`)
>    turns that comment into a measurement, and the measurement shows the error runs
>    in the DANGEROUS direction: on `ctxSOwnMisindexed` the model **accepts** and the
>    real bytecode **rejects**, so `WSC.Model.globalModel` is UNSOUND — not merely
>    incomplete — at the one line #112 added, and the axiom
>    `WSC.Model.globalModel_faithful` (`WSC/Props/P1_Transfer.lean:428`) is refuted
>    by a concrete context. Scope: the SHAPED P1/P5/P6 results do NOT route through
>    that axiom (`WSC/Shaped/Probe/P1Axioms.lean` is the census showing it absent);
>    anything built on `P1_model` does. `WSC/STATUS.md` §7 row F24.
>
> 6. **Defect D6 is FIXED, and half of what it justified is withdrawn.** Blaster
>    `4d320dd` repairs the kernel-ill-typed `dite'`; both reproductions
>    (`T3PrepFAILS`, `T4PrepFAILS`) now BUILD and are relabelled as regression
>    tests. The campaign's standing claim that P1's containment dispatch **Paths B
>    and C are "unreachable at UPLC at any shape" is therefore FALSE and is
>    withdrawn** — SHAPE T3's accept class is measured non-empty
>    (`T3_vacuity_probe`, `✅ Expected Falsified`, 4.6 s). But they are still not
>    PROVED, for a different and much cheaper reason: T3/T4 are pre-re-cut and not
>    node-realizable (T3 needs 3 redeemer entries, supplies 1), so they need a
>    **T3R/T4R re-cut** that does not exist. "D6 is fixed" must not be read as
>    "the dispatch paths are verified".
> 7. **`recutFamily` grew 13 → 14** (SHAPE T8R, 42 free leaves; total 458 → 500).
>    Because §6's results are REFUTATIONS, a larger family makes every one of them
>    **strictly stronger** at no witness cost. ~~The roster is deliberately no longer
>    called "N node-realizable shapes": thirteen carry a certified inhabitant and
>    T8R does not (F23, item 5).~~ **CORRECTED at task H1: all FOURTEEN now carry a
>    certified inhabitant** (`WSC.t8R_realizable`), so "fourteen node-realizable
>    shapes" is again the accurate description of the roster.
>
> Per-task detail: `WSC/IMPACT-PR112.md` (N1–N5 appendices) and
> `WSC/status-fragments/N6-compose-and-reaudit.md` (the existence check, the
> composition restoration, the clean-room numbers, and the KEEP/DELETE table).


---


**What this file is.** The authoritative statement of what is and is not
established, and the last technical gate before the campaign is quoted outside this
repository. Nothing below is taken on any earlier agent's word — including the four
stage-11 agents (E1, E2, E3, E4) whose work the E5 seal gated, and the two G-stage
agents (G1, G2) whose work **this** revision gates. Every number was re-measured, in
three independent clean-room rebuilds at E5 and **two more at G3**, all on
2026-07-25; every claim that could not be reproduced is corrected in place and
listed in §8.

**This revision SUPERSEDES the C4 audit**, which superseded A3, which superseded U3.
Their bodies are folded in finding by finding; the originals remain in `git log`
(`300f9e0`, `416087d`). Where this audit disagrees with C4 the disagreement is
stated, not patched over. **§1, §3, §4 and §7 were re-measured at G3 (`f4486ca`) and
two E5 numbers are corrected there**, both flagged in place.

Audited revision: branch `wsc-containment-proofs`, **HEAD `f4486ca`** (G1's commit,
on top of G2's `9e5d417`, on top of E5's `7039cdb`), tree clean. The E5 body below
was written at `7039cdb`; every measurement in §1, §3 and §4 has been re-taken at
`f4486ca` and the tables carry both columns.

> **⚠️ ONE REVISION LATER — THE DEAD-FILE CLEANUP (task H2).** Five modules were
> deleted for PR submission. **Every verdict survived**: the clean-room rebuild
> still reports **162 verdicts (103 ✅ Valid + 59 ✅ Expected Falsified), 0 errors,
> 0 ⚠️/❌, 20 `sorry` warnings, 5 unused-variable**, and the per-verdict source
> reconciliation is still exactly 59 + 2 + 101. Four numbers in this file moved and
> **all four are flagged in place below**: jobs **432 → 431**, WSC modules
> **94 → 93**, `#print axioms` results **174 → 172**, `native_decide` results
> **72 → 70** and zero-project-axiom results **124 → 122**. The full decision table
> — every file in the tree, KEEP or DELETE, with the reason — is **§12**. Read it
> before concluding that anything went missing.
Environment: 32-core box, Lean 4.24.0, Z3 4.15.2, `maxHeartbeats 0`,
Blaster git `59db213ca6396269d2606b7dd9ac2bc26ae7c4ce` (branch
`beta-lambda-cache-optimization`, pinned by rev in `lake-manifest.json`),
PlutusCoreBlaster by local path at rev `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`
(branch `cip153-value-builtins`, unpushed — see §6.2).

**THE HEADLINE CHANGES SINCE C4.**

1. **Audit F1's obligation gap is closed: N = 0.** There is now a `LeafSet` with
   **no** remaining leaf hypothesis, over a class that is not empty — and a **second**
   one for the seize purpose. But the number that matters is not N; it is the
   **ratio**, and it is measured in §3.4: *on each side, one of four leaves is the
   production bytecode and three are the shape.*
2. **The most damning practical caveat, D5, is materially repaired.** The substrate
   is now pinned by revision in three places and carries an offline `git bundle`
   that this audit independently applied and byte-compared. It is not fully closed —
   the branch is still unpublished.
3. **Shape coverage is now stated in Lean, and it is PROVED FALSE** at the smallest
   bound the family already covers, with three node-realizable transactions the real
   bytecode accepts in exactly the certified witness's 2,603 steps.
4. **One stage-11 unit delivered nothing at all** (§7.2, finding **F20**), so F17,
   F18 and F19 were all still open when the E5 seal was written. F17 was **measured
   and answered** there, though not landed as a theorem.
5. **ADDED AT G3 — all three of F17, F18, F19 are now CLOSED, and this time the work
   EXISTS.** §7.6 is the existence check, done before anything else was believed,
   because F20 is the reason the G stage was run at all.
   * **F17 LANDED** by G1 (`f4486ca`): `M2RWitness.exec_accepts_at_900` and
     `K_is_784` pinned two-sided, in `P4ShapedRIdx.lean`. SHAPE M2R now meets 4/4,
     so **every re-cut shape in the library meets the full four-item bar** — with
     F19's L2R that is **13 of 13**, and there is no longer a 3/4 row.
   * **F18 RESOLVED** by G2 (`9e5d417`): the faithful rule is not expressible in
     `TxInfo`, so the predicates are renamed `…AllPlutus`, the direction of the
     error is now a pair of theorems rather than a comment, and every negative use
     is audited individually (6 unaffected, 6 downgraded with the side condition in
     the TYPE, 1 measurement re-read).
   * **F19 CLOSED** by G1: SHAPE **L2R** exists (`WSC/Shaped/MintingLocalShapedRIdx.lean`),
     is node-realizable, and carries the full four-item bar. The superseded
     `P4_local_noEscape_shapedIdx` is replaced by `P4_local_noEscape_RIdx`.
   The build moved **431 → 432 jobs and 159 → 162 verdicts**, and every unit of that
   delta is reconciled to a source line in §1.3.
6. **ADDED AT G3 — two new minor findings, F21 and F22**, both of the F20 family:
   things no existing instrument was looking at. Neither is load-bearing.

---

## 0. THE ONE-PARAGRAPH ANSWER

The library is internally consistent and its measurements reproduce. **At G3
(`f4486ca`): 432 jobs, 1 m 46 s – 2 m 10 s over two runs, 162 solver verdicts all ✅
(103 Valid + 59 Expected Falsified), zero errors, zero `⚠️ Undetermined`, zero
unexplained `sorry`s**, source reconciliation exact and now done **per verdict rather
than by totals**, and the leaf theorems say what they claim to say in ground-truth
vocabulary. (At E5 `7039cdb`: 431 jobs, 1:39–1:57 over three runs, 159 verdicts =
102 + 57. The +1 job and +3 verdicts are G1's SHAPE L2R, reconciled to three source
lines in §1.3.) Six safety properties of the four
production validators are genuinely proved against the **real compiled bytecode**,
whose provenance this audit re-verified end to end (4/4, §6.1). Three things changed
since C4 and they are the only reasons to re-read this file:

1. **Both composed results now have complete `LeafSet`s — and the honest measure is
   the ratio, not the count.** `RealizableLeaves.containment_on_realizable_class`
   (transfer, over `T1RShapeNS`) discharges `p1` from the production
   `programmableLogicGlobal` bytecode with its acceptance hypothesis **consumed**,
   and discharges `p2`, `p4`, `nopre` **from the shape**, with their acceptance
   hypotheses **unused and bound as `_`**.
   `RealizableLeaves.containment_on_seize_class` (seize, over `S1RShape`) is the
   mirror image: `p2` is the production `programmableSeize` bytecode with its
   acceptance hypothesis consumed, and the other three are the shape. **One of four
   leaves is the code, on each side.** Closing `p2` on the transfer side cost
   **nothing** in trust base — the axiom sets are set-equal, measured in §3.1.
2. **The coverage question has an answer, and it is "no".** `WSC/Coverage.lean`
   states coverage in Lean and refutes it for the twelve re-cut shapes at
   `SizeBound 2 2 2 2 0` — SHAPE T1R's own size — with three counterexamples that
   are ledger-valid, Conway-redeemer-exact, accepted by the real CEK, and cost
   **exactly 2,603 steps**, byte-identical to the certified inhabitant. The machine
   cannot tell them apart from a covered transaction; only the skeleton can. No
   project axiom, no `sorryAx`.
3. **Reproducibility moved from "one machine" to "one machine plus a verified
   artifact"** (§6.2).

The top-level sentence *"in an honest deployment, programmable tokens cannot exist
outside the mini-ledger"* is still **not proved**, and the reasons are now sharper
rather than merely structural: there is no shape-coverage argument **and coverage is
now known to be false for this family**, every bytecode result is still bounded twice
(a CEK step budget AND a fixed `Data` skeleton), and 28 project axioms plus `sorryAx`
still stand under both composed results. The deliverable is: six real, controlled,
non-vacuous properties of the production bytecode over named bounded families that
are node-realizable; a machine-checked reduction of the top claim to four leaf
obligations plus 28 axioms; that reduction discharged **completely** over two
realizable classes, with one quarter of the work done by the code on each; and a
machine-checked refutation of the coverage step that would connect the two. Not the
claim.

---

## 1. CLEAN-ROOM REBUILD

### 1.1 Method

```
cp -a /home/gumbo/iohk/CardanoLedgerApiBlaster <SCRATCH>/clab-E5
cd <SCRATCH>/clab-E5
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.olean \
       .lake/build/lib/lean/WSC.ilean .lake/build/lib/lean/WSC.olean.hash \
       .lake/build/lib/lean/WSC.ilean.hash .lake/build/lib/lean/WSC.trace
/usr/bin/time -v lake build WSC WSC.ShapeBridge
```

Dependency oleans (`CardanoLedgerApi` and the `PlutusCore` / `Blaster` packages under
`.lake/packages`) were **kept**; every `WSC.*` olean/ilean/trace was deleted. That is
the right cut and a full `lake clean` is not needed: no WSC verdict is computed in a
dependency module — every `#import_uplc`, `#prep_uplc` and `#blaster` lives in a
`WSC/` module — so deleting the WSC oleans forces all of them to run for real.
Confirmed by the log: **93 distinct `WSC.*` modules re-elaborated** (94 at G3;
**93 again after the H2 cleanup**, and the two must not be confused — E5's 93 and
H2's 93 are different sets), including all
shaped/unshaped `#prep_uplc` modules, all 4 `#import_uplc` sites, and all solver
invocations (159 at E5, **162 at G3**).

**Run 3 was executed after this task's own changes were applied** (§6.2), to confirm
they are inert with respect to the build. They are.

**G3 re-ran the identical recipe TWICE at `f4486ca`**, in a fresh `cp -a` workspace
(`clab-G3`); the canonical repo was never built in. Both G3 runs exited 0.

### 1.2 Result, against the audited baselines

| measurement | A3 (`80cdac7`) | C4 (`300f9e0`) | E5 (`7039cdb`) | **G3 (`f4486ca`, 2 runs)** | **H2 (dead-file cleanup)** |
|---|---|---|---|---|---|
| exit status | 0 — 405 jobs | 0 — 429 jobs | 0 — 431 jobs | **0 — `Build completed successfully (432 jobs)`, both runs** | **0 — 431 jobs** (−1 = the deleted `WSC.Props.P5_Witness1600`) |
| wall clock | 1 m 38.50 s | 1 m 30.22 / 1 m 42.57 s | 1:39.29 / 1:46.56 / 1:57.07 | **1 m 46.22 s / 2 m 09.91 s** (**quote 1:46–2:10**, never a point; the box was running concurrent agents) | 1 m 49.01 / 2 m 00.03 s over two runs (its own pre-change control run on the same box, same load: **2 m 35.84 s** — so **do not read this as a speed-up**; RSS/wall remain machine measurements, §1.2 note) |
| user + sys CPU | 275.9 + 33.6 s | 380.4 + 56.6 s | 402.7–434.9 + 50.3–54.0 s | **466.7–515.0 + 64.3–70.3 s** (450–499 %) | 478.0 + 58.4 s (control: 584.7 + 83.9 s) |
| max RSS | 1.65 GB | 1.65 GB | 1.50–1.52 GB | **1.652–1.658 GB** — see the note below; **not** attributable to G1/G2 | 1.643–1.647 GB (control 1.656 GB) |
| WSC modules re-elaborated | 67 | 90 | 93 | **94** (+1 = `WSC.Shaped.MintingLocalShapedRIdx`) | **93** (−1, and it is a *different* set from E5's 93) |
| `error:` lines | 0 | 0 | 0 | **0** (hard requirement — met, both runs; but see **F21**) | **0** |
| solver verdicts | 101: 66 V + 35 F | 158: 101 V + 57 F | 159: 102 V + 57 F | **162: 103 `✅ Valid` + 59 `✅ Expected Falsified`** (identical in both runs) | **162: 103 V + 59 F — UNCHANGED. This is H2's acceptance criterion and it is met.** |
| `⚠️ Undetermined` / `❌` | 0 | 0 | 0 | **0** (both runs) | **0** |
| `declaration uses 'sorry'` | 20 | 20 | 20 | **20** (census §2, unchanged) | **20** |
| `unused variable` | 5 | 5 | 5 | **5** — still all at `Composition.lean:2442-2446` (§5.4) | **5**, same lines |

**On the RSS regression, 1.50 → 1.65 GB.** It is **not** G1's or G2's doing and G3
did not take it on trust. G2 independently stashed its own work and rebuilt
unmodified `7039cdb` under the same machine load, measuring **123.15 s / 1,643,188
KB** — i.e. the 1.65 GB figure reproduces at the E5 revision when other agents are
running concurrently. E5's 1.50 GB was measured on a quiet box. The correct
reviewer-facing statement is **"1.50–1.66 GB, load-dependent"**, and peak RSS is
hereby demoted from a campaign instrument: it measures the machine, not the library.

### 1.3 The verdict delta reconciles exactly

**`159 → 162` at G3 is `+3`, and every one is pinned to a source line** (this is the
F20-proof form of the check: it names the line, so a unit that did nothing cannot
pass it):

* **G1** (`f4486ca`): **+1 module, +3 verdicts.**
  * `P4LocalShapedR.lean:597` — `blaster (timeout: 300)` closing
    `P4_local_RIdx_negative_control` → **+1 `✅ Valid`**. (Note this is a *sixth*
    `:= by`-newline site; see §1.4.)
  * `P4LocalShapedR.lean:677` — `#blaster (timeout: 300) (gen-cex: 0) (solve-result: 1)
    [P4_local_RIdx_tightness]` → **+1 `✅ Expected Falsified`**.
  * `P4LocalShapedR.lean:708` — the same form for `[P4_local_RIdx_vacuity_probe]`
    → **+1 `✅ Expected Falsified`**.
  * The **F17** paste (`P4ShapedRIdx.lean`, `M2RWitness`) adds **0** verdicts: it is
    `native_decide` throughout, and `P4ShapedRIdx.lean` still contributes exactly
    3 V + 2 F.
  * `WSC/Shaped/Probe/L2RProbe.lean` exists but is **deliberately not imported**
    into `WSC.lean`, following the house convention for probe modules carrying
    `⚠️ Undetermined` verdicts. Verified: it appears nowhere in the marker table,
    and the built set has 0 Undetermined.
* **G2** (`9e5d417`): **+0 modules, +0 verdicts** — every new result is ordinary
  Lean (`rfl`, `decide`, term proofs) and the six retargeted emptiness theorems keep
  their existing tactic proofs. Verified by differencing the per-file table:
  `ShapeRealizability.lean` and `GlobalRealizability.lean` contribute 0 markers
  before and after.
* **G3** (this task): **+0 / +0** — documentation only.

`102 + 1 = 103` ✅ Valid and `57 + 2 = 59` ✅ Expected Falsified. **432 = 431 + 1**
module.

The E5-era reconciliation of `158 → 159` is retained below, unchanged:

* **E1** (`ad0e2e9`): **+1 module, +1 verdict** — `bridge_S1R`, 1 `✅ Valid` at
  `RealizableLeavesS1R.lean:166`. Everything else E1 added in both modules is
  ordinary Lean, `rfl`, or `native_decide`. Verified by differencing the per-file
  marker table: `RealizableLeaves.lean` still contributes exactly 1.
* **E4** (`4919968`, `8163803`): **+1 module, +0 verdicts** — `WSC/Coverage.lean`
  runs no solver at all. Verified: it appears nowhere in the marker table.
* **E2**: **+0 / +0** — it produced nothing (§7.2).
* **E5** (this task): **+0 / +0** — documentation and the substrate artifact only.

`101 + 1 = 102` ✅ Valid and `57 + 0 = 57` ✅ Expected Falsified.

Per-file marker table, complete (regenerable from the log), **at G3 `f4486ca`**; the
only row that moved since E5 is `P4LocalShapedR.lean`, **6 V + 2 F → 7 V + 4 F**:

| file | ✅ Valid | ✅ Expected Falsified |
|---|---|---|
| `WSC/ShapeBridge.lean` | 19 | 6 |
| `WSC/Props/Shaped/P4DelegateShaped.lean` | 7 | 4 |
| `WSC/Props/Shaped/P4DelegateShapedR.lean` | 7 | 4 |
| `WSC/Props/Shaped/P4LocalShaped.lean` | 7 | 3 |
| **`WSC/Props/Shaped/P4LocalShapedR.lean`** | **7** | **4** |
| `WSC/Props/Shaped/P1Shaped.lean` | 5 | 5 |
| `WSC/Props/Shaped/P1ShapedR.lean` | 5 | 5 |
| `WSC/Props/Shaped/P2Shaped.lean` | 5 | 3 |
| `WSC/Props/Shaped/P2ShapedR.lean` | 5 | 3 |
| `WSC/Props/Shaped/P4Shaped.lean` | 4 | 2 |
| `WSC/Props/Shaped/P4ShapedR.lean` | 4 | 2 |
| `WSC/Props/Shaped/P4ShapedIdx.lean` | 3 | 2 |
| `WSC/Props/Shaped/P4ShapedRIdx.lean` | 3 | 2 |
| `WSC/Props/P3_Base.lean` | 3 | 2 |
| `WSC/Props/P3_BaseRun.lean` | 3 | 1 |
| `WSC/Props/Shaped/P5Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P5ShapedR.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6Shaped.lean` | 2 | 2 |
| `WSC/Props/Shaped/P6ShapedR.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Shaped.lean` | 2 | 2 |
| `WSC/Shaped/Calib/P3Unshaped.lean` | 1 | 1 |
| `WSC/Goldens/Witnesses.lean` | 1 | — |
| `WSC/Prep/Global.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/P4_Minting.lean` | 1 (vacuity BY DESIGN) | — |
| `WSC/Props/Shaped/RealizableLeaves.lean` | 1 | — |
| **`WSC/Props/Shaped/RealizableLeavesS1R.lean`** | **1** | — |
| `WSC/Coverage.lean` | **0** | **0** |
| `WSC/Shaped/MintingLocalShapedRIdx.lean` (new at G1) | **0** | **0** |
| **total (G3, `f4486ca`)** | **103** | **59** |

### 1.4 Source reconciliation — the check that rules out a skipped stanza

**G3 replaced the E5 method with a stronger one.** E5 counted stanzas in the source
and compared totals. G3 instead takes each of the 162 `file:line:col` verdicts the
log emits, reads **that exact source line** out of the built tree, and classifies
it. This is strictly better: a totals match can be produced by two compensating
errors, whereas a per-verdict map cannot, and — the F20 lesson — it names the line,
so it reports on what the log *says happened*, not on what the source *contains*.

Result, at `f4486ca`, both runs identical, **zero verdicts unclassified**:

| source construct at the verdict's own line | count | verdict |
|---|---|---|
| `#blaster … (solve-result: 1)` command | **59** | 59 × `✅ Expected Falsified` |
| `#blaster … (solve-result: 0)` command | **2** | 2 × `✅ Valid` |
| `blaster` **tactic** in theorem position | **101** | 101 × `✅ Valid` |
| anything else | **0** | — |

59 + 2 + 101 = **162**, and the per-file split matches §1.2's table one-for-one.
**No stanza is unaccounted for and none is skipped.**

The two `solve-result: 0` sites are the deliberate vacuity assertions:
`WSC/Prep/Global.lean:83` `global_vacuity_probe_600` and
`WSC/Props/P4_Minting.lean:386` `minting600_is_vacuous`.

> **The `:= by`-newline trap — count is now SIX, not five.** E5 recorded 5 tactic
> sites written `:= by` with `blaster` indented on the following line, which a naive
> one-line grep misses. G1 added a sixth. The complete list at `f4486ca` is
> `P3_Base.lean:210`, `P3_BaseRun.lean:93,112,141`, `Goldens/Witnesses.lean:152`,
> and **`P4LocalShapedR.lean:597`** (`blaster (timeout: 300)`). Any auditor who
> greps for `by blaster` on one line will land on **156**, not 162. Note also that
> the sixth carries an argument, so a grep for the bare token `blaster$` misses it
> too — this is why G3 stopped grepping the source and started reading the line the
> log points at.

### 1.5 Slowest cold modules

At **G3 (`f4486ca`, run 1, box under concurrent load** — these are in-parallel wall
times and are not comparable across runs):
`WSC.Prep.Global1600` 57 s, `WSC.ShapeBridge` 45 s,
`WSC.Shaped.MintingLocalShapedIdx` 40 s, **`WSC.Shaped.MintingLocalShapedRIdx` 38 s**
(new at G1 — SHAPE L2R; it is now the fourth most expensive module in the build),
`WSC.Props.Shaped.P2Shaped` 33 s, `WSC.Props.Shaped.P2ShapedR` 22 s,
`WSC.Props.Shaped.RealizableLeavesS1R` 20 s, `WSC.Props.Shaped.RealizableLeaves`
19 s, `WSC.Prep.Minting1300` 9.6 s, `WSC.Composition` 6.0 s. Everything else ≤ 7 s.

E5's quiet-box figures, for comparison: `Prep.Global1600` ≈ 42 s, `ShapeBridge`
≈ 38 s, `MintingLocalShapedIdx` ≈ 30 s, `P2Shaped` ≈ 25 s, `P2ShapedR` ≈ 24 s,
`RealizableLeavesS1R` 20 s, `Composition` 5.4 s, `Coverage` 1.7–2.2 s.

> **A build-hazard the G stage discovered and every future rung inherits.**
> Blaster's **default solver timeout is infinity** (`Blaster/Command/Syntax.lean:15`).
> G1's first, uncapped attempt at the direct SHAPE L2R no-escape goal ground for
> **over 13 minutes** on a single Z3 before it was killed, with no diagnostic. Every
> L2R solver call in the built tree now carries an explicit `(timeout: 300)`. The
> cap is **not** a soundness hole: on `Undetermined` the tactic calls
> `goal.replaceTargetDefEq` and leaves the goal open (`Blaster/Command/Tactic.lean:47-50`),
> so the build hard-fails rather than admitting. G3 endorses this as a house rule:
> **every `blaster` call in a new shape carries an explicit cap.**

---

## 2. SORRY / ADMIT CENSUS

20 `declaration uses 'sorry'` warnings, classified — locations re-extracted from the
log, not carried over:

| class | count | detail |
|---|---|---|
| **(a)** blaster `admit` on a declaration that reported ✅ Valid | **19** | all in `WSC/ShapeBridge.lean` |
| **(b)** PCB pre-existing, not WSC code | **1** | `PlutusCore/UPLC/CekMachine.lean:299:4` — unchanged |
| **(c)** anything else = DEFECT | **0** | — |

**The warning count is NOT a census and must never be quoted as one (§8 F4).**
`grep -rl 'set_option warn.sorry false' WSC/` returns **38** modules (C4: 37; E1's
`RealizableLeavesS1R` is the +1 — `WSC/Coverage.lean` deliberately does **not**
suppress and emits zero warnings), so the ~100 further `admit`-closed theorems in
them emit no warning at all. The authoritative instrument is `#print axioms` →
`sorryAx` (§3), and by that instrument **every one of the 101 `by blaster` theorems
in the library is admit-closed.** (100 at E5; G1's L2R negative control is the
101st, and it is admit-closed like the rest.)

Literal-source grep over `WSC/**/*.lean`, comments stripped — **re-run at G3**:

* **no** literal `sorry`, `admit` or `stop` in tactic position anywhere. The
  remaining textual hits are prose inside docstrings. Verified at `f4486ca`.
* **51** `axiom` declarations: `WSC/Honest.lean` (**38**), `WSC/Composition.lean`
  (**10**), `WSC/Props/P1_Transfer.lean` (**2**), `WSC/Model/SeizeModel.lean` (**1**).
  **Unchanged by stage 11 and by the G stage** — E1, E4, G1 and G2 added none.
  In particular G2 did **not** renumber the census: it deliberately kept the name
  `LR_REDEEMER_COVERAGE` and rewrote only its *statement* and docstring, precisely
  so that this count would not move (§8 F18).
* **Zero `axiom` declarations under `WSC/Prep/`, `WSC/Shaped/` or
  `WSC/Props/Shaped/`** — machine-verified at `f4486ca`, and this is the shaped
  layer's central claim: it adds no assumption. **It survives E1, E4, G1 and G2
  intact**, including `RealizableLeavesS1R.lean` and G1's new
  `WSC/Shaped/MintingLocalShapedRIdx.lean` and its additions to
  `WSC/Props/Shaped/{P4ShapedRIdx,P4LocalShapedR}.lean`. (`WSC/Coverage.lean` is not
  under those directories; it declares no axiom either — verified.)

---

## 3. AXIOM CENSUS

> **UPDATED AT H2.** The dead-file cleanup deleted the only two `#print axioms`
> results that lived in a module with no Lean dependents, so this section's totals
> move by exactly −2: **172** results, **37** `sorryAx` (**unchanged**), **70**
> `native_decide`, **122** zero-project-axiom. The two removed are
> `WSC.Witness1600.golden_halts_at_1600` and `…golden_errors_at_1553`, both
> `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`
> — i.e. both were in the "builtins-only" bucket, which is why the `sorryAx` count
> and every project-axiom figure in §3.1–§3.4 are untouched. Re-measured with the
> two-trap-safe parser at the cleanup revision; the G3 body below is left as G3
> wrote it.

Measured at **G3 (`f4486ca`)**: the rebuild log carries **174** `#print axioms`
results, all distinct names (E5 at `7039cdb`: 173; C4: 142). Of these, **37** carry
`sorryAx`, **72** use `native_decide`, and **124** carry **zero project axioms** —
i.e. **`sorryAx` and the zero-project-axiom count did not move at all**; the single
new result is G2's `WSC.g6_class_is_empty_nonNative`, which carries one project
axiom (`WSC.OnChain`). Identical in both G3 runs.

> **Second parsing trap, found at G3.** `#print axioms` has **two** output forms.
> Most results read `'NAME' depends on axioms: [ … ]`, but a genuinely axiom-free
> declaration prints `'NAME' does not depend on any axioms` — **no brackets**. A
> parser that scans only for the bracketed form returns **169**, not 174, and **119**
> zero-project-axiom results rather than 124. There are exactly **5** bracket-free
> results at this revision: `RealizableLeaves.{t1RShape_witness,
> t1RShapeNS_witness, s1RShape_witness, witness_noSeizeWdrl}` and
> `ShapeBridge.inputs_M1`. G3 initially reported 169/119 and had to correct itself;
> E5's 173/124 was right. Both traps must be handled together: parse **across
> newlines** AND for **both output forms**.
>
> Decomposition of the 124, so the number can be checked rather than trusted:
> **102** builtins-only (`propext` / `Classical.choice` / `Quot.sound` /
> `Lean.ofReduceBool` / `Lean.trustCompiler`), **17** carrying `sorryAx` but no
> project axiom, and the **5** bracket-free. 102 + 17 + 5 = 124.
> **At H2 the first bucket is 100** (the two deleted `Witness1600` results were
> both in it): 100 + 17 + 5 = 122.

> **Parsing trap, recorded because it cost this audit time.** `#print axioms` output
> **wraps across log lines**. A line-oriented `grep 'depends on axioms' | grep -c
> sorryAx` returns **17**, not 37 — it only sees names whose axiom list happens to
> fit on the first line. Parse for `'NAME' depends on axioms: [` … `]` across
> newlines. C4's published "27 with `sorryAx`" was produced by the line-oriented
> method and is **corrected here**.

Legend: **(i)** Lean-standard `propext`/`Classical.choice`/`Quot.sound`;
**(ii)** `native_decide` = `Lean.ofReduceBool` + `Lean.trustCompiler`;
**(iii)** `sorryAx` = blaster's `admit`; **(iv)** project axioms, counted.

### 3.1 The number a reviewer needs

There are now **three** strongest-available claims and they are not comparable, so
all three are quoted:

**(a) `Composition.containment_on_contained_class` — 26 project axioms.** Over the
`ContainedTx` accounting class. Uses **no UPLC result**; its acceptance hypotheses
are provably unused.

**(b) `RealizableLeaves.containment_on_realizable_class` — 28 project axioms, no
leaf hypothesis.** Over `T1RShapeNS`, a non-empty shape class. Uses the production
`programmableLogicGlobal` bytecode for `p1`, **consuming the acceptance
hypothesis**. The 28 are the same 26 **plus exactly two**:

* `WSC.LR_BUDGET_global` — the ledger↔meter bridge at `K_global = 4400`, whose
  non-vacuity hypothesis is *discharged*, not assumed
  (`NonVacuity.globalNonVacuous_at_4400`, `native_decide` on the real CEK);
* `WSC.TS3` — reached through `Composition.coveringIn_of_coveringRaw`, the
  raw↔ground-truth reconciliation of the directory exemption predicate.

**(c) `RealizableLeaves.containment_on_seize_class` — 28 project axioms, no leaf
hypothesis.** Over `S1RShape`. Uses the production `programmableSeize` bytecode for
`p2`, **consuming the acceptance hypothesis**. Its 28 are the same 26 plus
`WSC.LR_BUDGET_seize` and `WSC.nodeStepsSeize`. `TS3` disappears because `p1` no
longer needs the raw↔ground-truth covering reconciliation.

Measured set differences (from the parsed log, not from any report):

```
axioms(containment_on_realizable_class) Δ axioms(containment_on_realizable_class_of_p2)  =  ∅
axioms(containment_on_realizable_class) ∖ axioms(containment_on_contained_class)
      =  {WSC.LR_BUDGET_global, WSC.TS3}                       (∅ in the other direction)
axioms(containment_on_seize_class)      ∖ axioms(containment_on_contained_class)
      =  {WSC.LR_BUDGET_seize, WSC.nodeStepsSeize}             (∅ in the other direction)
axioms(containment_on_seize_class)      Δ axioms(containment_on_realizable_class)
      =  {LR_BUDGET_seize, nodeStepsSeize}  vs  {LR_BUDGET_global, TS3}
```

**Two facts a reviewer should take from this.** First, the two-axiom delta is the
price of making the bytecode load-bearing, and it is the single most informative
number in this audit: result (a) is cheaper in axioms and says nothing about the
validators; results (b) and (c) each cost two more and each say something about one
validator. Second — new in stage 11 — **closing `p2` cost nothing at all**: the
axiom set of the hypothesis-free (b) is *set-equal* to that of the C4 result that
assumed `p2`. The obligation was removed by a class restriction, not bought with a
new assumption. That is the honest reading, and §3.4 gives the honest price.

The 26 shared, by home file:

`WSC/Honest.lean` (16):
```
Deployed  OnChain
LR_CTX  NONNEG  LR_BUDGET_base
LR_MINT_RUNS_POLICY  LR_SPEND_RUNS_VALIDATOR  LR_WDRL_RUNS_VALIDATOR
NodeAcceptsBase  NodeAcceptsGlobal  NodeAcceptsMinting  NodeAcceptsSeize
nodeStepsBase  nodeStepsGlobal  nodeStepsMinting
mlhPolicyId
```

`WSC/Composition.lean` (10):
```
LedgerStep  Genesis
lr_utxo_semantics  lr_inputs_in_ledger  lr_registration_source
LR_BALANCE_SLOT  NONNEG_L  DIRWF_L
ts_genesis  ts_minting_identity_L
```

**Read 26/28 as a floor, not a ceiling.** The library declares 51; the 21 that no
top-level theorem reaches — `LR1`–`LR7`, `LR_BUDGET_minting`, `DIRWF`, `TS1`–`TS5`
(less `TS3`), `TS_MINTING_IDENTITY`, `LR_REDEEMER_COVERAGE`, and the two `*_faithful`
axioms — are what a *fuller* bytecode discharge of the leaves would add.

### 3.2 Per-theorem table (project-axiom count; flags)

| theorem | (i) | (ii) | (iii) | (iv) |
|---|---|---|---|---|
| **`RealizableLeaves.containment_on_realizable_class`** | ✓ | ✓ | ✓ | **28** (§3.1b), **no leaf hypothesis** |
| **`RealizableLeaves.no_tokens_outside_mini_ledger_on_realizable_class`** | ✓ | ✓ | ✓ | **28** (identical set) |
| **`RealizableLeaves.containment_on_seize_class`** | ✓ | ✓ | ✓ | **28** (§3.1c), **no leaf hypothesis** |
| **`RealizableLeaves.no_tokens_outside_mini_ledger_on_seize_class`** | ✓ | ✓ | ✓ | **28** (identical set) |
| `RealizableLeaves.containment_on_realizable_class_of_p2` (C4, retained) | ✓ | ✓ | ✓ | 28 + one open `p2` |
| **`RealizableLeaves.realizableLeavesNS`** | ✓ | ✓ | ✓ | **12** — `Deployed`, `LR_BUDGET_global`, `LR_CTX`, `NodeAccepts{Global,Minting,Seize}`, `OnChain`, `TS3`, `nodeSteps{Base,Global,Minting}`, `LedgerStep` |
| **`RealizableLeaves.realizableLeavesS1R`** | ✓ | ✓ | ✓ | **13** — the above with `{LR_BUDGET_seize, NONNEG, nodeStepsSeize}` for `{LR_BUDGET_global, TS3}` |
| **`RealizableLeaves.p2_of_noSeizeWdrl`** (closed leaf, transfer side) | ✓ | **—** | **—** | **7** — and **no `sorryAx`, no `native_decide`**: no bytecode result is reachable from it |
| **`RealizableLeaves.p1_of_noGlobalWdrl`** (closed leaf, seize side) | ✓ | **—** | **—** | **7** — likewise |
| **`RealizableLeaves.p2_on_S1RShape`** (bytecode leaf, seize side) | ✓ | ✓ | ✓ | **10** — `Deployed`, `LR_BUDGET_seize`, `LR_CTX`, `NONNEG`, `NodeAcceptsSeize`, `OnChain`, `nodeSteps{Base,Global,Minting,Seize}` |
| **`RealizableLeaves.shapedGlobalContainment_T1RNS`** (bytecode leaf, transfer side) | ✓ | ✓ | ✓ | **7** — `LR_BUDGET_global`, `LR_CTX`, `NodeAcceptsGlobal`, `OnChain`, `nodeSteps{Base,Global,Minting}` |
| `RealizableLeaves.p4_on_T1RShape` / `nopre_on_T1RShape` | ✓ | — | **—** | 6 each (field signature only; **no bytecode**) |
| `RealizableLeaves.p4_on_S1RShape` / `nopre_on_S1RShape` | ✓ | — | **—** | 7 each (likewise) |
| **`RealizableLeaves.exec_T1R`, `exec_S1R`** | ✓ | — | **—** | **0 — kernel-checked `rfl`** |
| **`RealizableLeaves.bridge_T1R`, `bridge_S1R`** | ✓ | — | ✓ | **0** |
| **`RealizableLeaves.realizable_inhabitant`, `_NS`, `_S1R`** | ✓ | ✓ | **—** | **0 — the classes are non-empty and node-realizable, on no assumption** |
| **`RealizableLeaves.inhabitant_accepted_by_bytecode`** | ✓ | ✓ | **—** | **0** |
| `RealizableLeaves.witness_noSeizeWdrl`, `t1RShapeNS_witness`, `s1RShape_witness` | ✓ | — | — | **"does not depend on any axioms"** |
| **`Coverage.not_covers_at_T1R_size`, `_size'`, `_with_three_reference_inputs`** | ✓ | ✓ | **—** | **0 — no project axiom, no `sorryAx`** |
| **`Coverage.missed_transactions_are_realizable_and_accepted`, `_cost_exactly_2343_steps`** | ✓ | ✓ | **—** | **0** |
| `Coverage.family_invariants`, `ctxOk_in_family`, `wdrl_range_char`, `wdrlPair_char`, `unshaped_covers` | ✓ | — | — | **0** |
| `Coverage.skeletons_at_{T1R,M1R,minimal_transfer}_size` | — | ✓ | — | **0** |
| `Coverage.p3_lives_over_the_wdrlPair_class` (**REPLACES** `p3_lives_over_a_covering_class`, which is false at 2306678) | ✓ | — | ✓ | 0 (inherits P3's blaster `admit` — expected, and stated in the module) |
| `Composition.containment_on_contained_class` / `no_escape_on_contained_class` / `top_claim` | ✓ | ✓ | ✓ | **26** |
| `Composition.containedLeaves` | ✓ | **—** | **—** | **11**. **No `sorryAx`, no `native_decide`, no `blaster` verdict** — exactly how you can tell no bytecode result is used |
| `Composition.preservation` | ✓ | ✓ | ✓ | 22 |
| `P1R_T1/T2/T6/T7`, `P5R_shaped_indexed/_exists`, `P6R_*`, `P4*_R*`, `P2a_R_*`, `P2b_R_containment` | ✓ | — | ✓ | **0** |
| `P5R_shaped_groundtruth` | ✓ | — | ✓ | 3 — `Deployed`, `OnChain`, `TS3` |
| the 12 `*_class_coverage` and 12 `*_realizable` theorems | ✓ | ✓/— | **—** | **0** |
| `ShapeRealizability.t1_class_is_empty` | ✓ | — | **—** | **5** |
| `NonVacuity.*`, all concrete CEK witnesses (`K_T1R_is_2343`, `K_is_784`, …) | ✓ | ✓ | **—** | **0** |

### 3.3 Four properties of the list a reviewer should notice

1. **Every top-level theorem carries `sorryAx`.** All of them reach `p3_lifted`,
   which reaches the blaster-closed run-form P3; the shaped ones additionally reach
   `P1R_T1`/`bridge_T1R` or `P2b_R_containment`/`bridge_S1R`. The kernel did **not**
   check them; their status is "checked modulo a `✅ Valid` Z3 verdict recorded in the
   build log". The sentence "the top theorem is `sorry`-free" is **false as stated**.
2. **A P1 result and now a P2 result both appear in top-level dependency graphs.**
   In `containment_on_contained_class` no P1/P2/P4/P5/P6 result appears anywhere; in
   `containment_on_realizable_class`, `P1R_T1` and `bridge_T1R` are reached; in
   `containment_on_seize_class`, `P2b_R_containment` and `bridge_S1R` are. That is
   why those two carry `sorryAx` **through a shaped leaf** and why
   `NodeAcceptsGlobal` / `NodeAcceptsSeize` are not merely mentioned in a field type
   but consumed.
3. **Three of seven published budget instantiations are now exercised** —
   `LR_BUDGET_base` at 600 (`p3_lifted`), `LR_BUDGET_global` at 4400
   (`shapedGlobalContainment_T1R`), and — **new in stage 11** — `LR_BUDGET_seize` at
   3800 (`p2_on_S1RShape`). `LR_BUDGET_minting` is still applied by nothing (§8 F15).
4. **Lean's `unused variable` linter is still the honest instrument it was in A3.**
   Five warnings, all at `Composition.lean:2442-2446` — A2's inline `LeafSet` — and
   **none** in `RealizableLeaves.lean`, `RealizableLeavesS1R.lean` or `Coverage.lean`,
   because the bytecode leaves really do use their acceptance hypotheses and the
   shape leaves bind theirs as `_` deliberately (§5.4).

### 3.4 THE RATIO — the honest measure, and why "N = 0" must never be quoted alone

C4 reported an **N = 1** obligation gap and asked whether closing it would make the
bytecode do more work. **It does not, and the artifact says so itself.** Verified
here by reading the proof terms and by the axiom flags in §3.2, not from any report:

| composed result | class | `p1` | `p2` | `p4` | `nopre` | leaf hypotheses |
|---|---|---|---|---|---|---|
| `containment_on_realizable_class` | `T1RShapeNS` (transfer) | **BYTECODE** — `WSC.P1R_T1`, `programmableLogicGlobal` @ 4400, acceptance hyp. **used** | SHAPE + ledger rule | SHAPE | SHAPE | **0** |
| `containment_on_seize_class` | `S1RShape` (seize) | SHAPE + ledger rule | **BYTECODE** — `WSC.P2b_R_containment`, `programmableSeize` @ 3800, acceptance hyp. **used** | SHAPE | SHAPE | **0** |

**One of four leaves is the bytecode on each side; three of four are the shape.**

The mechanism on the shape side is a real ledger argument, not hand-waving, and it is
the only genuinely new proof technique in stage 11:
`NoSeizeWdrl hp ctx := credentialInWithdrawals hp.seizeLogicCred …txInfoWdrl = false`
makes the `p2` leaf's *hypotheses contradictory* via `validScriptInfo`'s
`RewardingScript` clause (`CardanoLedgerApi/V3/Contexts.lean:1014`, transcribing
Conway rewarding `scriptsNeeded`, `Alonzo/UTxO.hs:375-384`): a rewarding script runs
only for a credential the transaction actually withdraws at. `WSC.NodeAcceptsSeize`
is bound as `_hacc`, and `p2_of_noSeizeWdrl` carries **no `sorryAx` and no
`native_decide`** — machine-checkable evidence that no seize-validator result is
reachable from it. The seize side is the mirror image with `NoGlobalWdrl`.

**What this means, stated so it cannot be softened.** Removing the last leaf
hypothesis did **not** make the composition say more about the validators. It made
explicit that in a pure-transfer class three of the four obligations are about things
the class does not do, and that on the seize side the load-bearing leaf is the other
one. **Quote the ratio, never just "N = 0".** Both module docstrings say this, and so
does `WSC.lean`'s stanza — checked.

**Two further restrictions, recorded because E1 flagged them and this audit confirms
them.** (i) The `T1R` class is now strictly *smaller*: `containment_on_realizable_class`
excludes transfers whose second script withdrawal *is* the seize script. That
exclusion is the entire content of "discharged by the shape" — a class restriction,
not a proof about `programmableSeize`. (ii) `S1RShape` carries conjuncts
`T1RShapeNS` does not: `SeizeWithinBudget`, which is `Composition.WithinBudget`'s
deliberately-absent seize clause and is about the **opaque** `WSC.nodeStepsSeize`, so
unlike every other conjunct it **cannot be checked at the witness**; and
`mlCS = key` / `mCS = key`, which restrict to the **seized** policy because
`P2b_R_containment` is about that policy alone while `LeafSet.p2` demands containment
for *every* policy. Without those, on seize acceptance alone `p2` is **false** for a
positive mint of a *non-seized* policy sent off-base — nothing the seize validator
checks constrains another policy's mint; that is `p4`'s job. The S1R module states
all of this at §2, §3.3 and §5 rather than asserting inhabitation of the full class.

---

## 4. VACUITY RE-VERIFICATION

The highest-risk failure mode in the library, and the reason is on the record: task
V3 stated P6 at SHAPE G6 budget **2500**, got `✅ Valid`, and only the mandatory probe
revealed the class was accept-**UNSAT** — the theorem was empty. Preserved as
`WSC/Shaped/Probe/G6Vacuous2500.lean`.

### 4.1 The pairing census, run mechanically over the whole built set

For every module in the built set, every prep/run term appearing in a theorem's
hypothesis was collected by identifier extraction and matched against every term
appearing in a `*vacuity*`/`*vacuous*` stanza. Result: **20 prep/run terms carry
accept-hypothesis theorems, and every one of the 20 has at least one probe at that
same term.** Unchanged by stage 11 — and that is the correct outcome, because:

* **E1 added no accept-hypothesis theorem over a prep term.** `bridge_S1R` is an iff
  between two executions and `exec_S1R` an equality (both over
  `appliedSeizeRShaped3800`, which already carries `P2_R_vacuity_probe`);
  `p2_on_S1RShape` hypothesises `WSC.NodeAcceptsSeize`, an abstract axiom, not a prep
  term. The correct vacuity question for the `RealizableLeaves*` modules is **class
  inhabitation**, and §4c answers it for both classes.
* **E4 added no accept-hypothesis theorem at all.** `WSC/Coverage.lean`'s acceptance
  results are *positive witnesses* (`Runs.globalRun 4400` accepts three named
  contexts), which need no probe — a probe certifies that an accept class is
  non-empty, and a witness *is* that certificate.

Five terms appear with theorems but no probe; each was re-inspected and **none is an
accept-hypothesis theorem**: `appliedGlobalShapedIdx1600`,
`appliedGlobalShapedNIdx1600` (bridges — equalities/iffs), `appliedMinting800` (a
positive witness), `appliedMinting1300`, `appliedSeize` (never used in a theorem).

**Re-run at G3 (`f4486ca`), mechanically, from the 162 verdict sites rather than
from the source.** For each verdict the enclosing declaration and every `applied*`
identifier in its statement were extracted, then grouped by term:

* **35 applied terms carry at least one verdict.** **31 of the 35 have a vacuity
  probe at that same term**, and 24 of those also carry a tightness stanza.
* **The 4 without one are exactly the expected 4, and none is a safety property.**
  Two are the **unshaped production terms** `appliedGlobal1600` and
  `appliedMinting900`, whose *symbolic* probes are documented **OPEN** — no verdict
  in 87 minutes (`P5_NonMember.lean:548`, `Honest.lean:1294`) — and whose
  non-vacuity is therefore discharged **concretely** instead
  (`ShapeBridge.prop_accepts_1600`, `G1NonVacuity.globalNonVacuous_at_1600`, and the
  deliberate `minting600_is_vacuous` calibration at 600). Two are
  `appliedGlobalShapedIdx1600` / `appliedGlobalShapedNIdx1600`, which carry only the
  `bridge_GIdx` / `bridge_GNIdx` prop↔prop biconditionals — see **F22**.
* **SHAPE L2R, new at G1, is in the "has a probe" set**: `P4_local_RIdx_vacuity_probe`
  and `P4_local_RIdx_tightness` are both stated over `appliedMintLocalRShapedIdx2500`
  — **the L2R prep term, not L1R's** — and both report `✅ Expected Falsified`.
  That is the check the house rule exists for, and G1 passed it.

### 4.2 The re-cut groups

**Every one of the now-13 re-cut shapes has a vacuity probe stated at ITS OWN prep
term AND ITS OWN shape builder**, verified by extracting the `applied*` and `*Ctx`
identifiers from each theorem and each probe and comparing them mechanically rather
than by reading docstrings. All 13 rows (T1R, T2R, T6R, T7R, G1R, G6R, M1R, M2R, L1R,
**L2R**, DT1R, DS1R, S1R) report **Falsified** in this rebuild. **A probe at the OLD
term would have certified nothing about the new one.**

> **L2R is where that discipline paid, and the payoff is worth stating.** At SHAPE
> L2R the *direct* no-escape goal is `⚠️ Undetermined` at a 300 s cap
> (`WSC/Shaped/Probe/L2RProbe.lean`, module wall 303 s). An `Undetermined` looks
> exactly like a hard problem and exactly like an empty class. **It was the vacuity
> probe coming back `Falsified` that separated the two** — accepting shape-L2R
> contexts do exist within 2500 CEK steps, so the Undetermined is a solver limit.
> Without the probe, G1 could not honestly have distinguished this case from the
> SHAPE G6 @ 2500 disaster that §4 opens with.

### 4b. THE RE-CUT ITSELF — unchanged from C4, re-verified

The Conway rule (`hasExactSetOfRedeemers`,
`eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs:239-262`, cardano-ledger
`cd8b7fab8`) computes `redeemersNeeded` from `scriptsNeeded` filtered to scripts that
are **provided** and **not native**, then requires the redeemer-map key set to equal
it exactly. C3's CLAB transcription is an **over-approximation** (it omits both
filters, because `TxInfo` records neither a script's language nor the witness set) —
this is finding **F18**, restated in §8 with stage 11's disposition.

The rule reproduces the real node on **13/13** goldens
(`#redeemers = #script-inputs + #mint-policies + #script-withdrawals` exactly, with
the purpose multiset matching), all 13 satisfy `redeemerCoverageAllPlutus`, all 9 accepting
goldens satisfy `redeemersExactAllPlutus`, and `all_old_witnesses_fail_c3_coverage` proves
`redeemerCoverageAllPlutus = false` at all 5 pre-C2 witnesses. **The flip is machine-checked
in both directions.**

### 4c. ARE THE CLASSES REALLY NON-EMPTY?

A3's §9 warned: *"Do not believe that instantiating the `Shape` parameter with a
shaped context class would fix that. It produces a true theorem about an EMPTY
class."* That warning was correct then and is why this section exists.

* `ShapeRealizability.t1_class_is_empty` proves the PRE-re-cut SHAPE T1 class empty
  **unconditionally**, and `t1_no_honest_step` proves no `Reachable.step` can fire.
  Both retained, as the picture of what failure looks like.
* **Transfer side.** `realizable_inhabitant_NS` proves, with **0 project axioms and
  no `sorryAx`**, that `P1RShapedWitness.ctxOk` is (i) a member of `T1RShapeNS
  witnessParams`, (ii) `validRewardingContext`, (iii) `redeemersExactAllPlutus`. The
  refinement did **not** empty the class: `witnessParams.seizeLogicCred = SEIZE ∉
  {GLOBAL, TLS}`, by `rfl`, no axioms (`witness_noSeizeWdrl`). The real compiled
  bytecode accepts it in **2,603** steps.
* **Seize side.** `s1RShape_witness` proves `P2RWitness.ctxAccept` satisfies
  `S1RCore ∧ NoGlobalWdrl` by `rfl` with **no axioms**; `realizable_inhabitant_S1R`
  adds `validRewardingContext` and Conway `redeemersExactAllPlutus`; and
  `inhabitant_accepted_by_bytecode` shows the restrictions do not empty the *accept*
  class — `isSuccessful (Runs.seizeRun 3800 ppCS ctxAccept)`, exact K = **2,301** at
  2306678 (was 3,004 pre-#112), pinned two-sided by `K_is_2301_and_2412`.
  **0 project axioms, no `sorryAx`.**

**The honest limit, stated precisely, and it now has one extra clause.** None of this
proves that a `Reachable` trace in the new classes can take a step, and it cannot:
`HonestTx` also requires `WSC.OnChain ctx`, an opaque axiom, so **no term in this
library can prove any concrete context on-chain**. That is true of every witness in
the campaign. **Additionally, the seize class's third conjunct `SeizeWithinBudget`
is about the opaque `WSC.nodeStepsSeize` and therefore cannot be checked at the
witness at all** — so `S1RShape`'s inhabitation is certified for two of its three
conjuncts, and the module says so instead of quietly claiming the third. "Not
provably empty, with the known obstruction removed" is weaker than "provably
inhabited on-chain", and this audit will not let the two be confused.

---

## 5. ANTI-TAUTOLOGY SPOT-CHECK

The question in each case: **is the postcondition a fact about the transaction, or is
it "the validator's own accumulator came out true"?** Re-read line by line at this
revision.

### 5.1 P1 containment at the realizable cut — `WSC.P1R_T1`

Postcondition, verbatim: `Model.outSum (.ScriptCredential plc) cs tn …txInfoOutputs ≥
Model.inSum … …txInfoInputs + Model.mintSigned cs tn …txInfoMint`.

* `Model.outSum` / `inSum` (`WSC/Model/Ground.lean:43-56`) are independent structural
  recursions over the context's own output/input lists, guarded by
  `WSC.payCred o == base` and summing CLAB's `valueOf`. **No validator function
  appears in the postcondition** — the validator appears only in the hypothesis.
* `plc` is not a free choice: it is the same variable the shape puts in the
  params-UTxO datum the validator reads.
* The escape route is REAL and proved so: `P1RShapedWitness.ctxEscape_quantities`
  gives `outSum = 3 < inSum = 5`, and `exec_rejects_escape` shows the real CEK
  **rejects** that context with 4,400 steps available (a genuine rejection, not budget
  exhaustion).
* The accepting witness is pinned two-sided: `K_T1R_is_2343` (was `K_T1R_is_2603` pre-#112).

**Verdict: ground truth. Not true by construction.**

### 5.2 P2b containment — `WSC.P2b_R_containment`

Postcondition is `P2.sumOutAtBase … ≥ P2.sumInAtBase … + WSC.mintOf …`, universally
quantified over `tn`, in independent recursions; nothing from the seize validator's
`valueDelta` / `ptokenPairsContain` machinery appears.

**Doubt, recorded, and it is now MORE important than it was, because this theorem is
load-bearing in a composed result for the first time.** This conjunct is
FALSE-in-general on the source model — obligation B1 has two machine-checked
counterexamples (`ptokenPairsContain` is unsound with duplicate token names or
unsorted maps) — and it closes here *because* SHAPE S1R gives every value exactly one
policy and one token name. **`containment_on_seize_class` therefore inherits that
shape-dependence directly.** The re-cut removed the realizability defect; it did NOT
remove the shape-dependence, and stage 11 did not either. This is the sharpest doubt
in the library and it is why §8 F2-coverage remains CRITICAL.

### 5.3 P4-Local no-escape — `WSC.P4_local_noEscape_R`

Postcondition `noEscape (.ScriptCredential plc) ownCS (localRCtx …outputs) = true`,
where `noEscape` scans the transaction's own output list. Both disjuncts are live
(distinct free variables). `L1RWitness.exec_rejects_escaping_output` is the
excluded-case witness through the real CEK over a redeemer-covered context.

**Verdict: ground truth. Not true by construction.**

### 5.4 The same check applied to the three `LeafSet` terms, and to the new leaves

| | `Composition.containedLeaves` (A2) | `realizableLeavesNS` (E1) | `realizableLeavesS1R` (E1) |
|---|---|---|---|
| class non-empty? | yes | **yes, certified** | **yes, 2 of 3 conjuncts certified** |
| bytecode used? | **no** | **yes — `p1`** | **yes — `p2`** |
| acceptance hyps consumed? | **none** (5 linter warnings) | **1 of 4** | **1 of 4** |
| project axioms | 11 | 12 | 13 |

**The new closed leaves are not tautologies, and the check is mechanical.**
`p2_of_noSeizeWdrl` and `p1_of_noGlobalWdrl` carry **no `sorryAx` and no
`native_decide`**, so no bytecode result is reachable from them; they are `exfalso`
arguments from CLAB's `validScriptInfo` and nothing else. The added conjuncts are
decidable facts about the **withdrawal map alone** — they say nothing about value
flow, outputs, or what any validator computes, so they cannot be used to prove
containment of anything. That is the difference between "discharged by the shape" and
"assumed".

### 5.5 The coverage refutation (new)

`Coverage.not_covers_of_invariant` is the whole argument and it is three lines: a
context that satisfies `Valid` and `Bound` but violates `ShapeInvariants` cannot be
in any family member, because `family_invariants` proves every member implies
`ShapeInvariants`. The risk is a **mis-transcribed** family — a `rangeXYZ` that is
not really the shape's range would make `¬ Covers` trivially true. E4 anticipated
this: `ctxOk_in_family` puts the certified inhabitant *inside* `rangeT1R`
(`[propext]`), so the family is demonstrably non-trivial. **This audit regards that
as the correct control and confirms it is present.**

The 12 `inv_*` proofs are `simp only [rangeXYZ, forall_exists_index]; intros;
subst_vars; exact ⟨…⟩` — computation at every leaf assignment, **no solver**. The
three counterexamples each change **exactly one** `Data`-skeleton feature of `ctxOk`
(signatory list length; reference-input list length; validity-interval constructor
tag), leaving every leaf scalar untouched. **None is repairable by adding a shape
parameter — two are list lengths and one is a constructor tag.**

---

## 6. PROVENANCE AND REPRODUCIBILITY

### 6.1 The bytecode chain — re-verified 4/4, independently

The four `.flat` files are byte-identical to the `cborHex` of the named unapplied
production scripts on wsc-poc `main` at commit
`f918ec6dcef4398952febe11e84fda089c064374` (the squash-merge of PR #110). At the
time of this audit the check was run against the export commit
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f` on the since-deleted PR branch; the
two commits carry the identical tree `d86b6aa15e89fa989018d08b4e4bcd08ecc66e5f`,
so the measurement below stands verbatim and is now quotable against a ref a
third party can fetch (`WSC/flats/PROVENANCE.md`, `WSC/REPRODUCE.md` §6.1).
Re-run by this audit against the wsc-poc worktree, not carried over:

```
1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3  programmableLogicBase
ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2  programmableLogicGlobal
289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1  programmableSeize
7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048  programmableTokenMinting
```

**4/4 MATCH on both sides.** This is the campaign's strongest single fact and it is
now verified at four separate audits.

### 6.2 D5 — the substrate pin, materially repaired

The `PlutusCore` (PlutusCoreBlaster, "PCB") dependency is required from an absolute
local path on an **unpushed** branch. C4 recorded this as *"nothing here is currently
reproducible off this machine"* — the highest operational risk in the repository.

Stage 11's E3 unit built the repair but **left it uncommitted in a scratch
directory** (§7.3). This audit verified it and landed it. What now exists:

| record | where |
|---|---|
| revision `9f9ca8c76baf3b5efdb63c33ca0091efa606b474`, branch, base, clean-tree status, and the shallow-clone caveat | `lakefile.lean` comment block |
| `"rev"` / `"inputRev"` on the PlutusCore entry | `lake-manifest.json` |
| the two branch commits as an **incremental git bundle** + `git am` patches | `WSC/substrate/` |
| apply/verify recipe and what it does *not* fix | `WSC/substrate/README.md` |
| full third-party build recipe | `WSC/REPRODUCE.md` |

**Verified here, not asserted.** The bundle was applied from a clone of the public
base into a scratch directory and byte-compared against the build machine's checkout:

```
bundle sha256   3d34a23d5e25ac09beddcdf6032ecb3d13c47d064239b09be8040842d1a82789  (39,068 bytes)
git bundle verify … → "is okay"; requires a04042c…; contains refs/heads/cip153-value-builtins
HEAD after apply : 9f9ca8c76baf3b5efdb63c33ca0091efa606b474   (canonical: identical)
tree after apply : e75862b26b5055e8cc36ea8cf393054e2417ca62   (canonical: identical)
diff -r -x .git -x .lake <canonical PCB> <reconstructed>  →  CLEAN
```

And the manifest claim was tested rather than believed: `lake build` **preserves** the
`"rev"` / `"inputRev"` keys on a `"type": "path"` entry across a full clean-room
rebuild (sha256 of `lake-manifest.json` unchanged after run 3).

**What is still open.** The branch is **not published**, so the bundle's custody is
the trust anchor; the `require` is still an absolute path, so building elsewhere is a
mandatory two-file manual edit; and lake does not *verify* the recorded rev for a path
dependency (`lake update` would drop it). **D5 is downgraded from HIGH/OPEN to
MEDIUM/PARTIALLY REPAIRED, not closed.** The one-line fix that retires it is to push
the branch and restore a git pin.

---

## 7. VERIFICATION OF THE STAGE-11 AND G-STAGE UNITS

This section is the point of task E5. Each unit's central claim is checked against
its artifact, and every gap is reported.

### 7.1 E1 — discharge `p2`, close F1 → **CLAIMS HOLD, with one labelling error**

| E1 claim | verdict |
|---|---|
| `p2` is NOT vacuously dischargeable over `T1RShape`; SHAPE T1R's second withdrawal `w1` is free and `Deployed` is opaque | **CONFIRMED** — `GlobalShapedP1.lean:225-226` and `RealizableLeaves.lean:140` read as described |
| `p2_of_noSeizeWdrl` discharges the leaf by the ledger rule, acceptance hypothesis bound as `_` | **CONFIRMED** — proof read line by line; `_hacc`; no `sorryAx`, no `native_decide` |
| axiom set of `containment_on_realizable_class` Δ `…_of_p2` = ∅ | **CONFIRMED by measurement** (§3.1) |
| 28 = 26 + `LR_BUDGET_global` + `TS3`; seize side 28 = 26 + `LR_BUDGET_seize` + `nodeStepsSeize` | **CONFIRMED by measurement** |
| `LR_BUDGET_seize` applied for the first time; F15 goes 2/7 → 3/7 | **CONFIRMED** |
| +1 job, +1 verdict (`bridge_S1R`), marker delta exactly +1 Valid | **CONFIRMED** — per-file table §1.2 |
| zero `unused variable` warnings in either module | **CONFIRMED** — all 5 are `Composition.lean:2442-2446` |
| **the ratio is 1 bytecode / 3 shape on each side** | **CONFIRMED, and this audit adopts it as the headline measure** (§3.4) |

**The one gap: a namespace labelling error in E1's report.** Its S1R axiom table
names `WSC.RealizableLeavesS1R.*`. That namespace **does not exist**: the module
`WSC/Props/Shaped/RealizableLeavesS1R.lean` declares everything in
`WSC.RealizableLeaves`. Every identifier in this audit uses the real name. The
theorems themselves are exactly as reported; only the report's prefix was wrong.
Cosmetic, but it would waste a reviewer's `#print axioms`.

**Answer to the question E5 was told to ask.** *Is the leaf load-bearing, or is it
discharged by the shape's narrowness?* **The latter, and E1 says so itself.** Counted
both ways: leaf hypotheses 1 → 0; bytecode-discharged leaves 1 → 1. The composition
does not say more about the validators than it did at C4. What changed is that the
gap is now visible as a *class restriction* rather than as an *assumption* — a real
improvement in honesty, not in strength.

### 7.2 E2 — F17 / F18 / F19 → **NOTHING WAS DELIVERED. New finding F20.**

`git log` shows no E2 commit. Its scratch workspace sits at `300f9e0` with a
**completely clean working tree**: no modified file, no untracked file, no log.
**The unit produced no artifact of any kind.**

Consequently **F17, F18 and F19 were all still open**, exactly as C4 left them, and
none of the four bar items E5 was asked to check for an "L2R" exists — there is no
L2R, and SHAPE L2 was never re-cut. This audit therefore did the cheapest of the
three itself, by measurement rather than by adding a theorem (§7.5).

### 7.3 E3 — reproducibility → **WORK IS CORRECT AND VERIFIED, BUT WAS NEVER LANDED**

E3 produced no report and made no commit. Its scratch workspace held modified
`lakefile.lean` + `lake-manifest.json` and an untracked `WSC/substrate/`.

**Did the reproduction rehearsal actually run end to end, and do its numbers match?**
This audit re-ran it from scratch. **Yes on both counts** — bundle size, sha256, HEAD,
tree and a full `diff -r` all match E3's documented values exactly (§6.2). The
shallow-clone caveat E3 documented is real and correctly diagnosed. **E3's technical
work is sound.**

**Two gaps, one of them serious:**

1. **It was not landed.** Left in a scratch directory, it repaired nothing — the
   canonical repository still had D5 wide open at `8163803`. E5 has landed it.
2. **Two dangling cross-references.** E3's new `lakefile.lean` comment block directs
   the reader to `WSC/REPRODUCE.md` ("Full third-party recipe") and
   `WSC/substrate/README.md` ("bundle verify/apply"). **Neither file existed.** A
   reproducibility fix whose own instructions point at missing files is not a fix.
   E5 authored both, from its own re-measurement.

Also recorded: E3's `lakefile.lean` block claims the base `a04042c` is `refs/heads/main`
of the **public** `input-output-hk/PlutusCoreBlaster`. This audit confirmed `a04042c`
is the base of the local branch and is reachable as `main` in the local clone, but
**could not verify the public remote from this environment**. Treat "it is on the
public remote" as E3's claim, not as measured here; `WSC/substrate/README.md` §3 tells
the reader to check it with one `git rev-parse`.

### 7.4 E4 — shape coverage → **CLAIMS HOLD; IT IS A LEAN ARTIFACT, NOT PROSE**

| E4 claim | verdict |
|---|---|
| coverage is *stated in Lean* and refuted, not argued in prose | **CONFIRMED** — `WSC/Coverage.lean`; `Covers`, `SizeBound`, **14** `range*` defs (T8R joined at N6), `not_covers_*` |
| the three refutations carry **no project axiom and no `sorryAx`** | **CONFIRMED by measurement** — `[propext, ofReduceBool, trustCompiler, Quot.sound]` |
| witnesses are ledger-valid + Conway-redeemer-exact, accepted at 4400, at exactly **2343** steps (2603 pre-#112) | **CONFIRMED** — theorems present and building, re-measured at N6 |
| the transcription control `ctxOk_in_family` exists | **CONFIRMED** (§5.5) |
| `WSC/Coverage.lean` adds **zero** solver verdicts and zero warnings | **CONFIRMED** — absent from the marker table; not among the 38 `warn.sorry` suppressors |
| `p3_lives_over_a_covering_class` inherits `sorryAx` from P3 | **CONFIRMED, and E4 stated it** |
| skeleton arithmetic | **RE-CHECKED**: 995,328 × 3.3 s ≈ 38 CPU-days; 9,269,489,664 × 3.3 s ≈ 970 CPU-years; 3.05×10¹⁴ × 3.3 s ≈ 3.2×10⁷ CPU-years. E4's figures are right. |

**No gap found between claim and artifact.** E4's own limits are accurate and this
audit adopts them: "coverage is false" ≠ "coverage is impossible" (the impossibility
argument is **arithmetic only** and is not a theorem); realizability of the
counterexamples is **necessary, not sufficient**; and `SizeBound`'s choice of five
dimensions is a modelling decision, which is exactly where an overclaim would hide.

One process note: E4 appended an `import` stanza to `WSC.lean`, which it did not own,
and said so. That is the right disposition — without it the module would be outside
`lake build WSC` and invisible to this audit.

### 7.5 F17, measured here rather than left open

C4 called F17 "the cheapest open item" and E2 did not do it. This audit **measured
the answer** in a scratch module (deliberately not committed — E5 owns documents, not
Lean sources):

```lean
theorem m2r_exec_accepts_at_900 :
    isSuccessful (appliedMintRShapedIdx900.exec M1RWitness.ppCS M1RWitness.mlh
      "OWNCS" "TOK" (-3) "OWNER" 100 5 "DEST" 60 2 "MINTLOGIC" 0 "MLRED" 40 "" 0 0 1 "" 0) :=
  M1RWitness.isHaltB_sound _ (by native_decide)
```

* **It builds, and the real compiled `programmableTokenMinting` bytecode ACCEPTS the
  SHAPE-M2R witness on `.exec`.**
* `#print axioms` → `[propext, Classical.choice, Lean.ofReduceBool,
  Lean.trustCompiler, Quot.sound]` — **0 project axioms, no `sorryAx`**, the same
  shape as M1R's `exec_accepts_at_900`.
* **Exact K = 784**, measured by search over `isHaltB` at
  `mintingPolicyInputs900 … M2RWitness.ctx` — **byte-identical to SHAPE M1R's
  `K_is_784`**, as the "the re-cut cost zero CEK steps" result predicts (the
  withdrawal index lives in the redeemer *payload*, not in the map's keys).

**F17 was therefore answered but not landed at E5.** Landing it is a two-theorem
paste into `WSC/Props/Shaped/P4ShapedRIdx.lean`'s `M2RWitness` namespace, after which
M2R meets 4/4 bars and STATUS §2's only "3/4" row disappears. The E5 audit left the
paste to whoever owns that file, with the measurement done. **G1 landed it — see
§7.6.1, where the landed theorems are compared against this measurement line by
line.**

---

### 7.6 VERIFICATION OF THE TWO G-STAGE UNITS — **EXISTENCE FIRST**

**Why this section is written the way it is.** F20 records that a stage-11 unit
reported nothing, delivered nothing, and *no instrument in the campaign could see
it*: verdict counts, the axiom census and the marker table all measure what EXISTS,
so a unit that adds nothing is indistinguishable from a unit that was never run. G3's
first action was therefore **not** to rebuild and **not** to re-census, but to ask, of
each of F17/F18/F19: *is there a commit, does the named path contain the named
declaration, and does that declaration say what the report says it says?*

**Both G-stage units delivered. Neither is an E2.** Recorded plainly, in the same
register the E2 finding is written in:

```
git log --format='%H %an %s' -3
f4486ca  Philip DiSarro  WSC F17 + F19: land M2R's accepting witness; re-cut SHAPE L2 to L2R
9e5d417  Philip DiSarro  WSC F18: redeemerCoverage is stronger than the ledger — rename, bound, audit every negative use
7039cdb  Philip DiSarro  WSC E3+E5: reproducibility (revision pin + verified substrate bundle) and the sealed reviewer documents
```

`9e5d417` touches 21 files, +818/−227. `f4486ca` touches 5 files, +970/−10, of which
two are new. Tree clean at both. **Neither commit is empty and neither is
documentation-only.**

#### 7.6.1 F17 — **LANDED. Claim matches artifact.**

| G1 claim | G3 verdict |
|---|---|
| `M2RWitness.exec_accepts_at_900` exists in `WSC/Props/Shaped/P4ShapedRIdx.lean` | **CONFIRMED**, `:174-181` |
| it runs the **shaped applied term the theorems above it quantify over** | **CONFIRMED** — it is `appliedMintRShapedIdx900.exec`; the five property theorems at `:48,66,84,100,120` use `appliedMintRShapedIdx900.prop`, the same prep (`MintingShapedRIdx.lean:173`) |
| `K_is_784` is pinned **TWO-SIDED** | **CONFIRMED**, `:190-194` — `isHaltB … 784 = true ∧ isHaltB … 783 = false`, both `native_decide` |
| K is measured at **the same inputs** as the acceptance | **CONFIRMED BY READING THE DEFINITIONS, not by trusting the report.** `K_is_784` measures `cekExecuteProgram programmableTokenMinting900.script (mintingPolicyInputs900 ppCS mlh ctx)`; `mintingPolicyInputs900 p m c = toTerm p :: toTerm m :: mintingInputs c` (`Prep/Minting900.lean:69-71`) and `mintRInputsIdx p m …leaves = toTerm p :: toTerm m :: mintingInputs (mintRCtxIdx …leaves)` (`MintingShapedRIdx.lean:158-171`). The 19 leaves passed to `exec_accepts_at_900` are **character-identical** to those building `ctx` at `:136-140`. The two theorems are about the same run. |
| this is M1R's house pattern, not a weaker one | **CONFIRMED** — `P4ShapedR.lean:278/288` has exactly this structure |
| `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, 0 project axioms | **CONFIRMED** — the census at §3 gained no `sorryAx` and no project-axiom occurrence from `P4ShapedRIdx.lean` |
| adds **zero** solver verdicts | **CONFIRMED** — `P4ShapedRIdx.lean` still contributes exactly 3 V + 2 F (§1.2) |

**SHAPE M2R now meets 4/4.** The E5 measurement reproduced exactly, including K.

#### 7.6.2 F19 — **CLOSED, and by a better route than the task assumed.**

The task said "re-cut SHAPE L2". G1 did that (`WSC/Shaped/MintingLocalShapedRIdx.lean`,
362 lines, SHAPE **L2R**) but could **not** close the headline the obvious way, and
said so instead of hiding it. G3 verifies both the artifact and the honesty.

| bar item | G3 verdict |
|---|---|
| **(a) theorem, `✅ Valid`** | **CONFIRMED, with the route stated.** `P4_local_noEscape_RIdx` (`P4LocalShapedR.lean:616`) is **not** solver-closed directly — the direct goal is `⚠️ Undetermined`. It is derived from `P4_local_RIdx_negative_control` (`:575`, `blaster (timeout: 300)`, **`✅ Valid` at `:597` in both G3 runs**) by `halt_not_error` (`:555`, `[propext]` alone). G3 read the derivation: it is a two-case `cases` on the postcondition with `absurd`, and it is sound because `isSuccessful = isHaltState` and `isUnsuccessful = isErrorState` are `True` on **disjoint** `State` constructors (`PlutusCore/UPLC/Utils.lean:24-36`). The negative control is therefore **strictly stronger** than the headline — `(¬post → ERRORS)` implies `(HALTS → post)`, and not conversely, since a budget-exhausted run is neither. **This is a legitimate strengthening, not a weakening.** |
| **(b) vacuity probe at its OWN term and shape** | **CONFIRMED** — `:687` `P4_local_RIdx_vacuity_probe` over `appliedMintLocalRShapedIdx2500`, `✅ Expected Falsified` at `:708`; plus `P4_local_RIdx_tightness` at `:654`, Falsified at `:677`. Both over the **L2R** prep, not L1R's (§4.1). |
| **(c) two-sided CEK witness** | **CONFIRMED** — `L2RWitness.exec_accepts_at_2500` (`:777`) and `K_is_1681` (`:800`), 1681 true / 1680 false. Equal to `L1RWitness.K_is_1681` and to the `mint-local-registered-by-ref` golden. |
| **(d) realizability theorem** | **CONFIRMED** — `L2RWitness.ctx_realizable` (`:763`) over the class-level `localRIdx_{wdrl,spend,mint}_covered` (`MintingLocalShapedRIdx.lean:302,314,325`). |
| SHAPE L2R strictly contains SHAPE L1R | **CONFIRMED** — `localRCtxIdx_at_one` (`:220`) is `rfl`, i.e. **definitional**, not a solver claim. |
| the loosened index is **live**, not decorative | **CONFIRMED, and this is the item that makes the rung mean something.** `L2RWitness.ctxIdx0` at `regIdx = 0` is ledger-valid and redeemer-covered (`:834`) and **REJECTED** by the real bytecode (`exec_rejects_regIdx0`, `:841`). Without this, "the index is symbolic" could have been true and empty. |

**One caution G3 adds, which G1's own header already carries.** `L2RWitness.ctx` is
`rfl`-equal to `L1RWitness.ctx` (`ctx_eq_L1R`, `:742`). So the *accepting* witness at
L2R is literally L1R's witness at index 1; what is genuinely new is the **symbolic
quantification** in the theorem and the **rejecting** witness at index 0. That is the
correct reading and the module states it.

**What G1 did NOT close, and said so in-source rather than staying silent** — this is
recorded here so it is not lost when the module header is skimmed:

* **C1 at SHAPE L2R (`L2R_C1`) is `⚠️ Undetermined`** at the 300 s cap and is **NOT
  asserted as a theorem**. C1 at the concrete-index SHAPE L1R (`P4a_local_R`) is
  unaffected and still `✅ Valid`.
* **The direct `L2R_noEscape` goal is `⚠️ Undetermined`** at the same cap.
* **The registration conjunct is not attempted at L2R.**
* `WSC/Shaped/Probe/L2RProbe.lean` is the exploratory record of all of the above and
  is **deliberately out of the build**, per the house convention for probe modules
  carrying Undetermined verdicts. G3 confirms it is not imported and that the built
  set carries **0 `⚠️`**.

#### 7.6.3 F18 — **RESOLVED as an explicit, typed downgrade — not as a narrowing.**

The honest summary, and it is the one G2 itself gives: **the predicate was NOT
narrowed, because it cannot be.** `TxInfo` (`CardanoLedgerApi/V3/Contexts.lean:401-430`)
carries no scripts and no script languages; the only script-shaped payload in the
whole V3 API is `V2.TxOut.txOutReferenceScript : Option ScriptHash`, and
`ScriptHash := ByteString`. `isNativeScript` is a predicate on a script **body**
(`cardano-ledger` `Core.hs:586-587`), so it cannot be evaluated at a hash. What is
missing is exactly **one bit per needed script**.

| G2 claim | G3 verdict |
|---|---|
| the rule was read at the cited ledger revision | **CONFIRMED** — `/home/gumbo/playground/cardano-ledger` @ `cd8b7fab8`, `Alonzo/Rules/Utxow.hs:239-262` |
| the `scriptsProvided` lookup is a **no-op**, the `isNativeScript` filter is the real gap | **PLAUSIBLE AND WELL-ARGUED** — `babbageMissingScripts` runs at `Babbage/Rules/Utxow.hs:344`, seven lines before `hasExactSetOfRedeemers` at `:351`. G3 did not re-derive the STS ordering independently and does not claim to have; the citation is precise enough for a reviewer to check. This **corrects** the earlier F18 wording, which listed both filters as gaps. |
| predicates renamed `…AllPlutus` at every use site | **CONFIRMED** — `redeemerCoverageAllPlutus` etc., 21 files, and the build is green, which is itself the check (an unapplied rename does not compile) |
| the two directions are **theorems**, not comments | **CONFIRMED** — `coveredByNonNative_of_coveredBy` / `redeemerCoverageModNative_of_allPlutus` (positive), `coveredByNonNative_strictly_weaker` / `noExtra_not_conservative` (negative), `Contexts.lean:1427-1500` |
| the downgrade is **in the TYPE**, not only in prose | **CONFIRMED, and this is the load-bearing check.** The six conditional emptiness theorems now take `RedeemerCoverageAt w` — `ShapeRealizability.lean:350,373,394,439,463,489` — with two visible suppliers, `RedeemerCoverageAt_of_allPlutus` (over-strong) and `RedeemerCoverageAt_of_true` (true rule + explicit `¬ isNative w`). A reader cannot consume the weaker result without seeing which one they picked. |
| 6 unaffected / 6 downgraded / 1 measurement re-read | **CONFIRMED** — the table is at `ShapeRealizability.lean` §2.3, `:561-566` and around |
| `g6_class_is_empty_nonNative` is the axiom-free true-rule form | **CONFIRMED BY MEASUREMENT** — `[propext, Classical.choice, Quot.sound, WSC.OnChain]` (1 project axiom) vs `g6_class_is_empty`'s `[…, WSC.LR_REDEEMER_COVERAGE, WSC.OnChain]` (2). This is the **+1** in §3's 173 → 174. |
| the axiom census was **not** renumbered | **CONFIRMED** — 51 `axiom` declarations, unchanged; `LR_REDEEMER_COVERAGE` deliberately keeps its name |
| adds **zero** solver verdicts | **CONFIRMED** (§1.3) |

**The discriminator G2 used is the right one and G3 endorses it.** The six survivors'
uncovered purpose is the **running** script, pinned by `Deployed` to a compiled Plutus
V3 validator, so `isNativeScript` is irrelevant to them. The six downgrades' uncovered
purpose is a **free `ByteString` parameter** of the shape (`w0`/`w1`) — nothing pins
it to a Plutus script, so **none of the six can be re-established outright**, only
conditioned. That is a real loss of strength and it is now visible in the types.

#### 7.6.4 What G2 flagged against itself, and G3 confirms

Recorded because self-reported limits are the campaign's best evidence of good faith:

1. **The six downgraded emptiness results cannot be repaired, only conditioned.**
   Repair means re-cutting each shape so its second withdrawal credential is pinned
   to a deployed WSC validator hash. That is a re-prep-and-reprove job.
2. **`noExtraRedeemersModNative` is stated with `List.all`/`List.any`**, not CLAB's
   `Recursor.all`/`Recursor.any`, so it is **not** proved defeq to
   `noExtraRedeemersAllPlutus`; its defect is witnessed by the standalone
   counterexample `noExtra_not_conservative` instead. Confirmed by reading the
   definitions.
3. **G2 edited files it did not own.** Unavoidable for a rename, and it said so.
   G1's files and G2's did not in fact collide.
4. **`all_recut_witnesses_redeemersExact` kept its name** while the definitions were
   renamed — deliberate, cosmetic, and stated.

---

## 8. FINDINGS, RANKED

### F2-coverage — CRITICAL, and now SHARPER: coverage is not merely absent, it is FALSE

No argument exists that the shapes exhaust the transactions the claim is about, and
stage 11 replaced that absence with a **machine-checked refutation**: at
`SizeBound 2 2 2 2 0` — SHAPE T1R's own size — three node-realizable transactions
that the production bytecode accepts in exactly 2,603 steps lie outside all twelve
re-cut shapes (`Coverage.not_covers_at_T1R_size`). Two differ from the certified
inhabitant by a **list length**, one by a **constructor tag**; none is repairable by
adding a shape parameter.

**One bookkeeping gap, recorded at G3 rather than left implicit.** `Coverage.lean`
names **twelve** shapes (`rangeG1R`, `rangeG6R`, `rangeT1R/T2R/T6R/T7R`,
`rangeM1R/M2R`, `rangeL1R`, `rangeDT1R`, `rangeDS1R`, `rangeS1R`) and was **not**
extended with a `rangeL2R` disjunct when G1 added SHAPE L2R. The refutation is
therefore literally about those twelve. **This weakens nothing** — it is a *negative*
result, so a thirteenth disjunct could only make it harder to hold, never easier —
but `not_covers_at_T1R_size` does not mention L2R and must not be quoted as if it
did. Adding the disjunct is a small, purely mechanical job for whoever next touches
that file.

The arithmetic says the gap cannot be closed by enumeration: the smallest bound
admitting a real transfer (1 input, **2** reference inputs — the global validator
cannot run without its params reference input plus the directory node its redeemer
indexes — 1 output) already contains ≈9.27×10⁹ `Data` skeletons ≈ **971 CPU-years**
for one property at the measured 3.3 s/shape. **This is now the binding constraint on
the entire deliverable**, and `WSC/COVERAGE.md` recommends against a coverage
programme on exactly these numbers.

### F1 — CRITICAL → **NARROWED TO A RATIO, NOT CLOSED**

C4's N = 1 obligation gap is gone; two composed results now have complete `LeafSet`s.
But **one of four leaves is the bytecode on each side and three are the shape**
(§3.4), so the composition does not say more about the validators than it did. For
the general class nothing is proved. **The correct citation is the ratio; "N = 0" on
its own is misleading and this audit treats quoting it alone as an overclaim.**

### D6 — was HIGH, OPEN → **CLOSED / FIXED UPSTREAM** (task N5; re-tested at N6)

Blaster emitted a kernel-ill-typed `Blaster.dite'` whenever a CIP-153 `Value`
builtin result stayed symbolic. `dite'` is well typed only when its branch binders
are syntactically `c` / `¬c`, but the condition and the branch lambdas were
optimized INDEPENDENTLY, so any normalisation that rewrote `¬c` but not `c` emitted
a term the kernel rejects. Two such rewrites fire on #112 bytecode: `¬(a ∧ b) ⇝ ¬a ∨ ¬b`
and `¬(true = x) ⇝ false = x`.

**Fix:** `optimizeDITE` now rebuilds both binder types from the FINAL condition —
`Blaster/Optimize/Rewriting/OptimizeITE.lean`, Blaster branch
`wsc-d6-dite-branch-retype` @ **`4d320dd`** (= public `59db213` + that one commit).
Branches that actually *use* their proof binder are untouched, so the change can
only repair a term the kernel would have rejected.

**RE-TESTED AT N6, NOT TAKEN ON TRUST.** The two reproductions now build:

| module | before | at `4d320dd` |
|---|---|---|
| `WSC/Shaped/Probe/T3PrepFAILS.lean` (`¬(true = b)` rewrite) | kernel error | **exit 0, 0 errors, 2.4 s** |
| `WSC/Shaped/Probe/T4PrepFAILS.lean` (De Morgan rewrite) | kernel error | **exit 0, 0 errors, 9.4 s** |

Both files are **relabelled as REGRESSION TESTS** (their filenames are now
historical and say so in their headers). D6's fix also unblocked N1's defect **D8**
— `WSC/Prep/Global1600` went from an 8 m 9 s kernel failure to building — which is
why P1/P5/P6 are statable at all at 2306678.

**Verdict-neutrality control** (it is shared substrate, so the fix had to be shown
harmless): the eight `WSC/Props/Shaped/P4*` modules give **42 ✅ Valid + 23 ✅ Expected
Falsified** with the patched Blaster and the **identical 42 + 23** with canonical
`59db213`.

#### The consequential claim D6 supported is WITHDRAWN, and its replacement is weaker than "fixed" sounds

D6 was the sole evidence for the campaign's standing limitation that **P1's
containment dispatch Paths B and C, and input-side aggregation, are "unreachable at
UPLC at any shape"**, i.e. ARCHITECTURE Tier 3.1's "1 of 3 paths at UPLC". Task N6
re-checked that rather than restating it:

* **Reachable — measured.** `T3_vacuity_probe`, stated at SHAPE T3's OWN prep term
  and OWN shape, returns **`✅ Expected Falsified` in ≈ 4.6 s**: Z3 exhibits a model
  in which the post-#112 bytecode ACCEPTS at a shape that takes Path B/C. So the
  residual is not merely kernel-clean, its accept class is non-empty.
* **Still not PROVED, for a different reason.** SHAPES T3/T4/T5 are PRE-RE-CUT and
  are provably unbuildable on a real node (audit **F2**): T3 has 1 script input +
  0 mint policies + 2 script withdrawals, so Conway's `hasExactSetOfRedeemers`
  demands 3 redeemer entries and T3 supplies 1. A P1 theorem there would live over
  an empty class of node-realizable transactions.

**So the honest status of Paths B/C was: no longer blocked by the substrate; blocked
only by the absence of a re-cut.** — **CLOSED at task H2 (2026-07-28).** The re-cut
was done: SHAPES **T3R** and **T4R** (`WSC/Shaped/GlobalShapedP1BC.lean`), preps at
budget 4400 (`GlobalShapedP1BCPrep.lean`), and P1 proved over both to the full
four-point bar (`WSC/Props/Shaped/P1ShapedBC.lean`). See the entry **H2** below for
exactly which of the three dispatch paths is now PROVED, which is MEASURED, and
which cannot be isolated by any accept/reject test at all.

### H2 (2026-07-28) — the containment dispatch, after the re-cut

> ⚠ **NAME COLLISION, disambiguated once here.** "H2" was ALSO the label of the
> PRE-#112 dead-file cleanup (§12, and the `pre-#112 (H2/G3)` column of the top
> banner). That stage is **2026-07-2x, pre-#112**; THIS one is **2026-07-28,
> post-#112**, and follows task **H1** (SHAPE T8R, finding F23). Every reference
> to this task in the tree carries the date.

ARCHITECTURE Tier 3.1 asks that each of `poutputsContainExpectedValueAtCred`'s
three dispatch paths independently imply the aggregate bound. Status, stated so
it cannot be over-read:

| path | what it is | status at UPLC, over a NODE-REALIZABLE class |
|---|---|---|
| **A** — single-asset accumulate-scan (`:567-593`) | taken iff the expected value is one currency symbol with one token name | **PROVED** since C1: `P1R_T1`/`P1R_T2`/`P1R_T6`/`P1R_T7`/`P1R_T8` over SHAPES T1R/T2R/T6R/T7R/T8R |
| **B** — wholesale `Data` equality (`:628-644`) | at the first mini-ledger output, `equalsData` of its non-ada map against the expected map | **REACHED, NOT ISOLABLE BY SEMANTICS.** On ledger-valid contexts with node-representable quantities `B ⟹ C`, so no accept/reject test can distinguish them — B is a pure performance fast path. (The one known separator is a `punionValue` overflow inside `accumulateOutputsAtCred`, which CLAB's `validTxOutValue` permits and a node's 64-bit CDDL bound does not; recorded in `P1ShapedBC.lean`'s header, not exploited.) Its CONDITION is evaluated in ground-truth vocabulary (`T3R_pathB_condition`) and its EXECUTION separated by cost: `K_T3R_B_is_1936` vs `K_T3R_C_is_2228`, two-sided, over two contexts differing in one integer leaf by one |
| **C** — CIP-153 builtin `pvalueContains` (`:615-618`) | reached when B's equality fails, or when no mini-ledger output is found | **PROVED EXECUTED AND TRUE** at `P1BCShapedWitness.ctxC` (`T3R_pathC_is_taken`), by a two-witness argument that assumes nothing about the validator beyond "the expected value does not read `txInfoOutputs`" and `pvalueContains`'s own specification |

Plus: `T3R_not_path_A` PROVES the SHAPE-T3R runs are on the B/C arm — two
rejections, one short on `tn0` with `tn1` whole and its mirror, which no
single-asset scan can both produce. And the INPUT side of the same D6 claim is
closed by SHAPE T4R: `P1BC_T4R` is P1 with `inAtBase` produced by
`pvalueFromCred`'s PHASE 3 builtin accumulation (`punValueData` / `punionValue` /
`pinsertCoin` / `pvalueData`) rather than PHASE 2's positional ada-drop.

**How to quote this: "2 of 3 dispatch paths verified at UPLC over realizable
classes with certified witnesses (A and C); the third (B) is reached and measured
but is semantically subsumed by C, so no theorem can separate it."** Anything
stronger is an overclaim.

### F8 — MEDIUM, OPEN, and now BINDING ON BOTH COMPOSED RESULTS

`PropExecFaithful` (`X.prop = X.exec`) is still unproved and deliberately not
axiomatized. Theorems are on `.prop`, witnesses and all measured K on `.exec`. It
binds all 12 re-cut groups and — since stage 11 — **both** composed results, through
`bridge_T1R` and `bridge_S1R`.

### F4 — MEDIUM, OPEN BY NATURE. "`sorry`-free" is false

**100** theorem-position results are closed by `blaster`'s `admit`; every top-level
theorem inherits `sorryAx`. And the build log's `sorry` warning count is **not** a
census — 38 modules suppress it.

### D5 — was HIGH → **MEDIUM, PARTIALLY REPAIRED** (§6.2)

Revision recorded in three places; offline bundle present and independently verified
to reconstruct the exact tree. Still: branch unpublished, path absolute, rev not
enforced by lake.

### F20 — MEDIUM, **PROCESS FIX ADOPTED**; the underlying blind spot is permanent

E2 produced no artifact at all (§7.2). E3 produced correct work and left it in a
scratch directory with two dangling cross-references (§7.3). **Process finding, but a
real one:** at `8163803`, the canonical repository's most damning practical caveat was
still fully open despite a unit having been assigned to it and having *solved* it.
E5 landed E3's work and wrote the two missing documents. **A campaign that measures
its own claims must also check that its units' claims reached the repository** — the
verdict counts, the axiom census and the marker table would all have looked perfectly
healthy while D5 stayed open, because none of them can see work that was never
committed.

**Disposition at G3.** The blind spot cannot be closed by a better instrument,
because every instrument the campaign owns measures what EXISTS. It is closed by a
**procedure**, which G3 executed and which is now the standing rule for any unit that
gates another's work:

1. **Existence before measurement.** Before rebuilding anything, resolve each
   assigned finding to (a) a commit, (b) a path, (c) a declaration name in that path,
   (d) a reading of that declaration. §7.6 is the worked example.
2. **Reconcile deltas to source LINES, not to totals.** §1.3 names
   `P4LocalShapedR.lean:597/677/708` rather than saying "+3". A totals check cannot
   distinguish "a unit added three verdicts" from "a unit added none and another
   removed three".
3. **Read the definitions the claim depends on.** §7.6.1 does not accept "the K is
   measured at the same term"; it unfolds `mintingPolicyInputs900` and
   `mintRInputsIdx` and checks they agree.

At G3 both G-stage units passed step 1 outright. **This is recorded as evidence that
the procedure ran and found work present, not as evidence that the procedure is
unnecessary.**

### F17 — was MEDIUM → **CLOSED. LANDED by G1 at `f4486ca`** (§7.5 measured it, §7.6.1 verified the landing)

SHAPE M2R's witness **is** accepted by the real bytecode, at exactly **K = 784**
pinned two-sided, with 0 project axioms and no `sorryAx`. The two theorems
`M2RWitness.exec_accepts_at_900` and `M2RWitness.K_is_784` are in
`WSC/Props/Shaped/P4ShapedRIdx.lean:174-194`. G3 verified they run the shaped applied
term the module's property theorems quantify over, and that the K measurement is over
the same inputs list (by unfolding both, §7.6.1). **SHAPE M2R meets 4/4; the "3/4"
row is gone; all 12 node-realizable families now meet the full bar.** Zero solver
verdicts added.

### F18 — **RESOLVED by task G2** (stage 11). Not expressible; renamed, bounded, and audited use by use

**Verdict on expressibility: NOT EXPRESSIBLE in PlutusV3 `TxInfo`, and now proved so
by construction.** The ledger's `redeemersNeeded` keeps a needed `(purpose, hash)`
pair only if `Map.lookup hash scriptsProvided` succeeds AND the script found there
satisfies `not (isNativeScript script)`
(`Alonzo/Rules/Utxow.hs:245-262`, `isNativeScript = isJust . getNativeScript`,
`cardano-ledger-core/src/Cardano/Ledger/Core.hs:586-587`). Of the two filters:

* the `scriptsProvided` filter is a **no-op** on any transaction that reaches the
  rule — `babbageMissingScripts` (`Babbage/Rules/Utxow.hs:191-206`, run at `:344`)
  already rejects unless every needed hash is provided, so the lookup always
  succeeds. Dropping it costs nothing;
* the `isNativeScript` filter is **not recoverable**. Every needed script HASH is
  derivable from `TxInfo`, but `isNativeScript` is a predicate on the script BODY,
  and `TxInfo` carries no script bodies and no language tags — its only
  script-shaped field is `TxOut.txOutReferenceScript : Option ScriptHash`
  (`CardanoLedgerApi/V2/Tx.lean:78-83`), a bare `ByteString`
  (`V1/Scripts.lean:15-16`); the witness script set has no `TxInfo` field at all.
  **The missing information is exactly one bit per needed script, and `TxInfo` does
  not contain it.**

**What G2 landed** (`CardanoLedgerApi/V3/Contexts.lean`,
`WSC/Props/Shaped/ShapeRealizability.lean` §2.2/§2.3, `WSC/Realizability.lean`,
`WSC/Honest.lean`, `WSC/Props/Shaped/GlobalRealizability.lean` §4):

1. **Renamed at every use site.** `redeemerCoverage` → `redeemerCoverageAllPlutus`,
   `noExtraRedeemers` → `noExtraRedeemersAllPlutus`, `redeemersExact` →
   `redeemersExactAllPlutus`, the `Prop` `RedeemerCoverage` →
   `RedeemerCoverageAllPlutus`, and the three consequence lemmas to
   `…_of_coverageAllPlutus`. `LR_REDEEMER_COVERAGE` keeps its name (renaming an
   axiom would renumber the census) but its statement now literally reads
   `redeemerCoverageAllPlutus` and its docstring carries the over-strength warning.
2. **The faithful rule is stated, modulo an oracle**, and the direction claims are
   now THEOREMS rather than commentary — all six at `[propext, Quot.sound]`, no
   project axioms, no `sorryAx`: `coveredByNonNative`, `redeemerCoverageModNative`,
   `noExtraRedeemersModNative`, with `redeemerCoverageModNative_allPlutus` (ours is
   the `fun _ => false` instance), `redeemerCoverageModNative_of_allPlutus` (**the
   positive direction: ours implies the true rule for EVERY language assignment**),
   `coveredByNonNative_strictly_weaker` and `noExtra_not_conservative` (**the two
   negative directions, by explicit counterexample**).
3. **Every negative use audited individually** — the table is
   `ShapeRealizability.lean` §2.3. Result: **6 of 13 unaffected** (all the
   SPENDING-route ones: `t1_class_is_empty`, `t1Shape_is_empty`,
   `t1_leafSet_is_vacuous`, `t2/t6/t7_class_is_empty` — they use
   `LR_SPEND_RUNS_VALIDATOR` + `validScriptInfo`'s first conjunct, never
   `scriptsNeeded`, and `Deployed` pins the script to a compiled Plutus V3
   validator); **6 downgraded** to an explicit non-native side condition
   (L1/DT1/M1 on `w0`, G1/S1/T1-withdrawal-route on `w1`, DS1 on both) because in
   every one of those shapes the witness credential is a FREE `ByteString`
   parameter that nothing pins to a Plutus script; **1 measurement**
   (`all_old_witnesses_fail_c3_coverage`) whose statement survives verbatim and
   whose *interpretation* as "unrealizable" is downgraded.
4. **The downgrade is in the types, not only the prose.** The six conditional
   emptiness theorems now take `RedeemerCoverageAt w` — coverage at the ONE
   credential the proof turns on — which is strictly weaker than before and has
   two visible suppliers: `RedeemerCoverageAt_of_allPlutus` (over-strong) and
   `RedeemerCoverageAt_of_true` (the true rule + `¬ isNative w`).
   `WSC.g6_class_is_empty`, the one negative result that was stated
   UNCONDITIONALLY via the axiom, is joined by `g6_class_is_empty_nonNative`,
   which carries `¬ isNative w1` explicitly and whose census is
   `[propext, Classical.choice, Quot.sound, WSC.OnChain]` — **no
   `LR_REDEEMER_COVERAGE`.**

**Residual risk: LOW, and now bounded.** Nothing positive changes — no
realizability inhabitant, no leaf, and neither composed containment theorem
consumes any `*_under_coverage` theorem or `g6_class_is_empty`. What is weaker is
the JUSTIFICATION for retiring the pre-C2 shapes: "empty" becomes "empty unless
the uncovered withdrawal is witnessed by a native timelock". **This weakens the
library's self-criticism, never its claims.** "Unconditional" in the surviving
docstrings now means what it says only for the six spending-route results.

Verified green by G2 at its own commit `9e5d417`: 431 jobs, **159 verdicts (102 ✅
Valid + 57 ✅ Expected Falsified), 0 errors, 20 sorry warnings, 5 unused-variable —
delta 0 against the sealed baseline**, since G2 added no `blaster`/`solve`
invocation. **Re-confirmed at G3 by differencing the per-file marker table at
`f4486ca`**: `ShapeRealizability.lean` and `GlobalRealizability.lean` contribute
0 markers before and after, so all three of G3's extra verdicts belong to G1.

### F19 — was LOW/OPEN → **CLOSED by G1 at `f4486ca`** (§7.6.2)

`P4_local_noEscape_shapedIdx` ranged over SHAPE L2, whose class is **proved empty**
under `RedeemerCoverageAllPlutus` — a headline-adjacent theorem over a class known to
be empty. **It is now superseded.** SHAPE **L2R**
(`WSC/Shaped/MintingLocalShapedRIdx.lean`) is the same loosening rung — the `Local`
arm's registration reference-input index left symbolic — cut over the
**node-realizable** two-entry redeemer map, and it carries the full four-item bar.
**`P4_local_noEscape_RIdx` (`P4LocalShapedR.lean:616`) is the theorem to cite.**
SHAPE L2R **definitionally contains** SHAPE L1R (`localRCtxIdx_at_one`, by `rfl`), so
this is a strict strengthening of `P4_local_noEscape_R`, not a lateral move.

**Two things that remain true and must travel with the citation:**

* The headline is derived from a `✅ Valid` **negative control**, not from a direct
  solver verdict; the direct goal is `⚠️ Undetermined` at a 300 s cap. The derivation
  is sound and the negative control is *strictly stronger* (§7.6.2), but a reviewer
  should know which statement the solver actually saw.
* **C1 at SHAPE L2R is still `⚠️ Undetermined` and is not asserted.** Only the
  no-escape conjunct was carried up the rung. C1 at the concrete-index SHAPE L1R
  (`P4a_local_R`) is unaffected.

The stale "L2 was not re-cut / must not be quoted" language has been removed from
`STATUS.md` and `README.md` here. `P4LocalShaped.lean:407` (the superseded L2
theorem) and `RealizableShapes.lean:64` still carry pre-L2R wording; `WSC.lean:230`
carries a pointer note. Flagged as a documentation follow-up, not a result.

### F21 — INFORMATIONAL, NEW at G3. The build log contains two lines beginning `Error:` that the "zero errors" instrument does not see

`CardanoLedgerApi/V3/Contexts.lean` emits, at the `noExtraRedeemersAllPlutus`
definition, a Lean **`panic!`** surfaced as an `info:` diagnostic with a C++
backtrace:

```
info: CardanoLedgerApi/V3/Contexts.lean:1383:0: Error: invalid `Name.append`,
      both arguments have macro scopes, consider using `eraseMacroScopes`
```

It comes from CLAB's own `Recursor.all` macro, the definition elaborates anyway, and
**the build exits 0**. So it is benign. It is recorded for two reasons. First, the
campaign's hard requirement is stated as "`error:` lines = 0", measured with a
line-anchored grep; that grep is **case-sensitive and anchored**, so a line reading
`Error: …` in column 0 (log line 474 of the G3 run) passes it. The requirement is met
on the correct reading — zero Lean *error* diagnostics, exit status 0, both runs —
but the instrument is narrower than its name suggests. Second, this is **pre-existing,
not G2's doing**: it appears in the C4-era log (`c4-final.log`, 11:24) at the same
definition, then line 1255, now line 1383. G2 flagged it against itself and G3
confirms the flag by differencing logs.

### F22 — INFORMATIONAL, NEW at G3. Two shape bridges have no non-vacuity witness

`bridge_GIdx` and `bridge_GNIdx` (`ShapeBridge.lean:900-948`) are `↔` biconditionals
between `appliedGlobalShapedIdx1600.prop` / `appliedGlobalShapedNIdx1600.prop` and
`appliedGlobal1600.prop`. They are the **only** results over those two terms, and
neither term carries a vacuity probe, a concrete accepting witness, or a
`…_at_<index> = globalShapedCtx` reduction lemma — `WSC/Shaped/GlobalShapedIdx.lean`
contains **defs only, no theorems**. An `↔` between two unsatisfiable statements is
true, so if the GIdx/GNIdx accept-classes were empty at budget 1600 both bridges would
hold vacuously and nothing in the build would say so.

**Severity: informational.** Neither bridge is load-bearing — grep finds them cited
only in `SHAPE-BRIDGE.md:323` and in `ShapeBridge.lean:1504`'s own narrative, never
consumed by a property or a composed result. Their sibling `bridge_G1` **does** have a
concrete witness (`prop_accepts_1600`). The cheap fix is one `rfl` lemma showing
`globalShapedCtxIdx … 0 nIdx` reduces to a `globalShapedCtx` instance, which would
inherit G1's witness; G3 did not write it (not its file, and it is not a result).

### F15 — INFORMATIONAL. Budget instantiations: 3 of 7 exercised

`LR_BUDGET_base` @600, `LR_BUDGET_global` @4400, and now `LR_BUDGET_seize` @3800.
`LR_BUDGET_minting` is applied by nothing.

### F5, F7, F13, F14, F16 — CLOSED, unchanged since C4.

---

## 9. WHAT A REVIEWER SHOULD NOT BELIEVE

1. **Do not believe "the WSC containment property is proved."** It is (a)
   machine-checked as a *reduction* to four leaf obligations plus 26–28 project
   axioms, (b) discharged outright over one inert accounting class, and (c)
   discharged **completely** over two **node-realizable shape classes** — in each of
   which **the code does one quarter of the work and the shape does three quarters**.
   None of the three is the claim.
2. **Do not quote "N = 0" without the ratio.** Closing the last leaf hypothesis cost
   zero axioms and added zero bytecode content (§3.4). It is a statement about
   bookkeeping honesty, not about the validators.
3. **Do not believe the shapes cover anything.** Coverage is now **proved false** for
   this family at the smallest bound the family itself covers, with witnesses the real
   CEK accepts in the same number of steps as the certified inhabitant (§8
   F2-coverage). Every result is "over this layout".
4. **Do not believe the shapes are unrealizable — and do not believe they are
   node-buildable either.** A3's blanket "every shape is empty" is obsolete for 11 of
   12. What replaced it is narrower than it sounds: each re-cut shape has a concrete
   inhabitant satisfying CLAB's ledger predicate **and** both halves of the Conway
   redeemer rule, while `OnChain` remains an opaque axiom, so no term here proves any
   context genuinely on-chain. Fees, witness-set agreement and the UTxO set are still
   unmodelled.
5. **Do not believe any UPLC result is universally quantified over transactions.**
   Every one is bounded by a CEK step budget AND a fixed `Data` skeleton. Quote both
   bounds or quote neither. §5.2 exhibits a theorem that provably does not generalise
   — and it is now load-bearing in a composed result.
6. **Do not believe "`sorry`-free".** **101** theorem-position results are
   `admit`-closed; every top-level theorem inherits `sorryAx`. And do not use the
   build log's `sorry` warning count as a census — 38 modules suppress it.
7. **Do not believe the witnesses and the theorems are always about the same term.**
   For the shaped layer — including both composed results, via `bridge_T1R` and
   `bridge_S1R` — theorems are on `.prop`, witnesses and all measured K on `.exec`,
   equality unproved (F8). Name the layer when quoting this.
8. **Do not believe the source-model and shaped routes are the same strength.** The
   model route quantifies over all contexts and all step counts but trusts a hand
   transcription; the shaped route trusts no transcription but is doubly bounded.
   Neither dominates.
9. **Do not believe the prep-cost figures in `K-MEASUREMENTS.md` §5.1** (F5). Measure
   with `lake build`, never `lake env lean`.
10. **Do not quote SHAPE L2's theorem** `P4_local_noEscape_shapedIdx` — its class is
    proved empty. **Quote `P4_local_noEscape_RIdx` (SHAPE L2R) instead** (F19,
    §7.6.2), and when you do, carry the two riders: the headline is derived from a
    `✅ Valid` negative control rather than from a direct verdict, and **C1 at L2R is
    `⚠️ Undetermined` and is not asserted.**
11. **Do not believe this builds elsewhere without work.** It now *can* (§6.2,
    `WSC/REPRODUCE.md`), but only after reconstructing the substrate from the bundle
    and editing two files. The branch is still unpublished.
12. **Do believe, because it is machine-verified:** the four `.flat` files are
    byte-identical to the `cborHex` of the named unapplied production scripts at
    wsc-poc `f918ec6` on `main` (§6.1, 4/4, re-verified here; measured at the
    export commit `7ae0024`, identical tree); the redeemer-coverage rule
    reproduces the real node's output on 13/13 goldens (§4b); the re-cut cost zero CEK
    steps; and the substrate bundle reconstructs the pinned tree byte-identically
    (§6.2).

---

## 10. REPRODUCTION

Full third-party recipe, including substrate reconstruction: **`WSC/REPRODUCE.md`**.
The short form:

```bash
# 1. clean-room rebuild  (expected values are CURRENT, i.e. post-H2-cleanup;
#    at HEAD f4486ca they were 432 jobs / 94 modules — §1.2's last two columns)
#    expect: 431 jobs, 1:49-2:36, 162 ✅ markers (103 Valid + 59 Expected Falsified),
#            0 errors, 0 ⚠️/❌, 20 expected `sorry` warnings, 93 WSC modules,
#            5 `unused variable` warnings (all Composition.lean:2442-2446),
#            RSS 1.50-1.66 GB (LOAD-DEPENDENT — not an instrument, §1.2)
cp -a <CLAB> <SCRATCH>/clab-audit && cd <SCRATCH>/clab-audit
rm -rf .lake/build/lib/lean/WSC .lake/build/lib/lean/WSC.*
/usr/bin/time -v lake build WSC WSC.ShapeBridge 2>&1 | tee build.log

# 2. marker / sorry / error census
grep -o '✅ [A-Za-z ]*' build.log | sort | uniq -c   # 103 Valid, 59 Exp. Falsified
grep -cE '⚠️|❌' build.log; grep -c '^error:' build.log            # 0  0
#   NB (F21): two lines beginning `Error:` DO appear — a panic! from CLAB's
#   Recursor.all macro at V3/Contexts.lean. Pre-existing, benign, exit status 0.
grep -c "declaration uses 'sorry'" build.log                       # 20  (NOT a census — §2)
grep -c 'unused variable' build.log                                # 5

# 3. source reconciliation — DO NOT count stanzas and compare totals (§1.4).
#    Take each `file:line:col: ✅ …` from the log, read THAT line out of the tree:
#      59 x `#blaster … (solve-result: 1)`  -> 59 Expected Falsified
#       2 x `#blaster … (solve-result: 0)`  ->  2 Valid
#     101 x `blaster` TACTIC                -> 101 Valid       (59 + 2 + 101 = 162)
#    SIX of the 101 are `:= by` with `blaster` on the NEXT line, and one of those six
#    carries an argument (`blaster (timeout: 300)`), so no single grep finds them all.

# 4. axiom census — TWO traps, both must be handled (§3):
#      (a) PARSE ACROSS NEWLINES; a line grep undercounts sorryAx 17 vs 37
#      (b) parse BOTH output forms — 5 results say "does not depend on any axioms"
#          with NO brackets; a bracket-only parser returns 167/117 instead of 172/122
#    expect: 172 results, 37 sorryAx, 122 with zero project axioms, 70 native_decide
#            (at HEAD f4486ca: 174 / 37 / 124 / 72 — §3's H2 note)
#      Composition.containment_on_contained_class        -> 26
#      RealizableLeaves.containment_on_realizable_class   -> 28 (= 26 + LR_BUDGET_global + TS3)
#      RealizableLeaves.containment_on_seize_class        -> 28 (= 26 + LR_BUDGET_seize + nodeStepsSeize)
#      RealizableLeaves.realizable_inhabitant{,_NS,_S1R}  -> 0, no sorryAx
#      Coverage.not_covers_at_T1R_size                    -> 0, no sorryAx
#      g6_class_is_empty        -> 2 (LR_REDEEMER_COVERAGE, OnChain)
#      g6_class_is_empty_nonNative -> 1 (OnChain)            # G2's true-rule form

# 4b. EXISTENCE CHECK — run this BEFORE anything above if you are gating a unit (F20).
#     Resolve each claim to a commit, a path, a declaration, and a reading:
git log --format='%H %an %s' -5
git show --stat <commit>            # an empty diffstat is the F20 signature
grep -n 'exec_accepts_at_900\|K_is_784' WSC/Props/Shaped/P4ShapedRIdx.lean     # F17
grep -n 'P4_local_noEscape_RIdx\|P4_local_RIdx_' WSC/Props/Shaped/P4LocalShapedR.lean  # F19
grep -n 'RedeemerCoverageAt' WSC/Props/Shaped/ShapeRealizability.lean          # F18

# 5. axiom-declaration census
grep -rn '^axiom ' --include='*.lean' WSC/ | wc -l                                  # 51
grep -rn '^axiom ' --include='*.lean' WSC/Prep WSC/Shaped WSC/Props/Shaped | wc -l  # 0
grep -rl 'set_option warn.sorry false' --include='*.lean' WSC/ | wc -l              # 38

# 6. the re-cut, checked in both directions
#      RealizableShapes.all_recut_witnesses_redeemersExact
#      RealizableShapes.all_old_witnesses_fail_c3_coverage
#      Goldens.Audit.every_golden_is_redeemer_covered            # 13/13

# 7. PROVENANCE re-verification (§6.1) — 4/4
sha256sum WSC/flats/*.flat

# 8. SUBSTRATE re-verification (§6.2) — see WSC/substrate/README.md §3
git bundle verify WSC/substrate/pcb-cip153-value-builtins.bundle
```

**Always time with `lake build`, never `lake env lean`** — the latter omits
`--load-dynlib`, runs Blaster interpreted, and is 15–50× slower. That artefact is the
entire content of F5.

---

## 11. THE PLAIN STATEMENT (added at G3, and this is the paragraph to quote)

Written without hedging, because a reviewer who reads only one section should read
this one and should not be able to mistake what it says.

### 11.1 What the formalization establishes about the target sentence

The target sentence is **"in an honest deployment, programmable tokens cannot exist
outside the mini-ledger."**

**It is not proved. It is not nearly proved. What exists is a reduction plus six
bounded facts about the real code.** Precisely:

1. **The sentence is reduced, by machine, to four leaf obligations plus 28 named
   assumptions.** The reduction itself is real and is the durable asset: anyone who
   later discharges the four leaves over an unrestricted class gets the sentence.
   The 28 are a **floor, not a ceiling** — they are what the *current* proof term
   consumes, and a stronger result will consume more, not fewer.
2. **Six safety properties (P1–P6) of the four production validators are proved
   against the real compiled bytecode**, whose byte-identity to the deployment is
   cryptographically re-verified 4/4 at every audit. These are genuine facts about
   the deployed programs, not about a model of them.
3. **All four leaf obligations are discharged, with no remaining hypothesis, over
   two specific classes** — one transfer, one seize. **On each side, exactly one of
   the four leaves is carried by the bytecode; the other three are true because the
   class is too narrow for them to arise.** One quarter code, three quarters
   narrowness. That ratio did not improve at any point in stage 11 or the G stage.
4. **The classes provably do not cover real traffic.** `WSC/Coverage.lean` refutes
   coverage at the smallest bound that admits a real transfer, exhibiting three
   node-realizable transactions the production bytecode accepts in exactly the
   certified witness's 2,603 CEK steps and which lie outside all re-cut shapes. Two
   differ from a covered transaction only by a **list length**; one only by a
   **constructor tag**. Enumerating the gap costs ≈971 CPU-years for one property.

So: **the formalization establishes that the containment claim reduces cleanly to
four checkable obligations, that six specific safety behaviours of the deployed code
hold within measured bounds, and that the technique used to prove them cannot be
scaled to the full claim.** The last of those is the most valuable thing here, and it
is a negative result the project produced about itself.

### 11.2 What a reviewer would still be right to doubt

Every item below is something this audit agrees with.

* **That "machine-checked" means kernel-checked. It does not.** 101 theorem-position
  results are closed by the solver's `admit`; **both** composed containment results
  carry `sorryAx`, as does every top-level theorem. The verdict is a line in a build
  log. This is a defensible engineering trade — it is what makes analysing real
  compiled bytecode affordable — but it is not the same guarantee as a kernel proof,
  and the build's own `sorry` warning count (20) badly understates it because 38
  modules suppress the warning.
* **That the theorems and the executions are about the same term.** They are not,
  and this is F8: shaped theorems are stated on `.prop` (the optimizer's output),
  while every witness and every measured `K` is on `.exec`. Their equality is
  **unproved**, and `PropExecFaithful` — the statement that would close it — binds
  **both** composed results. A reviewer who assumes the two coincide is assuming
  something the library does not prove.
* **That `OnChain` and `Deployed` mean what they say.** They are **opaque axioms**.
  No term in this library proves any context is genuinely on-chain, or that any hash
  is genuinely the deployed one. Fees, witness-set agreement and the UTxO set are
  unmodelled.
* **That the results generalise beyond their bounds.** Every UPLC result is bounded
  **twice**: by a CEK step budget and by a frozen `Data` skeleton. §5.2 exhibits a
  load-bearing theorem that provably does not generalise.
* **That the redeemer-coverage predicate is the ledger's rule.** It is not — it is
  the **all-Plutus specialisation** (F18). It is conservative where the library uses
  it positively, and **six emptiness results are strictly weaker than they read**,
  now carrying an explicit `¬ isNative w` side condition in their types.
* **That this is reproducible by a third party today.** It is reproducible from the
  shipped bundle, which this audit reconstructed byte-identically — but the
  substrate branch is **unpublished**, so **the bundle's custody is the trust
  anchor**, and building elsewhere still requires a two-file manual edit.
* **That the shapes were chosen neutrally.** `SizeBound`'s five dimensions are a
  modelling decision. If an overclaim is hiding anywhere, it is there.

### 11.3 The three highest-value next steps, in priority order

1. **Invest in UNSHAPED prep/solve cost.** (This item used to begin "Fix Blaster
   defect D6"; **D6 is fixed** — see the D6 entry — so only the second half stands,
   and it got HARDER, not easier.) **The existence proof that the unshaped route
   works is GONE.** It used to be P3, the one property proved with no shape
   restriction; PR #112 gave the base validator a real redeemer and P3 no longer
   closes unshaped — task N3 measured `⚠️ Undetermined` at a 600 s Z3 cap, again at
   2400 s, and again with the redeemer skeleton frozen. **Not one property in the
   library is now proved unshaped**, so this step is no longer "make the demonstrated
   route cheaper" but "make an undemonstrated route work". The one encouraging
   measurement is N6's SHAPE B1W (`WSC/Props/P3_BaseWdrl.lean`): freezing a SINGLE
   ledger-level dimension — the withdrawal map's length — closes P3 in ≈5 s with the
   redeemer and both script parameters fully symbolic. That suggests the tractable
   frontier is minimal LEDGER-level cuts, not `Data`-skeleton cuts. This is the only step on
   this list that attacks the binding constraint rather than working around it, and
   it is why **the standing recommendation is to NOT start a coverage programme** —
   at ≈971 CPU-years for one property at the smallest realistic bound, enumeration
   is not an engineering option and no amount of care makes it one.
2. **Close F8 — prove `PropExecFaithful`, or restate the composed results on
   `.exec`.** This is the cheapest remaining item with real reviewer value. Today
   every witness, every measured `K` and every acceptance demonstration lives on a
   term that the theorems do not mention. Until it is closed, the honest form of
   every headline needs the phrase "on the optimizer's output", and both composed
   results inherit the gap.
3. **Publish the PlutusCoreBlaster branch and restore a git pin.** A one-line fix
   that retires the last structural part of D5 and converts "trust the bundle we
   shipped you" into "fetch it yourself". Everything else about reproducibility is
   already done.

**Explicitly NOT on this list, and deliberately so:** a shape-coverage programme
(item 1's rationale), and any further loosening rung of the L2R kind. The L2R rung
was worth doing because it retired a theorem quantified over an empty class, but it
cost a 300-second solver cap, left C1 `⚠️ Undetermined`, and moved the code/shape
ratio not at all. **Loosening rungs buy narrowness, not coverage.**

---

## 12. THE DEAD-FILE AUDIT (task H2, the PRE-#112 stage — not the 2026-07-28 dispatch-path task of the same name) — the full decision table

**What this section is.** The campaign accreted files for eleven stages. Before the
work is submitted as a PR, every file in `WSC/` was asked three questions and the
answers are recorded here rather than left in a diff, because the interesting cases
are the ones a reviewer would *expect* to be dead and which are not.

The three questions, and the rule:

1. **Does any Lean term outside the file depend on anything it declares?**
   (measured: `grep -rl '^import <module>$'` over the tree, plus a name-level grep
   for every declaration in the zero-importer cases)
2. **Is it cited in prose by a document or by a surviving module's docstring?**
   (measured: grep for the path, the basename, the brace-expanded form
   `{A,B}.lean`, and the module name `WSC.Shaped.Probe.X`)
3. **Is its content duplicated by something strictly better?**

**DELETE only when (1) is no AND (3) is yes, or when the file is pure scratch cited
by nothing.** A prose citation from a surviving module is by itself disqualifying:
deleting a probe that `NonVacuity.lean` names as the provenance of a quoted `K`
would convert a measured number into an unsourced one. That is why so many
zero-importer probes below are KEEP.

### 12.1 What was deleted — six files, and every one of them justified

| file | (1) Lean dependents | (2) prose citations | (3) superseded by | verdict |
|---|---|---|---|---|
| `WSC/Props/P5_Witness1600.lean` | **none.** No module cites `WSC.Witness1600.golden_halts_at_1600` or `…golden_errors_at_1553`; the only `import` was `WSC.lean`'s, i.e. it was in the build but nothing consumed it | 6 (5 × `P5_NonMember.lean`, 1 × `Honest.lean`) + 1 in `status-fragments/U2.md` — **all seven repointed, not dropped** | its two facts are established three further times and better: `P5ShapedWitness.exec_accepts_at_1600_unshaped` (theorem on `appliedGlobal1600.exec`, the term P5 quantifies over, `native_decide`, no `sorryAx`), `ShapeBridge.G1NonVacuity.globalNonVacuous_at_1600` (about the `prop` term), and `NonVacuity.globalNonVacuous_at_1600` — the one that actually discharges the `Honest.lean` obligation, 0 project axioms, K = 1541 pinned two-sided by `P5ShapedWitness.K_is_1541` | **DELETE** |
| `WSC/Shaped/Probe/M1Probe.lean` | none (0 importers) | **zero, anywhere** | `Props/Shaped/P4Shaped.lean` states `P4a_shaped_mint_runs_minting_logic` over the same `appliedMintShaped900` term with its full control set and vacuity probe. Header says "Not a deliverable" | **DELETE** |
| `WSC/Shaped/Probe/M2Probe.lean` | none | **zero** | `Props/Shaped/P4ShapedIdx.lean`, same term, 3 V + 2 F | **DELETE** |
| `WSC/Shaped/Probe/G1Probe.lean` | none | **zero** | `Props/Shaped/P5Shaped.lean` (`P5_shaped_indexed` / `_exists` / `_groundtruth`) over the same `appliedGlobalShaped1600`. Header says "Not a deliverable" | **DELETE** |
| `WSC/Shaped/Probe/M1Pos.lean` | none | **zero** | four `#eval`s asking whether a POSITIVE-mint SHAPE M1 context is ledger-valid. Answered as a **theorem** by `P1ShapedWitness.mintPos_form_REFUTED` (`P1Shaped.lean:674`) and its re-cut twin in `P1ShapedR.lean:697`, and by four `mintPos … = false` `✅ Valid` verdicts in the built set | **DELETE** |
| `WSC/Shaped/Probe/U3Census.lean` | none | **zero** (its own docstring is the only mention) | it aggregates ~40 `#print axioms` calls and claims to "reproduce the table in `WSC/AUDIT.md` §3". It no longer can: §3's census is **172 results over the whole built set**, and U3Census names none of the E1/E4/G-stage headline results (no `RealizableLeaves.*`, no `Coverage.*`, no `g6_class_is_empty_nonNative`) while still naming `P4_local_noEscape_shapedIdx`, which §9.10 says must not be quoted. A stale instrument that under-reports is worse than none; §10 step 4 is the recipe that gets all 172. Its own header states it "can be deleted without affecting any result" | **DELETE** |

**Measured effect on the build** (`lake build WSC WSC.ShapeBridge`, clean-room,
own before/after control runs on the same box under the same load):

| | before (`f4486ca`) | after |
|---|---|---|
| jobs | 432 | **431** (−1: only `P5_Witness1600` was in the build at all; the other five are not imported by anything and are never elaborated) |
| WSC modules re-elaborated | 94 | **93** |
| **solver verdicts** | **162 = 103 ✅ Valid + 59 ✅ Expected Falsified** | **162 = 103 + 59 — IDENTICAL** |
| per-verdict source reconciliation (§1.4) | 59 + 2 + 101, 0 unclassified | **59 + 2 + 101, 0 unclassified** |
| `error:` / `⚠️` / `❌` | 0 / 0 / 0 | **0 / 0 / 0** |
| `declaration uses 'sorry'` | 20 | **20** |
| `unused variable` | 5 | **5**, same lines |
| `#print axioms` results | 174 (37 `sorryAx`, 72 `native_decide`, 124 zero-project-axiom) | **172 (37, 70, 122)** — the −2 are the two `Witness1600` theorems, both builtins-only, so **no project-axiom or `sorryAx` figure anywhere in §3 moves** |
| `#import_uplc` sites under `WSC/` | 9 | **8** |

**No verdict was lost, so no verdict needs pinning to a source line.** That was the
acceptance criterion and it is met exactly.

### 12.2 What was NOT deleted, and why — the cases that look dead

These are the traps. Each was a plausible delete candidate on question (1) alone.

| file(s) | why KEEP |
|---|---|
| **the pre-re-cut shape modules and their Props** (`Shaped/{BaseShaped,MintingShaped,MintingShapedIdx,MintingLocalShaped,MintingLocalShapedIdx,MintingDelegateShaped,GlobalShaped,GlobalShapedIdx,GlobalMemberShaped,GlobalShapedP1,GlobalShapedP1Out,SeizeShaped}.lean`, `Props/Shaped/{P1Shaped,P2Shaped,P4Shaped,P4ShapedIdx,P4LocalShaped,P4DelegateShaped,P5Shaped,P6Shaped}.lean`) | **the emptiness proofs are STATED OVER THEM.** `ShapeRealizability.lean` and `GlobalRealizability.lean` prove T1/T2/T6/T7, G1, G6, M1, M2, L1, L2, DT1, DS1, S1 empty *as classes of ledger transactions*; those theorems are the entire before/after column that makes the C1/C2 re-cut mean anything, and they need the pre-re-cut shape builders to exist. They also carry **44 of the 162 verdicts** between them |
| `Shaped/Probe/{T3PrepFAILS,T4PrepFAILS}.lean` | the **D6 reproductions**, now **REGRESSION TESTS** — D6 was fixed at N5 and both modules build (exit 0). Filenames are historical and their headers say so. Still not imported by `WSC.lean`, so run them deliberately. T3 additionally carries `T3_vacuity_probe` (✅ Expected Falsified), the measurement that Paths B/C are reachable. Superseded as a RESULT by task H2's SHAPES T3R/T4R, which are node-realizable and are imported by `WSC.lean`; kept as regression tests. Cited 9× and 6× |
| `Shaped/Probe/G6Vacuous2500.lean` | the cautionary case §4 opens with: a `✅ Valid` over an accept-UNSAT class, caught only by the mandatory probe. Cited 7×, incl. `README.md:268`, `REPRODUCE.md:184`, `Honest.lean:1191`, `NonVacuity.lean:80/158`, and §4 of this file |
| `Shaped/Probe/L2RProbe.lean` | the `⚠️ Undetermined` measurement **behind** `P4_local_noEscape_RIdx`'s derivation. Cited by `P4LocalShapedR.lean:522/535/549` and by §1.3/§4.2/§7.6.2 here. Out of the build **on purpose** — that is what keeps the built set at 0 `⚠️` |
| `Prep/Global.lean` (`:83` `global_vacuity_probe_600`) and `Props/P4_Minting.lean` (`:386` `minting600_is_vacuous`) | the two deliberate **`solve-result: 0`** stanzas. Their `✅ Valid` markers are 2 of the 162 and are *records of vacuity*, not proofs of safety (§1.4) |
| `Model/*` (5 modules) | ~~`pathC_sound`, which covers a containment dispatch path that has no node-realizable UPLC shape~~ — **superseded at task H2**: SHAPE T3R exists and PATH C is now proved executed and true at UPLC (`T3R_pathC_is_taken`, entry **H2**), so `pathC_sound` is a source-model corroboration rather than the only evidence. **The library's only unbounded result, `P2.P2a_seizeModel_preserves_structure`, is REFUTED at 2306678** — `seizeModel_faithful` is false of the post-#112 bytecode and `Model/SeizeModelRefuted.lean` proves it by computation, so `Model/*` no longer supplies an unbounded seize result |
| **the K-search and prep-ceiling probes** — `Shaped/Probe/{M1K,G1K,L1K,DSRK,DTDSK,S1K,G1Witness,T1Probe,T4Probe,T6Probe,L1Probe,L2Probe,L2Reg,DTDSProbe,G2Probe,G3Probe,G6Diag,MPrep1700,MPrep2500,GPrep2500,GPrep4000,BasePrepUnshaped,UnshapedCost,B1Accept,AxAudit,Axioms,P1Axioms,V3Axioms,BridgeProbe,BridgeProbe2FAILS,BridgeProbe3..7}.lean` | 0 importers every one of them, **and every one is cited in prose as the provenance of a number that IS quoted** — e.g. `NonVacuity.lean:70/74/77` names `L1K`/`G1K`/`G6Diag` as where K = 1681 / 1541 / 2837 were searched; `P4DelegateShapedR.lean:546` names `DSRK`; `P4LocalShaped.lean:84` names `L2Reg` for the registration `⚠️ Undetermined`; `SHAPING-RESULTS.md` §§ and `SHAPE-BRIDGE.md:516-525` are inventory tables over them. Deleting any of these turns a measured figure into an unsourced one. **Note the grep trap:** several are cited only in brace-expanded form (`Probe/{M1K,G1K}.lean`, `Probe/{MPrep1700,MPrep2500,GPrep2500,GPrep4000}.lean`), so a basename grep reports them as uncited. They are not |
| `Prep/Minting1300.lean` | declares **no theorem** and its `appliedMinting1300` is used by no theorem (§4.1 says so) — and it is still load-bearing, because the module header *is* the F5 correction to `K-MEASUREMENTS.md` §5.1: the native-vs-interpreted prep table and the "affordable ceiling is 1700, 2000 dead" figure, cited by `P4_Minting.lean:212` and `Prep/Minting800.lean:20`. Its 9.6 s of build cost is itself the measurement |
| `goldens/prep-probes/*.lean.disabled` (9), `goldens/{KMeasure,KVerify}.lean.disabled` | the reproduction inputs for `K-MEASUREMENTS.md` §§2.1/3/5.1 and `MANIFEST.md:189-194`. §5.1's method is superseded and its figures carry a DO-NOT-USE warning (F5), but the probes are the *provenance* of figures that are still published with that warning; deleting them would leave §5.1's provenance column dangling |
| `goldens/pre-fix/**` (26 files) | the pre-D1-fix vectors, over which `Honest.lean:687` states a **FALSE-at-this-revision** predicate and `K-MEASUREMENTS.md` Appendix A states the superseded step counts. Deleting them deletes the before side of a before/after |
| `goldens/applied/*.flat` (13) | provenance-verified applied programs (`MANIFEST.md`, `K-MEASUREMENTS.md` §2.1, `verify-applied.py`). **Note:** after deleting `P5_Witness1600.lean` **no Lean module reads any of them** — see 12.3 |
| `status-fragments/*.md` (7) | 4 of 7 are cited by surviving Lean modules or by `SHAPE-BRIDGE.md` (`V3.md` ← `WSC.lean:138` + `P6Shaped.lean:88`; `V1-P1-shaped.md` ← 5 sites incl. two probe headers; `z6-p2shaped.md` ← `SeizeShaped.lean:109`, `P2Shaped.lean:231`; `U1.md` ← `SHAPE-BRIDGE.md:515`). The other 3 (`U2.md`, `V4.md`, `C1-global-realizable.md`) are cited nowhere and self-declare supersession — but they are the **only** record of two latent-unsoundness findings and their in-code dispositions (`U2.md` §2: `LeafSet.p4`'s "`LR5`'s rewarding clause" remark does not follow, isolated as `Composition.SeizeWdrlOfScoped`; `V4.md`: the interval conjunct must be over the pre-state snapshot, and `I(L)` is false without `cs ≠ adaSymbol`), none of which appears in this file. Folding 600+ lines of per-unit history into a sealed audit is a larger and riskier change than keeping the fragments, and the repo's own precedent is explicit against rewriting them (`V3.md`'s H1 addendum: *"rewriting a per-task record would destroy the only thing it is for"*). **KEEP, with the one dangling name in `U2.md:41` given an inline pointer instead of a rewrite** |
| `CIP153-BUILTINS-REPORT.md` | cited by **nothing** — the only genuinely orphaned document in the tree — and kept anyway, because it is the sole record of the **substrate fidelity evidence**: the `plutus` line citations for flat builtin tags 94–99, the arities, the uni tag, the `Value.hs` semantics read, the cost-model provenance, and six named deviations from `Value.hs`. §6.2 pins the substrate's *bytes*; this file is the argument that those bytes are faithful. H2 added a pointer to it from `WSC/substrate/README.md` so it is no longer an orphan |

### 12.3 Two things H2 observed and did not fix

Recorded rather than silently corrected, in the register §7 uses.

1. **§1.1's "all 4 `#import_uplc` sites" was never right.** There are **9**
   `#import_uplc` commands under `WSC/` at `f4486ca` (8 after H2): four import the
   four production flats, four more re-import three of them at other budgets
   (`Global1600`, `Minting800`, `Minting900`, `Minting1300`), and the ninth was
   `P5_Witness1600.lean`'s import of an *applied golden*. The sentence is true of
   the four **flats** and false of the sites. It does not affect any measurement —
   the claim it supports is "every `#import_uplc` re-ran", which the 93-module
   re-elaboration count establishes independently.
2. **No Lean module now executes an applied golden flat, and that is a real loss.**
   `P5_Witness1600.lean` was the only reader of `WSC/goldens/applied/*.flat`. Its
   two theorems were the only *theorem-grade* bracket on an applied golden's step
   count (HALT at 1600, budget-`Error` at 1553, i.e. K = 1554 for
   `programmableLogicGlobal.transfer-nonmember-covering-node`). After H2 that
   golden's K = 1554 survives only as a **measurement** in
   `K-MEASUREMENTS.md` §3, reproducible via `goldens/KMeasure.lean.disabled`. The
   deletion is still right — the fact the module was *cited* for is non-vacuity at
   budget 1600, and that is now carried by a theorem about the term P5 actually
   quantifies over rather than about a different program — but a reviewer should
   know that the applied-golden execution path is no longer exercised from Lean.
   Restoring it, if anyone wants it, is a ~10-line module and adds zero verdicts.
