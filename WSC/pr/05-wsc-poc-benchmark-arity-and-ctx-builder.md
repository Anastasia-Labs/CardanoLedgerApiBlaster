# SUBMISSION 4 — wsc-poc: benchmark arity fix + three ledger invariants in the ScriptContext builder

**Repo** `input-output-hk/wsc-poc` · **branch** `fix/benchmark-arity-and-ctx-builder`
(`c18c525fca143af8933ceb729bdf2abe1976f806`) · **base** `main`
(`f918ec6` = merged #110) · **1 commit for this PR** (the branch's other commit,
`97160f8`, is unrelated — see `06-…md`)

House style follows the recently merged #108/#109/#110: `## Summary` with the headline
numbers, a section per change with measurements, an explicit `## Verification`, and a
`## Notes` that states the caveats rather than hiding them.

---
---

# PART 1 — PR DESCRIPTION (submit this)

## Summary

Two independent problems in the benchmark harness, both found by formalising these
`ScriptContext`s in Lean and checking them against a transcription of the ledger's own
context-validity rules.

1. **Four benchmark cases applied 2 of a validator's 3 arguments.** A partially-applied
   Plutus script evaluates to a **lambda**, and the harness scores success as `isRight` on
   the evaluation result — so these cases reported **PASS without running a single
   check**, and the cost they reported was the cost of building a closure. One case was
   under-reporting CPU by **5,336%**.
2. **`buildLedgerShapedScriptContext` produced contexts no real ledger would emit**, so
   the benchmarks were measuring impossible transactions — and the extracted golden
   vectors all failed a ledger-context predicate. Three artefacts, each independently
   forbidden on chain.

Neither is a validator bug. Both mean published benchmark numbers were wrong, and the
seize path in particular was under-counting real work.

## 1. Arity — four cases applied 2 of 3 arguments

* **`mkProgrammableLogicBase`** takes `(globalCred, seizeCred, ctx)`
  (`ProgrammableLogicBase.hs:722`). Three cases passed only two arguments, with the
  **context sitting in the `seizeCred` position**:

  | case | CPU before | CPU after | |
  |---|---:|---:|---:|
  | `programmableLogicBase` | 560,100 | **4,525,794** | **+708%** |
  | `programmableLogicBase.Tx.c3111df7.Spending` | 560,100 | **4,525,794** | |
  | `programmableLogicBase.Tx.d29ce2a9.Spending` | 560,100 | **4,525,794** | |
  | *memory* | 3,600 | **11,715** | **+225%** |

* **`mkProtocolParametersMinting`** takes `(paramsSpendScriptHash, oref, ctx)`
  (`ProtocolParams.hs:48`). Same shape, in the catalogue **and** in the scenario backend's
  `ssbProtocolParamsMintSpec`:

  | case | CPU before | CPU after | |
  |---|---:|---:|---:|
  | `protocolParamsMinting` | 992,100 | **53,932,564** | **+5,336%** |
  | *memory* | 6,300 | **143,435** | **+2,177%** |

**Cross-check that the new numbers are the true ones, not merely different ones:** the
scenario backend's `ssbBaseSpendSpec` already passed all three arguments, and its
per-invocation cost in the mainnet-dex row was **already exactly 4,525,794**. The broken
primary was the only outlier. Every other application site was audited against its
Plutarch signature; the remaining cases were correct.

## 2. Three ledger invariants in `buildLedgerShapedScriptContext`

**(a) `txInfoFee = 0` in every context.** Now `defaultBalancedTxFee = 500_000`, taken out
of the change output so value conservation still holds. A sub-min-UTxO leftover is folded
into the fee, which is what a real coin selector does — the ledger would reject such a
change output.

**(b) Withdrawal credentials were emitted in insertion order**, which put `0x40..` before
`0x14..` in the seize scenarios. Now `canonicaliseWdrl` / `compareCredentialLedger` sort
by the **ledger's** `Credential` order — `ScriptHashObj < KeyHashObj`, the **opposite** of
`PlutusLedgerApi`'s derived order — then bytewise. `comparePurposeLedger` gained the
matching equal-kind tiebreak, which fixes the `(Rewarding, Rewarding)` pair in
`txInfoRedeemers` at the same time. **Spending-before-Minting is deliberately left
alone:** that one is already what the chain emits — `cardano-ledger` orders
`txInfoRedeemers` by `ConwayPlutusPurpose AsIx` and never re-sorts.

**(c) The seize residual outputs carried no ada entry**, which min-UTxO forbids. Now
`ensureMinAda` gives every non-empty output value `minAdaPerTxOut`. The seize scenarios
gained a pubkey funding input to pay for it — the ada **cannot** come from the seized
inputs, because the seize validator's corresponding-output check
(`pvalueEqualsDeltaCurrencySymbol`) requires every non-seized policy, ada included, to be
preserved exactly.

**This is a NEW entry point, not a change to `buildBalancedScriptContext`, on purpose.** A
positive fee moves lovelace, the canonical withdrawal order moves withdrawal **indexes**,
and min-UTxO ada adds a value entry — so every redeemer witnessing a withdrawal index must
be written against them. The benchmark catalogue uses the new builder; the 67 unit tests
keep their precise hand-balanced contexts on the legacy one, and all 67 still pass.

The builder now also **errors rather than emit a context no ledger could produce**
(negative leftover, or a token-carrying change output below min-UTxO). That check caught
three scenarios whose inputs exactly matched their outputs, leaving nothing for a fee; they
are now funded (`programmableBurnCtx` 10→12 ada in, `programmableMintTopUpCtx` 6→8 ada in,
`programmableBurnRedeem10Ctx` 30→28 ada out, and the two 4-ada mint funding inputs → 8
ada).

**Redeemer layout consequence:** the seize redeemers' `issuerWdrlIdx` changes **1 → 0**, a
direct consequence of (b) — `issuerCred 0x14..` now sorts before `seizeCredBench 0x40..`.

## Cost effect — the point of (b) and (c)

The seize path was under-counting real value-parsing and withdrawal-scan work:

| scenario | primary CPU | | full tx |
|---|---|---:|---:|
| `SeizeAct1` | 51,571,527 → **60,231,630** | **+16.8%** | **+22.3%** |
| `SeizeAct5` | 146,588,911 → **155,249,014** | **+5.9%** | **+16.7%** |
| `SeizeAct2.PartialSeizeWithNoise` | 96,841,491 → **105,501,594** | **+8.9%** | **+15.6%** |
| `SeizeAct10/20/50/100/150` | — | | **+14.2…15.5%** |

The full-transaction deltas exceed the primary ones because the per-input
`programmableLogicBase` witnesses now scan one extra withdrawal entry before matching the
seize credential — **a real cost the descending order was hiding**. `SeizeAct150` is now
at **83.5%** of the mainnet memory budget (was 76.6%).

**One case gets cheaper:** `Mint.BusyTx20Outputs` **−4.0%**, because its 2-ada leftover is
now dust folded into the fee instead of a 21st output — the scenario now has the 20 outputs
its name claims.

## Verification

Re-run in full immediately before opening this PR, at `c18c525` on top of `main`
(`f918ec6`):

```
cabal build all                                    → exit 0
cabal test programmable-tokens-test                → All 67 tests passed (11.11s)   PASS
cabal test regulated-stablecoin-test               → All 18 tests passed (70.27s)   PASS
cabal test aiken-example-test                      → All 2 tests passed (4.53s)     PASS
cabal run benchmark-onchain-scripts                → 49/49 PASS, no balance violations
golden re-dump (13 vectors)                        → all 13 verified against the
    prod-exported scripts at PV11; 9 accepting → accept, 4 rejecting → reject
```

(`--extra-lib-dirs=/usr/local/lib` is needed locally for libsodium's VRF.)

## Notes

* **The arity bug is a harness bug, not a validator bug**, and it is the kind that hides
  in plain sight: a partial application is a perfectly good Plutus value, so `isRight`
  cannot tell it from a passing validation. Consider whether the harness should assert the
  evaluation result is a **`Unit`/`Bool` terminal value** rather than merely `isRight` —
  that would make this whole class of bug impossible. Not done here; it is a harness
  design change, not a fix.
* **Published benchmark numbers before this commit are wrong for four cases and
  under-stated for the whole seize path.** Any comparison table quoting the old
  `protocolParamsMinting` or `programmableLogicBase` numbers should be re-baselined.
* **The `issuerWdrlIdx` 1 → 0 change is a redeemer-layout change** driven by (b). It is
  correct — the index must match the canonical order the chain emits — but anyone holding
  an out-of-band redeemer for these scenarios must regenerate it.
* Both defects were found by an out-of-tree formal model of these contexts in Lean, which
  is not public yet. The ledger facts it relies on are cited directly to `cardano-ledger`
  in the commit message; nothing in this PR depends on that work.

---
---

# PART 2 — PRE-SUBMISSION NOTES (do not submit this part)

## 2.1 Branch state, measured in this task

| | |
|---|---|
| worktree | `/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d` |
| HEAD | `c18c525fca143af8933ceb729bdf2abe1976f806` |
| `origin/main` | `f918ec6` — PR **#110 is MERGED**, so the branch is based on current main |
| commits ahead of `origin/main` | **2**: `c18c525` (this PR) and `97160f8` (nix — **split out**, see `06-…md`) |
| uncommitted | one untracked directory, `scratch-goldens/` — **must not be committed**; add to `.gitignore` or delete |
| diffstat of `c18c525` | 131 files, +37,745/−579 — **the vast majority is regenerated benchmark output under `doc/`**, which is this repository's convention (#110 did the same) |

## 2.2 The one required edit to the commit message

`c18c525`'s message opens:

> *Two independent problems, both found by formalising these contexts in Lean
> (CardanoLedgerApiBlaster WSC/LR-CTX-AUDIT.md).*

`WSC/LR-CTX-AUDIT.md` is in a repository the reviewer cannot open, and will remain so
until submission 5 is placed. **Reword** to either

> *…found by formalising these contexts in Lean and checking them against a transcription
> of the ledger's context-validity rules (formalization not yet public).*

or keep the path and append `(private formalization repo, not yet public)`. Everything
else in that commit message is excellent and should be preserved verbatim — it is the
source of most of Part 1.

## 2.3 Verify the benchmark and golden claims before quoting them

This task re-ran `cabal build all` and all three test suites (results in Part 1, all
green). It **did not** re-run `benchmark-onchain-scripts` (49/49) or the 13-vector golden
re-dump; those two lines in Part 1 are carried from `c18c525`'s own commit message.
**Re-run both before opening**, since they are the load-bearing evidence for section 2:

```bash
cabal --project-dir=<worktree> run benchmark-onchain-scripts --extra-lib-dirs=/usr/local/lib
# and the golden re-dump per the repo's usual invocation
```

If either has drifted, fix the numbers in Part 1 rather than the claim.

## 2.4 Housekeeping

- [ ] `git status` clean — remove or ignore `scratch-goldens/`
- [ ] `97160f8` split into its own PR (`06-…md`); this branch rebased so it carries **only** `c18c525`
- [ ] commit message reworded per §2.2
- [ ] `benchmark-onchain-scripts` and the golden re-dump re-run per §2.3
- [ ] confirm `origin/main` is still `f918ec6` at submission time
- [ ] body = Part 1
