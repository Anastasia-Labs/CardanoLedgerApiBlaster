# `WSC/substrate/` — the offline record of the PlutusCoreBlaster pin


> **⚠️ UPDATED AT TASK N6 (2026-07-28) — this directory previously did NOT
> reconstruct the substrate.** Two things were missing after wsc-poc PR #112:
>
> 1. **PlutusCoreBlaster moved `9f9ca8c` → `3fdd3fb`** (the CIP-153 `ScaleValue`
>    builtin at flat tag 100, plus `unValueData`/`valueData` cost corrections to
>    plutus 1.63). Carried by the INCREMENTAL bundle
>    `pcb-scalevalue-3fdd3fb.bundle` (14,697 bytes, sha256
>    `0e373d0004275db3e9f80c8e4ef994e5b7955d952ca48048434ebc0a19b7d27c`),
>    which sits on top of `9f9ca8c` and yields tree
>    `1c9d80221bd59fdd21ab132d1fcec086c7bbf3b9`.
> 2. **Blaster is no longer a public git require** — it carries the defect-D6 fix
>    as one commit on top of public `59db213`, and this directory shipped **no
>    artifact for it at all**. Now added:
>    `blaster-d6-dite-4d320dd.bundle` (3,313 bytes, sha256
>    `19e67631d1d5ff30ac0c47377131188031d66c6fa1aebaa37de775dbcb502b8c`),
>    reconstructing HEAD `4d320dd`, tree
>    `9550c96b0dff95096d07d29825a19d885fe7c6cd`; equivalently
>    `patches/0003-Optimize-DITE-re-type-branch-binders-D6.patch` (6,073 bytes,
>    sha256 `1ba2c74cd2a67dc5a07be1f7eb36296ee1688474540e3f370e43f03ab546a374`).
>
> Step-by-step reconstruction for both is in `WSC/REPRODUCE.md` §1 and §1b.
>
> **Verification caveat.** Every bundle here was checked with `git bundle verify`
> against the LOCAL working repository, which is the only check available without
> network access. None has been fetched into a fresh clone of the corresponding
> public remote. The prerequisite commits are public, so it should work; it is
> untested, and that is a real residual risk for anyone reproducing this offline.

> # ⚠️ THIS BUNDLE IS NO LONGER SUFFICIENT (task N6, 2026-07-28)
>
> `pcb-cip153-value-builtins.bundle` reconstructs PCB `cip153-value-builtins` up to
> **`9f9ca8c`**, which is one commit SHORT of the pin the library now needs.
> wsc-poc PR #112 made `programmableSeize` use **`ScaleValue`** (plutus-core flat
> tag **100**), a SEVENTH CIP-153 builtin that `9f9ca8c` does not have. Against a
> checkout reconstructed from that bundle alone,
> `WSC/flats/programmableSeize.flat` fails with `Could not decode program!`, so
> **no P2 result is statable at all**.
>
> **The second artifact in this directory closes the gap:**
>
> | file | 14,697 bytes | sha256 `0e373d0004275db3e9f80c8e4ef994e5b7955d952ca48048434ebc0a19b7d27c` |
> |---|---|---|
> | `pcb-scalevalue-3fdd3fb.bundle` | contains | `3fdd3fb` on `refs/heads/cip153-value-builtins` |
> | | requires | `9f9ca8c` — i.e. apply the FIRST bundle first |
>
> Verified in this task, not asserted: `git bundle verify` says *"is okay"* against
> a checkout at `9f9ca8c`; `git fetch` from it yields `FETCH_HEAD =
> 3fdd3fb5cb259f039b60cc584cd954de18c819dc`; and `git diff` between that commit and
> the canonical `/home/gumbo/iohk/PlutusCoreBlaster` working tree is **empty**
> (`TREES IDENTICAL`).
>
> Recipe: apply `pcb-cip153-value-builtins.bundle` exactly as below, then
> ```
> git fetch <path>/pcb-scalevalue-3fdd3fb.bundle cip153-value-builtins
> git checkout FETCH_HEAD      # 3fdd3fb
> ```
> The commit adds `ScaleValue` (enum entry, arity, flat tag 100, CEK denotation,
> cost arms) **and** fixes `unValueData`/`valueData` cost coefficients that were
> still plutus **1.57** in an otherwise-1.63 table — a bug only the post-#112 seize
> path could expose, because global *references* those builtins but never
> *executes* them on its goldens' paths. After the fix PCB's metered budget
> reproduces the ledger `ExBudget` exactly on all nine accepting goldens (was 7).

---

**Why this directory exists.** The `CardanoLedgerApi` package requires
`PlutusCore` (PlutusCoreBlaster, "PCB") **from an absolute local path**. A lake
`"type": "path"` dependency has no revision field lake fills in, so for most of
this campaign `lake-manifest.json` recorded **no revision at all** for the single
substrate every "proved against production bytecode" result depends on. That was
audit finding **D5**, and it was the campaign's highest operational risk: the
build reproduced on exactly one machine.

This directory is the fix that does not require pushing anything. It carries the
two commits that distinguish the pinned branch from its **public** base, as a git
bundle and as plain patches.

---

## 1. What is pinned

```
repository   PlutusCoreBlaster
branch       cip153-value-builtins        (NOT on the public remote)
commit       9f9ca8c76baf3b5efdb63c33ca0091efa606b474
tree         e75862b26b5055e8cc36ea8cf393054e2417ca62
base         a04042c4b7b19c66e7e6fa5bbcc3b1c985894ed0
             = the public repo's main
             https://github.com/input-output-hk/PlutusCoreBlaster
```

The branch's own two commits, `+2832 / −6` over the base:

| commit | subject |
|---|---|
| `830819b` | Add CIP-153 Value builtins (`insertCoin`, `lookupCoin`, `unionValue`, `valueContains`, `valueData`, `unValueData`) |
| `9f9ca8c` | `Value`: blaster-friendly denotation restatement + algebra lemmas |

> **Where the FIDELITY argument for `830819b` lives: `WSC/CIP153-BUILTINS-REPORT.md`.**
> This directory pins the substrate's *bytes* (§2/§3 below verify the bundle
> reconstructs the exact tree). It does not argue that those bytes are a faithful
> transcription of upstream Plutus. That argument — the `plutus` source citations for
> flat builtin tags 94–99, the six arities, uni tag 13, the full `Value.hs` semantics
> read, the cost-model provenance, and **six named, deliberate deviations from
> `Value.hs`** — is in `WSC/CIP153-BUILTINS-REPORT.md`. It is a raw per-task record,
> not a reviewer document, and it names the branch by its *first* commit (`830819b`)
> rather than the pinned tip (`9f9ca8c`); read it for the fidelity evidence only.
> Cross-reference added at H2, which found it was the one document in `WSC/` that
> nothing else referenced (`AUDIT.md` §12.2).

**What depends on it.** That branch carries flat decoder tags 94–99
(`PlutusCore/UPLC/FlatEncoding/Basic.lean:305-310`) plus their CEK denotations.
Without them the production `programmableLogicGlobal` flat does not decode at all
— which is itself the negative control recorded at `WSC/Prep/Global.lean:10-13`.
So **every P1 / P5 / P6 result in this campaign inherits this pin.**

---

## 2. Files

| file | bytes | sha256 |
|---|---|---|
| `pcb-cip153-value-builtins.bundle` | 39,068 | `3d34a23d5e25ac09beddcdf6032ecb3d13c47d064239b09be8040842d1a82789` |
| `patches/0001-Add-CIP-153-Value-builtins-insertCoin-lookupCoin-uni.patch` | 67,281 | — |
| `patches/0002-Value-blaster-friendly-denotation-restatement-algebr.patch` | 94,093 | — |

The bundle is **incremental**: it contains the two commits and *requires* the base
`a04042c` to already be present. `git bundle verify` says so explicitly.

> **Why incremental and not a whole-history bundle.** The working checkout of PCB
> on the build machine is a **shallow clone** (`.git/shallow` grafts at `a04042c`;
> only 3 commits are present). A whole-history bundle made from a shallow clone is
> **unusable** even though `git bundle verify` will call it "a complete history".
> Task E3 measured that failure; the incremental bundle is the disposition that
> works. Do not "improve" this by regenerating with `--all`.

---

## 3. Apply it

```bash
# 1. obtain the public base
git clone https://github.com/input-output-hk/PlutusCoreBlaster pcb
cd pcb
# The base a04042c is REACHABLE FROM main, so a plain clone always contains it.
# It also happened to be main's tip on 2026-07-26 — do NOT depend on that; test
# for the object, not for HEAD, so this step still passes after main advances:
git cat-file -e a04042c4b7b19c66e7e6fa5bbcc3b1c985894ed0^{commit} && echo "base present"

# 2. verify, then fetch the branch out of the bundle
git bundle verify <CLAB>/WSC/substrate/pcb-cip153-value-builtins.bundle
git fetch <CLAB>/WSC/substrate/pcb-cip153-value-builtins.bundle \
    'refs/heads/cip153-value-builtins:refs/heads/cip153-value-builtins'
git checkout cip153-value-builtins

# 3. confirm you reconstructed the exact substrate
git rev-parse HEAD        # 9f9ca8c76baf3b5efdb63c33ca0091efa606b474
git rev-parse HEAD^{tree} # e75862b26b5055e8cc36ea8cf393054e2417ca62
```

Fallback if the bundle is unavailable: `git am patches/0001-*.patch
patches/0002-*.patch` on top of `a04042c`. The patches carry the same content;
only the commit hashes are not guaranteed to reproduce byte-identically, so
**prefer the bundle** — the bundle is what was verified.

---

## 4. Verified, not asserted

Task E5 re-ran the whole procedure independently, from a clone of the base into a
scratch directory, and compared the result against the build machine's checkout:

```
HEAD after apply : 9f9ca8c76baf3b5efdb63c33ca0091efa606b474
tree after apply : e75862b26b5055e8cc36ea8cf393054e2417ca62
canonical HEAD   : 9f9ca8c76baf3b5efdb63c33ca0091efa606b474
canonical tree   : e75862b26b5055e8cc36ea8cf393054e2417ca62
$ diff -r -x .git -x .lake <canonical PCB> <reconstructed>
DIFF CLEAN
```

The bundle's own sha256 was re-checked at the same time and matches §2.

---

## 5. What this does NOT fix

* **Custody, not publication.** The branch is still not on the public remote. The
  bundle removes the "unpushed branch" objection — the bytes now travel with the
  repository — but it does not remove the "one machine" objection: the artifact is
  only as trustworthy as the repository carrying it. **The real fix is still to
  push the branch and restore a git pin**, which is one line in `lakefile.lean`:

  ```lean
  require PlutusCore from git
    "https://github.com/input-output-hk/PlutusCoreBlaster" @ "9f9ca8c76baf3b5efdb63c33ca0091efa606b474"
  ```

* **The path is still absolute.** `lakefile.lean` and `lake-manifest.json` both
  name `/home/gumbo/iohk/PlutusCoreBlaster`. Building elsewhere means editing
  **both** (`WSC/REPRODUCE.md` §2). Editing only one leaves lake resolving the
  manifest's stale `dir`.

* **Lake does not check the recorded revision.** The `"rev"` / `"inputRev"` keys
  now present on the manifest's PlutusCore entry are *preserved* by `lake build`
  but are not *verified* by it for a path dependency, and `lake update` would drop
  them. They are a record for humans and for `git`, not an enforcement mechanism.
  The enforcement is §3's `git rev-parse` check, run by hand.
