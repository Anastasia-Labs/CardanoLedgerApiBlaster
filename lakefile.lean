import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- ══ SUBSTRATE PIN (WSC U5/X4; C3, audit D5; made reproducible by task E3) ══
  --
  -- ┌── READ THIS FIRST IF THE BUILD DOES NOT RESOLVE ────────────────────────┐
  -- │ The `require` below is an ABSOLUTE LOCAL PATH. It is the one line that  │
  -- │ makes this repository non-portable. To build elsewhere, edit BOTH:      │
  -- │   1. this file — the `require PlutusCore from "…"` path, and            │
  -- │   2. `lake-manifest.json` — the PlutusCore entry's `"dir"` field.       │
  -- │ Editing only one leaves lake resolving the manifest's stale `dir`.      │
  -- │ Full third-party recipe: `WSC/REPRODUCE.md`.                            │
  -- └─────────────────────────────────────────────────────────────────────────┘
  --
  -- PlutusCoreBlaster, pinned BY REVISION (not merely by path):
  --
  --   path         /home/gumbo/iohk/PlutusCoreBlaster
  --   branch       cip153-value-builtins     (NOT on the public remote — E3 §2)
  --   commit       9f9ca8c76baf3b5efdb63c33ca0091efa606b474
  --   upstream base a04042c4b7b19c66e7e6fa5bbcc3b1c985894ed0
  --                = `refs/heads/main` of the PUBLIC repo
  --                  https://github.com/input-output-hk/PlutusCoreBlaster
  --   branch's own commits (2, +2832/−6 over the base):
  --     830819b  Add CIP-153 Value builtins
  --              (insertCoin/lookupCoin/unionValue/valueContains/valueData/unValueData)
  --     9f9ca8c  Value: blaster-friendly denotation restatement + algebra lemmas
  --   working tree CLEAN (`git status --porcelain` empty, re-verified 2026-07-25),
  --                so the verified substrate is a real commit and not an
  --                unrecorded working-tree state.
  --   CAVEAT      that checkout is a SHALLOW clone (`.git/shallow` grafts at the
  --                base; only 3 commits are present), so a whole-history
  --                `git bundle` made from it is UNUSABLE even though
  --                `git bundle verify` calls it "a complete history" — E3
  --                measured that failure. Use the incremental bundle below.
  --
  -- REVISION RECORD, in three places, deliberately redundant:
  --   * here;
  --   * `lake-manifest.json` — E3 measured that lake ACCEPTS and PRESERVES
  --     `"rev"` / `"inputRev"` keys on a `"type": "path"` entry across
  --     `lake build`, so the manifest now carries the revision too. (Lake does
  --     not itself check them for a path dep; `lake update` would drop them.)
  --   * `WSC/ARCHITECTURE.md` ADDENDUM E11.
  --
  -- OFFLINE ARTIFACT: `WSC/substrate/pcb-cip153-value-builtins.bundle`
  -- (39,068 bytes, sha256 3d34a23d5e25ac09beddcdf6032ecb3d13c47d064239b09be8040842d1a82789)
  -- carries exactly the two commits above on top of the public base. E3 verified
  -- it reconstructs HEAD 9f9ca8c and tree e75862b26b5055e8cc36ea8cf393054e2417ca62
  -- byte-identically (`diff -r` clean). See `WSC/substrate/README.md`.
  --
  -- WHAT DEPENDS ON IT: that branch carries the CIP-153 Value builtins — flat
  -- decoder tags 94-99 (`PlutusCore/UPLC/FlatEncoding/Basic.lean:305-310`) plus
  -- blaster-friendly Value denotations. Without them
  -- `WSC/flats/programmableLogicGlobal.flat` does not decode at all: against PCB
  -- `main` @ 4ef4860 the same flat fails with "Could not decode program!"
  -- (negative control, `WSC/Prep/Global.lean:10-13`). So EVERY P1/P5/P6 result
  -- "proved against production bytecode" inherits this pin.
  --
  -- RESIDUAL RISK: the bundle removes the "unpushed branch" objection but not the
  -- "single machine" one — the artifact is only as good as its custody. Publish
  -- the branch, then restore a real git pin by replacing the `require` with:
  --   require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "9f9ca8c…"
  --
  -- Cross-references: `WSC/REPRODUCE.md` (third-party recipe, rehearsed end to
  -- end), `WSC/substrate/README.md` (bundle verify/apply),
  -- `WSC/flats/PROVENANCE.md` (bytecode chain), `WSC/ARCHITECTURE.md` E11.
  require PlutusCore from "/home/gumbo/iohk/PlutusCoreBlaster"
  -- Blaster IS pinned by rev in `lake-manifest.json`:
  --   59db213ca6396269d2606b7dd9ac2bc26ae7c4ce
  -- on the PUBLIC repo https://github.com/input-output-hk/Lean-blaster, where
  -- `refs/heads/beta-lambda-cache-optimization` still resolved to exactly that
  -- rev when E3 re-checked it (2026-07-25). Branch names move; the manifest rev
  -- is what is verified.
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "beta-lambda-cache-optimization"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

/-- WSC (Wyoming Stable Token / CIP-113 programmable tokens) containment
proofs: UPLC-level verification of the compiled production validators.
See WSC/ARCHITECTURE.md. -/
lean_lib «WSC» where
  -- root module WSC.lean imports the WSC.* tree
