import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- ══ SUBSTRATE PIN (WSC U5/X4; auditable record added by task C3, audit D5) ══
  --
  -- PlutusCoreBlaster is required from an ABSOLUTE LOCAL PATH, so `lake` records
  -- `"type": "path"` and **NO REVISION AT ALL** for it in `lake-manifest.json`
  -- (contrast `Blaster`, which is a git require and IS pinned there). A path
  -- dependency has no revision field lake can fill in, so the pin is recorded
  -- HERE instead, and it is the only machine-readable record of it:
  --
  --   path         /home/gumbo/iohk/PlutusCoreBlaster
  --   branch       cip153-value-builtins        (UNPUSHED — see the risk note)
  --   commit       9f9ca8c76baf3b5efdb63c33ca0091efa606b474
  --   working tree CLEAN (`git status --porcelain` empty, verified 2026-07-25),
  --                so the verified substrate is a real commit and not an
  --                unrecorded working-tree state.
  --
  -- WHAT DEPENDS ON IT: that branch carries the CIP-153 Value builtins — flat
  -- decoder tags 94-99 (`PlutusCore/UPLC/FlatEncoding/Basic.lean:305-310`) plus
  -- blaster-friendly Value denotations. Without them
  -- `WSC/flats/programmableLogicGlobal.flat` does not decode at all: against PCB
  -- `main` @ 4ef4860 the same flat fails with "Could not decode program!"
  -- (negative control, `WSC/Prep/Global.lean:10-13`). So EVERY P1/P5/P6 result
  -- "proved against production bytecode" inherits this pin.
  --
  -- RISK: highest operational risk in the repository — this build reproduces on
  -- no other machine until the branch is pushed. Publish it, then restore a git
  -- pin by reverting the `require` below to:
  --   require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "<rev>"
  --
  -- Cross-references: `WSC/flats/PROVENANCE.md` (same table, with the decode
  -- evidence) and `WSC/ARCHITECTURE.md` ADDENDUM E11 "Substrate pins" — the
  -- ARCHITECTURE.md copy is NOT owned by task C3 and is reported to its owner
  -- for the same commit/branch/clean-tree update.
  require PlutusCore from "/home/gumbo/iohk/PlutusCoreBlaster"
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
