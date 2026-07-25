import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"
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
