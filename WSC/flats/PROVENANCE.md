# WSC flat provenance (ADDENDUM E7)

Extraction date: 2026-07-24.
Source repository: `wsc-poc` worktree
`/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d`
at git commit `7ae0024b185cf16f17e38c20c9ee97ae1410c51f`.

Each `.flat` file is the raw `cborHex` string copied verbatim out of the
corresponding TextEnvelope JSON (`"type": "PlutusScriptV3"`). The TextEnvelope
`cborHex` is a CBOR bytestring wrapping the CBOR-wrapped flat-encoded UPLC
program, hence the `double_cbor_hex` decoder in `WSC/Imports.lean`.

| flat | source JSON (relative to worktree root) | sha256 of .flat file |
|---|---|---|
| `programmableLogicBase.flat` | `generated/scripts/unapplied/prod/programmableLogicBase.json` | `1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3` |
| `programmableTokenMinting.flat` | `generated/scripts/unapplied/prod/programmableTokenMinting.json` | `7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048` |
| `programmableSeize.flat` | `generated/scripts/unapplied/prod/programmableSeize.json` | `289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1` |
| `programmableLogicGlobal.flat` | `generated/scripts/unapplied/prod/programmableLogicGlobal.json` | `ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2` |

These are the UNAPPLIED production scripts: every deployment parameter is still
a lambda, and is supplied Lean-side by the `*Inputs` functions in
`WSC/Imports.lean` (parameter evidence cited there per validator).

Note: `programmableLogicGlobal.flat` uses the CIP-153 Value builtins and does
not decode with the current PlutusCoreBlaster flat decoder (builtin tags 94-99
commented out in `FlatEncoding/Basic.lean`); its `#import_uplc` line is kept
commented in `WSC/Imports.lean` until task U5 lands those builtins.
