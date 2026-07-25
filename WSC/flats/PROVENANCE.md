# WSC flat provenance (ADDENDUM E7)

Extraction date: 2026-07-24.
Source repository: `wsc-poc` worktree
`/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d`
at git commit `7ae0024b185cf16f17e38c20c9ee97ae1410c51f`.

Each `.flat` file is the raw `cborHex` string copied verbatim out of the
corresponding TextEnvelope JSON (`"type": "PlutusScriptV3"`). The TextEnvelope
`cborHex` is a CBOR bytestring wrapping the CBOR-wrapped flat-encoded UPLC
program, hence the `double_cbor_hex` decoder used by `#import_uplc`.

| flat | source JSON (relative to worktree root) | sha256 of .flat file |
|---|---|---|
| `programmableLogicBase.flat` | `generated/scripts/unapplied/prod/programmableLogicBase.json` | `1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3` |
| `programmableTokenMinting.flat` | `generated/scripts/unapplied/prod/programmableTokenMinting.json` | `7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048` |
| `programmableSeize.flat` | `generated/scripts/unapplied/prod/programmableSeize.json` | `289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1` |
| `programmableLogicGlobal.flat` | `generated/scripts/unapplied/prod/programmableLogicGlobal.json` | `ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2` |

These are the UNAPPLIED production scripts: every deployment parameter is still
a lambda, and is supplied Lean-side by the `*Inputs` functions in
`WSC/Imports.lean` (parameter evidence cited there per validator).

## Re-verification (task C3, 2026-07-25) — both halves, independently

The table is not taken on trust. Both columns were re-derived from scratch at
this revision and **all four match on both counts, 4/4**:

```bash
sha256sum WSC/flats/*.flat

W=/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d
for n in programmableLogicBase programmableTokenMinting \
         programmableSeize programmableLogicGlobal; do
  git -C $W show \
    7ae0024b185cf16f17e38c20c9ee97ae1410c51f:generated/scripts/unapplied/prod/$n.json \
    | python3 -c "import sys,json;sys.stdout.write(json.load(sys.stdin)['cborHex'])" \
    | sha256sum
done
```

So "proved against production bytecode" is machine-verified rather than
asserted: each `.flat` is byte-identical to the `cborHex` string of the named
**unapplied** production TextEnvelope JSON at the recorded commit. "Unapplied"
is confirmed by the same check — every deployment parameter is still a lambda
and is supplied Lean-side, so no theorem can quietly be about a partially
applied term.

## Where the imports live, and the state of the CIP-153 decode

**CORRECTION (task C3, 2026-07-25 — audit finding F14).** This file previously
closed with:

> *"Note: `programmableLogicGlobal.flat` uses the CIP-153 Value builtins and does
> not decode with the current PlutusCoreBlaster flat decoder (builtin tags 94-99
> commented out in `FlatEncoding/Basic.lean`); its `#import_uplc` line is kept
> commented in `WSC/Imports.lean` until task U5 lands those builtins."*

**Every clause of that note is false at this revision.** Task U5 landed. Measured
here, not inferred:

* The import is **live and uncommented**, at `WSC/Prep/Global.lean:46`
  (`programmableLogicGlobal`) and `WSC/Prep/Global1600.lean:66`
  (`programmableLogicGlobal1600`). `grep` finds **no** commented-out
  `#import_uplc` anywhere under `WSC/`.
* It **does** decode. `WSC/Prep/Global.lean`'s decode gate records the importer's
  own `Successfully decoded double CBOR hex '…programmableLogicGlobal.flat'`, a
  3,444-node program with 282 builtin occurrences of which **46 are CIP-153**
  (`InsertCoin` 4, `LookupCoin` 0, `UnionValue` 14, `ValueContains` 2,
  `ValueData` 4, `UnValueData` 22) — the new tags are genuinely consumed, so the
  real production transfer validator runs in the Lean CEK. P1, P5 and P6 are all
  stated against it.
* Builtin tags **94-99 are present, not commented out**, at
  `PlutusCore/UPLC/FlatEncoding/Basic.lean:305-310` in the pinned
  PlutusCoreBlaster (`InsertCoin`, `LookupCoin`, `UnionValue`, `ValueContains`,
  `ValueData`, `UnValueData`).
* The imports were never in `WSC/Imports.lean` in the first place — that module
  says so itself at its line 6: *"The actual `#import_uplc` / `#prep_uplc`
  commands live in one module per …"*, i.e. under `WSC/Prep/`.

**What IS true, and is the operational risk to carry forward (audit D5).** The
decode depends on an unpushed local branch. `lakefile.lean` requires
PlutusCoreBlaster from the absolute local path
`/home/gumbo/iohk/PlutusCoreBlaster`, and `lake-manifest.json` records
`"type": "path"` with **no revision at all** — `lake` cannot express one for a
path dependency. The substrate actually used, recorded here and in
`lakefile.lean`'s comment so the pin is auditable anyway:

| | |
|---|---|
| path | `/home/gumbo/iohk/PlutusCoreBlaster` |
| branch | `cip153-value-builtins` (**unpushed**) |
| commit | `9f9ca8c76baf3b5efdb63c33ca0091efa606b474` |
| working tree | **clean** — `git status --porcelain` empty, verified 2026-07-25, so the verified substrate is a real commit and not an unrecorded working-tree state |

Negative control, on the record: against PCB `main` @ `4ef4860` the same flat
fails with *"Decoding error … Could not decode program!"*
(`WSC/Prep/Global.lean:10-13`). So **every** P1/P5/P6 "proved against production
bytecode" claim inherits this pin. It is the highest operational risk in the
repository; publish the branch before quoting the campaign outside it.
