# WSC flat provenance (ADDENDUM E7; RE-BASED on PR #112 by task N1)

Extraction date: **2026-07-28**.
Source repository: `input-output-hk/wsc-poc`.

**Verify against commit `2306678fb03b615d4e58ae207e3eccf9b3676b9b` on `main`.**
That is the durable ref and the one every command in this file uses. It was
verified to BE `origin/main` at extraction time:

```
$ git -C /home/gumbo/iohk/wsc-poc rev-parse origin/main
2306678fb03b615d4e58ae207e3eccf9b3676b9b
$ git -C /home/gumbo/iohk/wsc-poc log --oneline -1 origin/main
2306678 Seize path: per-pair value delta via CIP-153 builtins, witnessed base
        delegation (#112)
```

Unlike the previous export there is no second SHA to disambiguate: the flats
were extracted directly from the squash-merge commit on `main`, with
`git show <ref>:<path>`, so the ref in the table is the ref that was read.

Each `.flat` file is the raw `cborHex` string copied verbatim out of the
corresponding TextEnvelope JSON (`"type": "PlutusScriptV3"`), with **no trailing
newline** — the extraction pipes through
`python3 -c "…sys.stdout.write(json.load(sys.stdin)['cborHex'])"`, which emits
no terminator. That property is load-bearing: the re-verification below hashes
the JSON field and the file and compares, so a stray `\n` would break every row.
Verified at extraction: the last byte of each file is an ASCII hex digit
(`0x31`, `0x64`, `0x39`, `0x39` for base / global / seize / minting).

The TextEnvelope `cborHex` is a CBOR bytestring wrapping the CBOR-wrapped
flat-encoded UPLC program, hence the `double_cbor_hex` decoder used by
`#import_uplc`.

## The four flats at `2306678` (current)

| flat | source JSON (relative to the wsc-poc repo root) | bytes | sha256 of .flat file |
|---|---|---|---|
| `programmableLogicBase.flat` | `generated/scripts/unapplied/prod/programmableLogicBase.json` | 192 | `a9e7364b519a190787dcca47d46e843bf542361403b82885343d796e781ab3b9` |
| `programmableTokenMinting.flat` | `generated/scripts/unapplied/prod/programmableTokenMinting.json` | 2472 | `7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048` |
| `programmableSeize.flat` | `generated/scripts/unapplied/prod/programmableSeize.json` | 2594 | `350b58d7b32266dea2fca61b1189610205260b5c6e040e9c6cc2a0cd8ebb8423` |
| `programmableLogicGlobal.flat` | `generated/scripts/unapplied/prod/programmableLogicGlobal.json` | 5624 | `eed62d595f56c3c69779c363950bc9ae81f57e9fde062b09cff8f40eb4bf5dbf` |

These are the UNAPPLIED production scripts: every deployment parameter is still
a lambda, and is supplied Lean-side by the `*Inputs` functions in `WSC/Prep/*`
(parameter evidence cited there per validator).

## WHAT THIS SUPERSEDES, AND WHY — read before citing any pre-#112 result

This file **supersedes the `f918ec6` (PR #110) export** recorded in the previous
revision. The reason is not a re-export or a compiler bump: **wsc-poc PR #112
("Seize path: per-pair value delta via CIP-153 builtins, witnessed base
delegation", merged as `2306678`) is a SEMANTIC change to three of the four
validators.** Measured, both refs, `sha256` of the `cborHex` field:

| flat | `f918ec6` (PR #110) | `2306678` (PR #112) | |
|---|---|---|---|
| `programmableLogicBase` | `1881821b7a2c…` | `a9e7364b519a…` | **CHANGED** |
| `programmableLogicGlobal` | `ddd6f7df4278…` | `eed62d595f56…` | **CHANGED** |
| `programmableSeize` | `289e9e8d18b8…` | `350b58d7b322…` | **CHANGED** |
| `programmableTokenMinting` | `7274240514ff…` | `7274240514ff…` | **byte-identical** |

Full historical row set at `f918ec6`, kept so a reader can see exactly what
moved (this is the table this file used to publish):

| flat | sha256 at `f918ec6` | bytes |
|---|---|---|
| `programmableLogicBase.flat` | `1881821b7a2c0a59668203c900aa53f5b2bca83d9226d3f83318fbe02525faf3` | 260 |
| `programmableTokenMinting.flat` | `7274240514ff3acdfd867abcd0e29e60f92f8f1a96f2f35bc6bfe59316feb048` | 2472 |
| `programmableSeize.flat` | `289e9e8d18b865aba35d8fcab8fc84d6b1ad2f6092988113a0558df40b1c41a1` | 3932 |
| `programmableLogicGlobal.flat` | `ddd6f7df42789239d8a52a41404268c3b1316e59aee308dec54e201bdeb433a2` | 6880 |

One further historical ref, retained for the audit trail only:
`7ae0024b185cf16f17e38c20c9ee97ae1410c51f` is the PR #110 branch commit the
`f918ec6` export was actually run at (identical tree
`d86b6aa15e89fa989018d08b4e4bcd08ecc66e5f`); it is on no branch and no tag, so
it was never a citable ref and nothing depends on it. See this file's history
for the full argument.

**What changed in the source, per validator** (all citations
`src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs`
at `2306678`; the 812-changed-line diff of that one file is PR #112's payload):

* **base** — rewritten, **and its REDEEMER TYPE IS NEW**. Was: redeemer `()`,
  never read, body scanned the withdrawal map for `globalCred` or `seizeCred`.
  Now: `data BaseSpendRedeemer = SpendViaGlobal Integer | SpendViaSeize Integer`
  (:704-707) with `makeIsDataIndexed [('SpendViaGlobal,0),('SpendViaSeize,1)]`
  (:709); the body (:712-731) reads the redeemer off the `ScriptContext` by
  hand, uses the constructor tag to pick `globalCred` (tag 0) or `seizeCred`,
  and uses the integer field as an index into the credential-sorted withdrawal
  map. Parameters unchanged (`globalCred, seizeCred, ctx`, :711).
  The flat SHRANK, 260 → 192 hex chars.
* **global** — `TransferAct`/`PTransferAct` gained a field: `plgrOwnerWdrlIdxs`
  is now the THIRD of five (:1046; Plutarch `pownerWdrlIdxs` :1148).
  Parameters unchanged. Flat 6880 → 5624.
* **seize** — per-pair value delta now computed with the PV11/CIP-153 `Value`
  builtins (`pvalueEqualsDeltaCurrencySymbol`, :1727-1745) instead of a
  hand-rolled sorted walk. `PSeizeAct`'s field list is unchanged (:1154-1159).
  Flat 3932 → 2594.
* **minting** — untouched by PR #112; `Issuance.hs`, `PTokenDirectory.hs` and
  `ProtocolParams.hs` are byte-identical between the two refs
  (`git diff f918ec6 2306678 -- <path>` empty for each), which is why the flat
  is byte-identical and why `WSC/Redeemer.lean`'s `MintRedeemer` / `RegWitness`
  / `DirectorySetNode` / `GlobalParams` citations still resolve.

Consequence for the library: **every UPLC result about base, global or seize is
about bytecode that no longer exists on `main`.** The classification, module by
module, is `WSC/IMPACT-PR112.md`. The minting results (P4/P4a and their six
shapes) are unaffected and keep running against exactly the same bytes.

## Re-verification

The table is not taken on trust. This is the command a third party runs:

```bash
git clone https://github.com/input-output-hk/wsc-poc /tmp/wsc-poc
W=/tmp/wsc-poc
REF=2306678fb03b615d4e58ae207e3eccf9b3676b9b     # == origin/main at 2026-07-28

sha256sum WSC/flats/*.flat

for n in programmableLogicBase programmableTokenMinting \
         programmableSeize programmableLogicGlobal; do
  git -C $W show \
    $REF:generated/scripts/unapplied/prod/$n.json \
    | python3 -c "import sys,json;sys.stdout.write(json.load(sys.stdin)['cborHex'])" \
    | sha256sum
done
```

Every hash printed must appear in the "four flats at `2306678`" table — note the
loop prints in the order base, minting, seize, global, while
`sha256sum WSC/flats/*.flat` prints in filename order. Substituting
`REF=f918ec6dcef4398952febe11e84fda089c064374` reproduces the historical table
instead, and that is how the "CHANGED / byte-identical" column above was
measured (2026-07-28, 4/4 rows on both refs).

So "proved against production bytecode" is machine-verified rather than
asserted: each `.flat` is byte-identical to the `cborHex` string of the named
**unapplied** production TextEnvelope JSON at the recorded commit. "Unapplied"
is confirmed by the same check — every deployment parameter is still a lambda
and is supplied Lean-side, so no theorem can quietly be about a partially
applied term.

## The substrate pin, and what the new flats do to it — MEASURED, 2026-07-28

The decode depends on an unpushed local branch. `lakefile.lean` requires
PlutusCoreBlaster from the absolute local path
`/home/gumbo/iohk/PlutusCoreBlaster`, and `lake-manifest.json` records
`"type": "path"` with **no revision at all** — `lake` cannot express one for a
path dependency. The substrate actually used:

| | |
|---|---|
| path | `/home/gumbo/iohk/PlutusCoreBlaster` |
| branch | `cip153-value-builtins` (**unpushed**) |
| commit | `9f9ca8c76baf3b5efdb63c33ca0091efa606b474` |
| working tree | clean at the last check (2026-07-25) |

**Against that pin, the new flats behave as follows.** Each row was measured by
`lake build` in the N1 workspace copy at this revision, not inferred:

| flat | `#import_uplc` decode | `#prep_uplc` |
|---|---|---|
| `programmableLogicBase` | ✅ `Successfully decoded double CBOR hex …` | ✅ `appliedBase` at 600 — `WSC.Prep.Base` builds (22.8 s cold) |
| `programmableLogicGlobal` | ✅ `Successfully decoded …` | ✅ at 600 (`WSC.Prep.Global`, 2.5 s) / ❌ at 1600 — see below |
| `programmableSeize` | ❌ **`Decoding error in 'WSC/flats/programmableSeize.flat': Could not decode program!`** | n/a — `unknown constant 'programmableSeize'` |
| `programmableTokenMinting` | ✅ (bytes unchanged) | ✅ (unchanged) |

Two NEW blockers, both in the substrate rather than in this library, both handed
to the reprove units and recorded in `WSC/IMPACT-PR112.md`:

* **The new seize flat does not decode at all.** PR #112's seize path calls
  `pscaleValue`, which is `punsafeBuiltin PLC.ScaleValue`
  (`Plutarch/Builtin/Value.hs:164-167` in the pinned plutarch source), i.e. a
  PV11 `Value` builtin that is **not in PlutusCoreBlaster's `builtinTable`** —
  that table stops at `(99, .UnValueData)`
  (`PlutusCore/UPLC/FlatEncoding/Basic.lean:296-311`). Adding `ScaleValue`, with
  its flat tag read off plutus-core's `instance Flat DefaultFun` and NOT
  guessed, plus a CEK denotation for it, is a precondition for ANY seize result
  at `2306678`.
* **The new global flat decodes but does not prep at 1600.**
  `WSC/Prep/Global1600.lean` runs 8 m 9 s and then fails in the KERNEL, twice,
  with `(kernel) application type mismatch` on a `Blaster.dite'` whose
  discriminant is `Bool.true = eqDataMap …` while the branch supplied has type
  `Bool.false = eqDataMap … → State` — a polarity mismatch produced by Blaster's
  elaboration-time optimizer on the new bytecode. The 600 prep is unaffected.
  This is a Blaster/PCB defect, not a WSC one, and it blocks every global shaped
  prep, since all of `WSC/Shaped/Global*` import `WSC.Prep.Global1600`.

Negative control, still on the record: against PCB `main` @ `4ef4860` the global
flat fails with *"Decoding error … Could not decode program!"*
(`WSC/Prep/Global.lean:10-13`). So **every** P1/P5/P6 "proved against production
bytecode" claim inherits this pin; publish the branch before quoting the
campaign outside it.
