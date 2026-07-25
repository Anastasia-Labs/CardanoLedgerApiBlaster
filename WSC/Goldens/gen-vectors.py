#!/usr/bin/env python3
"""Generate WSC/Goldens/{Vectors,Terms,TermsCheck}.lean from the 13 golden JSONs.

The golden JSONs are the ground truth (provenance: WSC/goldens/MANIFEST.md).
Three generated modules come out of them:

* `Vectors.lean` — the raw `serialiseData` hexes as Lean string literals, so the
  Lean side never does file IO at elaboration time.  This is what
  `WSC/Goldens/Decode.lean` feeds through PlutusCoreBlaster's CBOR decoder.

* `Terms.lean` — the same values as `PlutusCore.Data` LITERALS.  Needed because
  Blaster's `normConst` cannot normalise a `partial def`, and both PCB's hex
  decoder (`hexStringToString`) and its CBOR decoder (`decodeDataLoop`) are
  `partial` — so `by blaster` on a goal mentioning `ctxOfHex …` fails with
  "normConst: partial function not supported".  The literals are produced by the
  independent CBOR decoder in this script, and every one of them is checked
  against PCB's decoder by a `native_decide` theorem in
  `WSC/Goldens/TermsCheck.lean` (`dataOfHex hex = some <literal>`), so the
  Python decoder is VERIFIED, not trusted.

* `TermsCheck.lean` — that gate, also generated here so one command regenerates
  everything.

Regenerate with

    python3 WSC/Goldens/gen-vectors.py            # from the repo root
    python3 WSC/Goldens/gen-vectors.py --check    # verify committed == generated

Task Y4 step 1.  Author: Philip DiSarro.
"""
import argparse
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))          # .../CardanoLedgerApiBlaster
GOLDENS = os.path.join(REPO, "WSC", "goldens")
OUT = os.path.join(HERE, "Vectors.lean")
OUT_TERMS = os.path.join(HERE, "Terms.lean")
OUT_CHECK = os.path.join(HERE, "TermsCheck.lean")

HEX_RE = re.compile(r"\A[0-9a-f]*\Z")


# ---------------------------------------------------------------------------
# A minimal, independent CBOR → Plutus `Data` decoder.
#
# Follows the Plutus `Data` CBOR profile (plutus-core Codec/CBOR/Extras.hs and
# PlutusCoreBlaster PlutusCore/Cbor/Basic.lean):
#   major 0/1                  -> I
#   major 2 (def or indef)     -> B   (indefinite = 64-byte chunking)
#   major 4 (def or indef)     -> List
#   major 5 (def)              -> Map
#   tag 121..127 / 1280..1400  -> Constr (compact forms), followed by an array
#   tag 102                    -> Constr (general form: array(2) [idx, fields])
#   tag 2 / 3                  -> big positive / negative integer
# Every literal produced from this decoder is cross-checked against PCB's own
# decoder by a native_decide theorem, so a bug here is caught, not shipped.
# ---------------------------------------------------------------------------

class DataI:
    def __init__(self, n): self.n = n
class DataB:
    def __init__(self, bs): self.bs = bs
class DataList:
    def __init__(self, xs): self.xs = xs
class DataMap:
    def __init__(self, kvs): self.kvs = kvs
class DataConstr:
    def __init__(self, tag, fields): self.tag, self.fields = tag, fields


INDEF = object()


def _head(b, i):
    """Decode a CBOR head at offset i -> (major, value_or_INDEF, next_offset)."""
    x = b[i]
    mt, ai = x >> 5, x & 31
    i += 1
    if ai < 24:
        return mt, ai, i
    if ai == 24:
        return mt, b[i], i + 1
    if ai == 25:
        return mt, int.from_bytes(b[i:i + 2], "big"), i + 2
    if ai == 26:
        return mt, int.from_bytes(b[i:i + 4], "big"), i + 4
    if ai == 27:
        return mt, int.from_bytes(b[i:i + 8], "big"), i + 8
    if ai == 31:
        return mt, INDEF, i
    raise ValueError(f"bad additional info {ai} at offset {i - 1}")


def _bytes(b, i):
    mt, n, i = _head(b, i)
    assert mt == 2, f"expected bytestring, got major {mt}"
    if n is INDEF:
        out = b""
        while b[i] != 0xFF:
            mt2, n2, i = _head(b, i)
            assert mt2 == 2 and n2 is not INDEF
            out += b[i:i + n2]
            i += n2
        return out, i + 1
    return b[i:i + n], i + n


def _array(b, i, decode):
    mt, n, i = _head(b, i)
    assert mt == 4, f"expected array, got major {mt}"
    xs = []
    if n is INDEF:
        while b[i] != 0xFF:
            x, i = decode(b, i)
            xs.append(x)
        return xs, i + 1
    for _ in range(n):
        x, i = decode(b, i)
        xs.append(x)
    return xs, i


def decode_data(b, i=0):
    mt, n, j = _head(b, i)
    if mt == 0:
        return DataI(n), j
    if mt == 1:
        return DataI(-1 - n), j
    if mt == 2:
        bs, j = _bytes(b, i)
        return DataB(bs), j
    if mt == 4:
        xs, j = _array(b, i, decode_data)
        return DataList(xs), j
    if mt == 5:
        assert n is not INDEF, "indefinite maps are not part of the Data profile"
        kvs = []
        for _ in range(n):
            k, j = decode_data(b, j)
            v, j = decode_data(b, j)
            kvs.append((k, v))
        return DataMap(kvs), j
    if mt == 6:
        if n == 2 or n == 3:                       # bignum
            bs, j = _bytes(b, j)
            m = int.from_bytes(bs, "big")
            return DataI(m if n == 2 else -1 - m), j
        if n == 102:                               # general Constr form
            mt2, cnt, j = _head(b, j)
            assert mt2 == 4 and cnt == 2
            mt3, idx, j = _head(b, j)
            assert mt3 == 0
            fields, j = _array(b, j, decode_data)
            return DataConstr(idx, fields), j
        if 121 <= n <= 127:
            tag = n - 121
        elif 1280 <= n <= 1400:
            tag = (n - 1280) + 7
        else:
            raise ValueError(f"unexpected CBOR tag {n}")
        fields, j = _array(b, j, decode_data)
        return DataConstr(tag, fields), j
    raise ValueError(f"unexpected major type {mt}")


def data_of_hex(h: str):
    b = bytes.fromhex(h)
    d, j = decode_data(b, 0)
    if j != len(b):
        raise ValueError(f"trailing bytes after Data ({j} of {len(b)} consumed)")
    return d


def lean_bytes(bs: bytes) -> str:
    """Lean string literal whose Chars are exactly these bytes."""
    out = []
    for x in bs:
        c = chr(x)
        if c == "\\":
            out.append("\\\\")
        elif c == '"':
            out.append('\\"')
        elif 0x20 <= x < 0x7F:
            out.append(c)
        else:
            out.append("\\x%02x" % x)
    return '"' + "".join(out) + '"'


def lean_data(d, indent: int = 0) -> str:
    pad = " " * indent
    if isinstance(d, DataI):
        return f"Data.I ({d.n})" if d.n < 0 else f"Data.I {d.n}"
    if isinstance(d, DataB):
        return f"Data.B (ByteString.mk {lean_bytes(d.bs)})"
    if isinstance(d, DataList):
        if not d.xs:
            return "Data.List []"
        inner = ("\n" + pad + ", ").join(lean_data(x, indent + 2) for x in d.xs)
        return "Data.List\n" + pad + "[ " + inner + "\n" + pad + "]"
    if isinstance(d, DataMap):
        if not d.kvs:
            return "Data.Map []"
        parts = [f"({lean_data(k, indent + 3)}, {lean_data(v, indent + 3)})"
                 for k, v in d.kvs]
        inner = ("\n" + pad + ", ").join(parts)
        return "Data.Map\n" + pad + "[ " + inner + "\n" + pad + "]"
    if isinstance(d, DataConstr):
        if not d.fields:
            return f"Data.Constr {d.tag} []"
        inner = ("\n" + pad + ", ").join(lean_data(x, indent + 2) for x in d.fields)
        return f"Data.Constr {d.tag}\n" + pad + "[ " + inner + "\n" + pad + "]"
    raise TypeError(type(d))


def lean_ident(validator: str, scenario: str) -> str:
    """Stable Lean identifier for a golden: <validator>_<scenario with - -> _>."""
    return validator + "_" + scenario.replace("-", "_")


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_opt_nat(n) -> str:
    return "none" if n is None else f"(some {n})"


def render(vectors) -> str:
    L = []
    L.append("/-")
    L.append("WSC/Goldens/Vectors.lean — GENERATED FILE, DO NOT EDIT BY HAND.")
    L.append("")
    L.append("Generated by `WSC/Goldens/gen-vectors.py` from the 13 golden JSONs in")
    L.append("`WSC/goldens/*.json` (task Y4 step 1).  Regenerate with")
    L.append("")
    L.append("    python3 WSC/Goldens/gen-vectors.py")
    L.append("")
    L.append("and check a committed copy against the JSONs with `--check`.")
    L.append("")
    L.append("Every hex field is `serialiseData` output produced by the off-chain Haskell")
    L.append("golden driver — i.e. exactly the bytes the ledger/CEK sees.  Provenance,")
    L.append("verification method and the per-golden scenario notes live in")
    L.append("`WSC/goldens/MANIFEST.md`; measured CEK step counts in")
    L.append("`WSC/goldens/K-MEASUREMENTS.md`.")
    L.append("-/")
    L.append("")
    L.append("namespace WSC.Goldens")
    L.append("")
    L.append("/-- One golden vector: a concrete (validator, params, redeemer,")
    L.append("ScriptContext) tuple whose accept/reject outcome was verified by running the")
    L.append("actual production-exported script at PV11 (`WSC/goldens/MANIFEST.md`).")
    L.append("")
    L.append("`paramsHex` is in application order; `redeemerHex` duplicates the")
    L.append("`scriptContextRedeemer` field inside `scriptContextHex` (exposed separately")
    L.append("for the ADDENDUM E8 round-trip gates).  `exBudgetCpu`/`exBudgetMem` are the")
    L.append("ledger's counting-evaluation figures and are `none` for rejecting goldens. -/")
    L.append("structure Vector where")
    L.append("  validator : String")
    L.append("  scenario : String")
    L.append("  accepts : Bool")
    L.append("  paramsHex : List String")
    L.append("  redeemerHex : String")
    L.append("  scriptContextHex : String")
    L.append("  exBudgetCpu : Option Nat")
    L.append("  exBudgetMem : Option Nat")
    L.append("  sourceTest : String")
    L.append("deriving Repr")
    L.append("")
    names = []
    for v in vectors:
        name = lean_ident(v["validator"], v["scenario"])
        names.append(name)
        L.append(f"/-- Golden `{v['validator']}.{v['scenario']}`"
                 f" (accepts: {str(v['accepts']).lower()}). -/")
        L.append(f"def {name} : Vector :=")
        L.append("  { validator := " + lean_str(v["validator"]))
        L.append("  , scenario := " + lean_str(v["scenario"]))
        L.append("  , accepts := " + ("true" if v["accepts"] else "false"))
        L.append("  , paramsHex :=")
        if v["paramsHex"]:
            for i, p in enumerate(v["paramsHex"]):
                L.append(("      [ " if i == 0 else "      , ") + lean_str(p))
            L.append("      ]")
        else:
            L.append("      []")
        L.append("  , redeemerHex :=")
        L.append("      " + lean_str(v["redeemerHex"]))
        L.append("  , scriptContextHex :=")
        L.append("      " + lean_str(v["scriptContextHex"]))
        L.append("  , exBudgetCpu := " + lean_opt_nat(v["exBudgetCpu"]))
        L.append("  , exBudgetMem := " + lean_opt_nat(v["exBudgetMem"]))
        L.append("  , sourceTest :=")
        L.append("      " + lean_str(v["sourceTest"]))
        L.append("  }")
        L.append("")
    L.append("/-- All 13 goldens, in `WSC/goldens/*.json` filename order. -/")
    L.append("def all : List Vector :=")
    for i, n in enumerate(names):
        L.append(("  [ " if i == 0 else "  , ") + n)
    L.append("  ]")
    L.append("")
    L.append("end WSC.Goldens")
    return "\n".join(L) + "\n"


def render_terms(vectors) -> str:
    L = []
    L.append("/-")
    L.append("WSC/Goldens/Terms.lean — GENERATED FILE, DO NOT EDIT BY HAND.")
    L.append("")
    L.append("The 13 goldens' `serialiseData` payloads as `PlutusCore.Data` LITERALS,")
    L.append("generated by `WSC/Goldens/gen-vectors.py` from `WSC/goldens/*.json`.")
    L.append("")
    L.append("WHY A SECOND REPRESENTATION.  `WSC/Goldens/Vectors.lean` carries the same")
    L.append("values as hex, and `WSC/Goldens/Decode.lean` decodes them with")
    L.append("PlutusCoreBlaster's own CBOR decoder — that is the pipeline the LR-CTX audit")
    L.append("uses, and it is the one whose fidelity is checked byte-for-byte.  But Blaster")
    L.append("cannot see through it: both PCB's hex decoder (`hexStringToString`) and its")
    L.append("CBOR decoder (`decodeDataLoop`) are `partial def`s, and `by blaster` on a goal")
    L.append("mentioning them dies with")
    L.append("")
    L.append("    normConst: partial function not supported")
    L.append("      PlutusCore.UPLC.ScriptEncoding.Internal.hexStringToString !!!")
    L.append("")
    L.append("so the real-suite positive witness (`WSC/Goldens/Witnesses.lean`, Y4 RESULT B)")
    L.append("needs the golden as a literal instead.")
    L.append("")
    L.append("THESE LITERALS ARE CHECKED, NOT TRUSTED.  They come from an independent CBOR")
    L.append("decoder written in the generator; `WSC/Goldens/TermsCheck.lean` proves")
    L.append("`dataOfHex <hex> = some <literal>` for all 45 payloads (13 contexts, 13")
    L.append("redeemers, 19 script parameters) by `native_decide`, i.e. against PCB's")
    L.append("decoder.  A")
    L.append("mistake in the generator is therefore a build failure, not a silent")
    L.append("substitution of a different transaction.")
    L.append("-/")
    L.append("import PlutusCore")
    L.append("")
    L.append("namespace WSC.Goldens.Terms")
    L.append("")
    L.append("open PlutusCore.Data (Data)")
    L.append("open PlutusCore.ByteString (ByteString)")
    L.append("")
    for v in vectors:
        name = lean_ident(v["validator"], v["scenario"])
        L.append(f"/-! ### `{v['validator']}.{v['scenario']}` -/")
        L.append("")
        L.append(f"def {name}_ctx : Data :=")
        L.append("  " + lean_data(data_of_hex(v["scriptContextHex"]), 2))
        L.append("")
        L.append(f"def {name}_redeemer : Data :=")
        L.append("  " + lean_data(data_of_hex(v["redeemerHex"]), 2))
        L.append("")
        L.append(f"def {name}_params : List Data :=")
        if v["paramsHex"]:
            for i, p in enumerate(v["paramsHex"]):
                L.append(("  [ " if i == 0 else "  , ") + lean_data(data_of_hex(p), 4))
            L.append("  ]")
        else:
            L.append("  []")
        L.append("")
    L.append("end WSC.Goldens.Terms")
    return "\n".join(L) + "\n"


def render_terms_check(vectors) -> str:
    nparams = sum(len(v["paramsHex"]) for v in vectors)
    L = []
    L.append("/-")
    L.append("WSC/Goldens/TermsCheck.lean — GENERATED FILE, DO NOT EDIT BY HAND.")
    L.append("")
    L.append("The gate that makes `WSC/Goldens/Terms.lean` trustworthy (task Y4 step 1).")
    L.append("Generated by `WSC/Goldens/gen-vectors.py` alongside `Vectors.lean` and")
    L.append("`Terms.lean`.")
    L.append("")
    L.append("`Terms.lean` holds the goldens as `Data` LITERALS, produced by the CBOR decoder")
    L.append("inside the generator (needed because Blaster cannot normalise PCB's `partial`")
    L.append("hex/CBOR decoders — see the header of `Terms.lean`).  This module proves, for")
    L.append(f"every one of the {len(vectors)} contexts, {len(vectors)} redeemers and {nparams} script")
    L.append("parameters, that the literal is EXACTLY what PlutusCoreBlaster's own CBOR")
    L.append("decoder produces from the golden hex:")
    L.append("")
    L.append("    dataOfHex <golden hex> = some <generated literal>")
    L.append("")
    L.append(f"All {2 * len(vectors) + nparams} payload equalities are discharged by `native_decide`"
             " (kernel")
    L.append("`decide` is not an option: `decodeDataLoop` is `partial`, so it has no equational")
    L.append("lemmas).  Two independent decoders — PCB's Lean one and the generator's Python")
    L.append("one — agreeing on every payload is what turns the literals from an assumption")
    L.append("into a checked fact.  If the generator ever drifts, this module stops building.")
    L.append("-/")
    L.append("import WSC.Goldens.Decode")
    L.append("import WSC.Goldens.Terms")
    L.append("")
    L.append("namespace WSC.Goldens.TermsCheck")
    L.append("")
    L.append("open PlutusCore.Data (Data)")
    L.append("")
    L.append("/-! ## Per-golden literal-vs-PCB-decoder equalities -/")
    L.append("")
    for v in vectors:
        n = lean_ident(v["validator"], v["scenario"])
        L.append(f"/-- `{v['validator']}.{v['scenario']}`: context, redeemer"
                 f" and {len(v['paramsHex'])} script parameter(s). -/")
        L.append(f"theorem lit_{n} :")
        L.append(f"    dataOfHex {n}.scriptContextHex = some Terms.{n}_ctx ∧")
        L.append(f"    dataOfHex {n}.redeemerHex = some Terms.{n}_redeemer ∧")
        L.append(f"    {n}.paramsHex.filterMap dataOfHex = Terms.{n}_params ∧")
        L.append(f"    {n}.paramsHex.length = Terms.{n}_params.length := by")
        L.append("  native_decide")
        L.append("")
    L.append("/-! ## Aggregate")
    L.append("")
    L.append("Every golden's three payload groups decode to the generated literals. -/")
    L.append("def allLiteralsAgree : Bool :=")
    conj = []
    for v in vectors:
        n = lean_ident(v["validator"], v["scenario"])
        conj.append(f"  (dataOfHex {n}.scriptContextHex == some Terms.{n}_ctx &&\n"
                    f"   dataOfHex {n}.redeemerHex == some Terms.{n}_redeemer &&\n"
                    f"   {n}.paramsHex.filterMap dataOfHex == Terms.{n}_params &&\n"
                    f"   {n}.paramsHex.length == Terms.{n}_params.length)")
    L.append(" &&\n".join(conj))
    L.append("")
    L.append("theorem allLiteralsAgree_true : allLiteralsAgree = true := by native_decide")
    L.append("")
    L.append("end WSC.Goldens.TermsCheck")
    return "\n".join(L) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="do not write; exit 1 if the committed file differs")
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(GOLDENS, "*.json")))
    if len(files) != 13:
        print(f"FATAL: expected 13 golden JSONs in {GOLDENS}, found {len(files)}",
              file=sys.stderr)
        return 2
    vectors = []
    for f in files:
        with open(f) as fh:
            v = json.load(fh)
        for k in ("validator", "scenario", "accepts", "paramsHex", "redeemerHex",
                  "scriptContextHex", "exBudgetCpu", "exBudgetMem", "sourceTest"):
            if k not in v:
                print(f"FATAL: {f} is missing key {k}", file=sys.stderr)
                return 2
        # sanity: hex fields must be lowercase hex of even length
        for h in list(v["paramsHex"]) + [v["redeemerHex"], v["scriptContextHex"]]:
            if not HEX_RE.match(h) or len(h) % 2 != 0:
                print(f"FATAL: {f} has a non-hex/odd-length field: {h[:40]}…",
                      file=sys.stderr)
                return 2
        # the JSON filename must equal <validator>.<scenario>
        stem = os.path.basename(f)[:-len(".json")]
        if stem != f"{v['validator']}.{v['scenario']}":
            print(f"FATAL: {f} filename does not match validator.scenario", file=sys.stderr)
            return 2
        vectors.append(v)

    text = render(vectors)
    terms = render_terms(vectors)
    outputs = [(OUT, text), (OUT_TERMS, terms), (OUT_CHECK, render_terms_check(vectors))]
    if args.check:
        rc = 0
        for path, want in outputs:
            base = os.path.basename(path)
            if not os.path.exists(path):
                print(f"CHECK FAILED: {base} does not exist", file=sys.stderr)
                rc = 1
                continue
            with open(path) as fh:
                got = fh.read()
            if got != want:
                print(f"CHECK FAILED: {base} differs from the JSONs", file=sys.stderr)
                rc = 1
            else:
                print(f"CHECK OK: {base} matches all {len(vectors)} golden JSONs")
        return rc
    for path, want in outputs:
        with open(path, "w") as fh:
            fh.write(want)
        print(f"wrote {path} ({len(vectors)} vectors, {len(want)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
