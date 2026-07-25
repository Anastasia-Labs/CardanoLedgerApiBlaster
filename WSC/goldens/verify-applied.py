#!/usr/bin/env python3
"""Diff the Data arguments baked into the APPLIED golden flats (as re-serialised
by PCB's CBOR encoder, output of KVerify.lean) against the golden JSONs'
paramsHex + scriptContextHex."""
import json, sys, os, collections

log = sys.argv[1]
gdir = "/home/gumbo/iohk/CardanoLedgerApiBlaster/WSC/goldens"

args = collections.defaultdict(dict)
for line in open(log):
    if line.startswith("ARG "):
        _, name, idx, hexv = line.rstrip("\n").split(" ", 3)
        args[name][int(idx)] = hexv

ok = True
for fn in sorted(os.listdir(gdir)):
    if not fn.endswith(".json"):
        continue
    j = json.load(open(os.path.join(gdir, fn)))
    name = fn[:-5]
    a = args.get(name)
    if a is None:
        print(f"MISSING {name}"); ok = False; continue
    params = j["paramsHex"] if isinstance(j["paramsHex"], list) else [j["paramsHex"]]
    expected = list(params) + [j["scriptContextHex"]]
    got = [a[i] for i in sorted(a)][1:]     # arg 0 = script-internal Force (let-binding)
    head = a[min(a)]
    status = "OK" if got == expected else "MISMATCH"
    if got != expected:
        ok = False
    print(f"{status} {name}: nargs_after_head={len(got)} expected={len(expected)} head0={head}")
    if got != expected:
        for i, (g, e) in enumerate(zip(got, expected)):
            if g != e:
                print(f"   arg{i+1} got={g[:80]}… exp={e[:80]}…")
        if len(got) != len(expected):
            print(f"   arity mismatch: got={len(got)} exp={len(expected)}")
print("ALL-MATCH" if ok else "SOME-MISMATCH")
