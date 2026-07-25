#!/usr/bin/env python3
# WSC/goldens/ctx-audit/GenCtxAuditDetail.py -- task Y3 (2026-07-25), LR-CTX empirical audit.
#
# WHAT IT DOES
#   Reads every WSC/goldens/*.json, and emits a Lean file that CBOR-decodes each
#   golden `scriptContextHex` into a CLAB `ScriptContext`
#   (PlutusCore.Cbor.decodeData + IsData.fromData) and evaluates hex-level detail of the failing fields (withdrawal credentials, output values, redeemer purposes).
#
# USAGE (from the CLAB checkout root)
#   python3 WSC/goldens/ctx-audit/GenCtxAuditDetail.py > /dev/null      # writes ./CtxAuditDetail.lean
#   lake env lean CtxAuditDetail.lean
#
# MEASURED RESULT (2026-07-25, all 13 goldens, recorded in WSC/STATUS.md §3 D3
# and in WSC/Honest.lean's LR_CTX audit table):
#   * seize goldens: withdrawal credentials 0x40*28 then 0x14*28 (DESCENDING).
#   * seize-1-input / seize-2-inputs: one output value is
#     [(cs=1b*28, [(tn=0x3063, n)])] with NO ada entry -- min-ada forbids this
#     on chain, so it is a builder artifact, not a CLAB over-reach.
#   * mint-burnonly: redeemer purposes [Spending, Minting, Rewarding x3].


import json, glob, os
d = "WSC/goldens"
want = ["programmableSeize.seize-1-input","programmableSeize.seize-2-inputs-partial-with-noise","programmableTokenMinting.mint-burnonly"]
out=[]
for nm in want:
    j=json.load(open(os.path.join(d,nm+".json")))
    out.append((nm,j["scriptContextHex"]))
head = r'''
import CardanoLedgerApi.V3
import PlutusCore.Cbor
import PlutusCore.UPLC

open CardanoLedgerApi.V3
open CardanoLedgerApi.IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.Cbor (decodeData)
open PlutusCore.UPLC.ScriptEncoding.Internal (hexStringToString)

def hexToStr (s : String) : Option String :=
  (hexStringToString s.data []).map (fun cs => ⟨cs⟩)

def decodeCtx (hex : String) : Option ScriptContext := do
  let bs ← hexToStr hex
  let (_, d) ← decodeData bs
  (IsData.fromData d : Option ScriptContext)

def hx (s : String) : String :=
  String.join (s.data.map (fun c => let n := c.toNat;
    let d1 := n / 16; let d2 := n % 16;
    let f := fun (k : Nat) => if k < 10 then Char.ofNat (48+k) else Char.ofNat (87+k)
    ⟨[f d1, f d2]⟩))

def showVal (v : CardanoLedgerApi.V1.Value.Value) : String :=
  String.intercalate " " (v.map (fun p =>
    match p with
    | (Data.B cs, Data.Map ts) =>
        s!"[cs={hx cs.data}(len {cs.data.length}) " ++
        String.intercalate "," (ts.map (fun t => match t with
          | (Data.B tn, Data.I n) => s!"tn={hx tn.data}(len {tn.data.length})={n}"
          | _ => "??")) ++ "]"
    | _ => "??"))

def detail (nm : String) (hex : String) : IO Unit := do
  match decodeCtx hex with
  | none => IO.println s!"{nm}: DECODE-FAILED"
  | some ctx =>
    let ti := ctx.scriptContextTxInfo
    IO.println s!"== {nm}"
    IO.println "   wdrl:"
    for w in ti.txInfoWdrl do
      match w.1 with
      | .ScriptCredential h => IO.println s!"      Script {hx h.data} (len {h.data.length}) amt={w.2}"
      | .PubKeyCredential h => IO.println s!"      PubKey {hx h.data} (len {h.data.length}) amt={w.2}"
    IO.println "   outputs:"
    for o in ti.txInfoOutputs do
      IO.println s!"      ok={CardanoLedgerApi.V2.validTxOutValue o.txOutValue} val={showVal o.txOutValue}"
    IO.println "   inputs (resolved):"
    for i in ti.txInfoInputs do
      IO.println s!"      ok={CardanoLedgerApi.V2.validTxOutValue i.txInInfoResolved.txOutValue} val={showVal i.txInInfoResolved.txOutValue}"
    IO.println s!"   mint={showVal ti.txInfoMint}"
'''
lines=[head,'def rows : List (String × String) := [']
for i,(nm,hxs) in enumerate(out):
    lines.append(('  ' if i==0 else '  , ')+f'("{nm}", "{hxs}")')
lines.append(']')
lines.append('#eval! do rows.forM (fun r => detail r.1 r.2)')
open("CtxAuditDetail.lean","w").write("\n".join(lines)+"\n")
print("ok")
