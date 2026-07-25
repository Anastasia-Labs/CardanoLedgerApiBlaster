#!/usr/bin/env python3
# WSC/goldens/ctx-audit/GenCtxAudit.py -- task Y3 (2026-07-25), LR-CTX empirical audit.
#
# WHAT IT DOES
#   Reads every WSC/goldens/*.json, and emits a Lean file that CBOR-decodes each
#   golden `scriptContextHex` into a CLAB `ScriptContext`
#   (PlutusCore.Cbor.decodeData + IsData.fromData) and evaluates every validTxInfo conjunct separately (one line per golden).
#
# USAGE (from the CLAB checkout root)
#   python3 WSC/goldens/ctx-audit/GenCtxAudit.py > /dev/null      # writes ./CtxAudit.lean
#   lake env lean CtxAudit.lean
#
# MEASURED RESULT (2026-07-25, all 13 goldens, recorded in WSC/STATUS.md §3 D3
# and in WSC/Honest.lean's LR_CTX audit table):
#   * validXContext = FALSE for all 13 -- every golden has txInfoFee = 0
#     (CLAB Contexts.lean:1201). Builder artifact: the goldens are produced by
#     the wsc-poc ScriptContext.Builder, not captured from a chain.
#   * validRedeemerMap = FALSE for the 2 accepting minting goldens (purposes
#     [Spending, Minting, Rewarding x3]) -- the CLAB-vs-ledger ScriptPurpose
#     ordering defect (STATUS.md D1).
#   * validWithdrawals = FALSE for the 3 seize goldens (two script credentials
#     emitted descending) and validOutputs = FALSE for the 2 accepting seize
#     goldens (residual output has no ada entry) -- builder artifacts.


import json, glob, os, sys
d = "WSC/goldens"
out = []
for p in sorted(glob.glob(os.path.join(d, "*.json"))):
    j = json.load(open(p))
    out.append((os.path.basename(p)[:-5], j["validator"], j["accepts"], j["scriptContextHex"]))
lines = []
lines.append('import CardanoLedgerApi.V3')
lines.append('import PlutusCore.Cbor')
lines.append('import PlutusCore.UPLC')
lines.append('')
lines.append('open CardanoLedgerApi.V3')
lines.append('open CardanoLedgerApi.IsData.Class')
lines.append('open PlutusCore.Data (Data)')
lines.append('open PlutusCore.Cbor (decodeData)')
lines.append('open PlutusCore.UPLC.ScriptEncoding.Internal (hexStringToString)')
lines.append('')
lines.append('''
def hexToStr (s : String) : Option String :=
  (hexStringToString s.data []).map (fun cs => ⟨cs⟩)

def decodeCtx (hex : String) : Option ScriptContext := do
  let bs ← hexToStr hex
  let (_, d) ← decodeData bs
  (IsData.fromData d : Option ScriptContext)

structure Row where
  name : String
  validator : String
  accepts : Bool
  hex : String

def b (x : Bool) : String := if x then "T" else "F"

def report (r : Row) : IO Unit := do
  match decodeCtx r.hex with
  | none => IO.println s!"{r.name}: DECODE-FAILED"
  | some ctx =>
    let ti := ctx.scriptContextTxInfo
    let purposeOK :=
      match ctx.scriptContextScriptInfo with
      | .SpendingScript .. => validSpendingContext ctx
      | .MintingScript _   => validMintingContext ctx
      | .RewardingScript _ => validRewardingContext ctx
      | _ => false
    IO.println s!"{r.name} | acc={b r.accepts} | validXContext={b purposeOK} | scriptInfo={b (validScriptInfo ctx)} | ins={b (validInputs ctx)} | refIns={b (validReferenceInputs ctx)} | outs={b (validOutputs ti.txInfoOutputs)} | fee>0={b (decide (ti.txInfoFee > 0))} | mint={b (Contexts.validMintValue ti.txInfoMint)} | wdrl={b (validWithdrawals ti.txInfoWdrl)} | range={b (CardanoLedgerApi.V2.validTxRange ti.txInfoValidRange)} | signers={b (CardanoLedgerApi.V2.validSigners ti.txInfoSignatories)} | rdmrs={b (validRedeemerMap ti.txInfoRedeemers)} | datums={b (CardanoLedgerApi.V2.validDatumMap ti.txInfoData)} | votes={b (validVoterMap ti.txInfoVotes)} | treas={b (validTreasuryAmount ti.txInfoCurrentTreasuryAmount)} | donat={b (validTreasuryDonation ti.txInfoTreasuryDonation)} | balanced={b (isBalanced ctx)} | nIns={ti.txInfoInputs.length} nRef={ti.txInfoReferenceInputs.length} nOut={ti.txInfoOutputs.length} nWdrl={ti.txInfoWdrl.length} nRdmr={ti.txInfoRedeemers.length} nMint={ti.txInfoMint.length}"
''')
lines.append('def rows : List Row := [')
for i, (name, val, acc, hexs) in enumerate(out):
    comma = '' if i == 0 else ', '
    lines.append(f'  {comma}⟨"{name}", "{val}", {"true" if acc else "false"}, "{hexs}"⟩')
lines.append(']')
lines.append('')
lines.append("#eval! do rows.forM report")
open("CtxAudit.lean","w").write("\n".join(lines)+"\n")
print("wrote", len(out), "rows")
