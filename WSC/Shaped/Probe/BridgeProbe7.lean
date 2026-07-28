-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
PROBE (task U1) — the run-form (Tier B) bridge, including at budget 4400 where no
unshaped prep exists.  MEASURED: both `rfl`s succeed, `blaster` verdict `Valid`.
-/
import WSC.Shaped.BaseShaped
import WSC.Shaped.GlobalShapedP1Prep
set_option maxHeartbeats 0
namespace WSC.BridgeProbe7
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

def baseRun (K : Nat) (g s : Credential) (ctx : ScriptContext) :=
  cekExecuteProgram programmableLogicBase.script (baseInputs g s ctx) K

def globalRun (K : Nat) (pcs : CurrencySymbol) (ctx : ScriptContext) :=
  cekExecuteProgram programmableLogicGlobal1600.script (globalInputs1600 pcs ctx) K

/-- run-form exec bridge, base. -/
theorem exec_run_B1
    (gh sh : ScriptHash)
    (txid : ByteString) (idx : Integer) (baseHash : ScriptHash) (lovelace : Integer)
    (w0 w1 : ScriptHash) (a0 a1 : Integer)
    (fee : Integer) (red : Integer) (lo hi : Integer) (tid : ByteString) :
    appliedBaseShaped.exec gh sh txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid
      = baseRun 600 (Credential.ScriptCredential gh) (Credential.ScriptCredential sh)
          (baseShapedCtx txid idx baseHash lovelace w0 w1 a0 a1 fee red lo hi tid) := rfl

/-- run-form exec bridge, SHAPE T1 at budget 4400 (no unshaped prep exists there). -/
theorem exec_run_T1
    (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer) :
    appliedGlobalShapedT1.exec ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee
      = globalRun 4400 ppCS
          (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
            dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
            nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee) := rfl

/-- Optimizer faithfulness at SHAPE T1's 4400-step prep — is this affordable? -/
def optFaithfulT1 : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    (isSuccessful
      (appliedGlobalShapedT1.prop ppCS cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)
    ↔ isSuccessful
      (globalRun 4400 ppCS
        (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
          dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
          nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)))

#blaster (gen-cex: 0) (solve-result: 0) [optFaithfulT1]

end WSC.BridgeProbe7
