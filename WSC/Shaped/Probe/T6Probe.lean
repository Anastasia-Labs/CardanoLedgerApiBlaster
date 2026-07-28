-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/Probe/T6Probe.lean — K measurement + ledger/model sanity for SHAPES
T6 / T7 (two mini-ledger outputs).  Diagnostic only.
-/
import WSC.Shaped.GlobalShapedP1Out
import WSC.Prep.Global1600
import WSC.Model.GlobalModel

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.T6Probe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

def ctxOut : ScriptContext :=
  p1ShapedOutCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 3 60 2
    (ByteString.mk "DEST") 90 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

def ctxOutEscape : ScriptContext :=
  p1ShapedOutCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 2 60 1
    (ByteString.mk "DEST") 90 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

def ctxOutBurn : ScriptContext :=
  p1ShapedOutMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    100 1 60 1
    (ByteString.mk "DEST") 90 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

def findK (ctx : ScriptContext) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then hi
  else
    let mid := (lo + hi) / 2
    if isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
                  programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) mid)
    then findK ctx lo mid else findK ctx mid hi
  decreasing_by all_goals omega

#eval (validRewardingContext ctxOut, validRewardingContext ctxOutEscape,
       validRewardingContext ctxOutBurn)
#eval (WSC.Model.globalModel ppCS ctxOut, WSC.Model.globalModel ppCS ctxOutEscape,
       WSC.Model.globalModel ppCS ctxOutBurn)
#eval (findK ctxOut 0 9000, findK ctxOutEscape 0 9000, findK ctxOutBurn 0 9000)

end WSC.T6Probe
