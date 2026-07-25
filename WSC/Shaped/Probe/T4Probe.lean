/-
WSC/Shaped/Probe/T4Probe.lean — K measurement and ledger/model sanity for SHAPES
T4 / T5 (two mini-ledger inputs).  Diagnostic only.
-/
import WSC.Shaped.GlobalShapedP1Agg
import WSC.Prep.Global1600
import WSC.Model.GlobalModel

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.T4Probe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE T4 accepting: 5 + 3 = 8 from the mini-ledger, 8 back. -/
def ctxAgg : ScriptContext :=
  p1ShapedAggCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
    (ByteString.mk "EXT") 100 4
    250 8
    (ByteString.mk "DEST") 120 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T4 escaping: only 6 of the aggregated 8 come back. -/
def ctxAggEscape : ScriptContext :=
  p1ShapedAggCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
    (ByteString.mk "EXT") 100 4
    250 6
    (ByteString.mk "DEST") 120 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T5 burn: 5 + 3 in, burn 6, so 2 must remain. -/
def ctxAggBurn : ScriptContext :=
  p1ShapedAggMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-6)
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 120 3
    (ByteString.mk "EXT") 100 4
    250 2
    (ByteString.mk "DEST") 120 4
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

#eval (validRewardingContext ctxAgg, validRewardingContext ctxAggEscape,
       validRewardingContext ctxAggBurn)
#eval (WSC.Model.globalModel ppCS ctxAgg, WSC.Model.globalModel ppCS ctxAggEscape,
       WSC.Model.globalModel ppCS ctxAggBurn)
#eval (findK ctxAgg 0 9000, findK ctxAggEscape 0 9000, findK ctxAggBurn 0 9000)

end WSC.T4Probe
