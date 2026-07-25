/-
WSC/Shaped/Probe/T1Probe.lean — exploration probe for SHAPE T1 (task V1):
does the concrete witness satisfy `validRewardingContext`, does the SOURCE MODEL
accept it, and what is its exact CEK step count?  Diagnostic only.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Prep.Global1600
import WSC.Model.GlobalModel

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.T1Probe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE T1 with containment RESPECTED: qIn = 5 at the mini-ledger, qOut = 5. -/
def ctxOk : ScriptContext :=
  p1ShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 5
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T1 with containment VIOLATED: qIn = 5 at the mini-ledger but only
qOut = 3 comes back; the missing 2 escape to the pubkey output (qEsc = 6). -/
def ctxEscape : ScriptContext :=
  p1ShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 3
    (ByteString.mk "DEST") 100 6
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T2 witness (nonzero mint, `Member` proof): mints +3, so the
requirement rises to qIn + 3 = 8 and the mini-ledger output holds 8. -/
def ctxMint : ScriptContext :=
  p1ShapedMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 3
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 8
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T2 witness, BURN case: mints -4, so `qIn + q = 1` and the mini-ledger
output holds 1. -/
def ctxBurn : ScriptContext :=
  p1ShapedMintCtx (ByteString.mk "MMM") (ByteString.mk "TOK") (-4)
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5
    (ByteString.mk "EXT") 100 4
    150 1
    (ByteString.mk "DEST") 100 4
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0
    50

/-- SHAPE T3 witness (two token names → the wholesale/builtin dispatch arm). -/
def ctxTwo : ScriptContext :=
  p1ShapedTwoCtx (ByteString.mk "MMM") (ByteString.mk "AAA") (ByteString.mk "BBB")
    (ByteString.mk "PROGLOGIC") (ByteString.mk "OWNER") 200 5 7
    (ByteString.mk "EXT") 100 4 2
    150 5 7
    (ByteString.mk "DEST") 100 4 2
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

/-- Smallest budget at which the real bytecode HALTS on `ctx` (binary search). -/
def findK (ctx : ScriptContext) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then hi
  else
    let mid := (lo + hi) / 2
    if isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
                  programmableLogicGlobal1600.script (globalInputs1600 ppCS ctx) mid)
    then findK ctx lo mid else findK ctx mid hi
  decreasing_by all_goals omega

#eval validRewardingContext ctxOk
#eval validRewardingContext ctxEscape
#eval validRewardingContext ctxMint
#eval validRewardingContext ctxBurn
#eval validRewardingContext ctxTwo

#eval WSC.Model.globalModel ppCS ctxOk
#eval WSC.Model.globalModel ppCS ctxEscape
#eval WSC.Model.globalModel ppCS ctxMint
#eval WSC.Model.globalModel ppCS ctxBurn
#eval WSC.Model.globalModel ppCS ctxTwo

#eval (findK ctxOk 0 6000, findK ctxEscape 0 6000, findK ctxMint 0 6000,
       findK ctxBurn 0 6000, findK ctxTwo 0 6000)

end WSC.T1Probe
