/-
WSC/Shaped/Probe/S1K.lean — exact CEK step counts of the three SHAPE S1 concrete
instances, plus their `validRewardingContext` verdicts.

No prep and no solver is involved here: this runs the imported production flat
through `cekExecuteProgram` directly, so these numbers are independent of both
the shaped prep and Z3.
-/
import WSC.Shaped.SeizeShaped

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace WSC.S1Probe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext validRewardingContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

def ppCS : CurrencySymbol := ByteString.mk "PARAMS"

/-- SHAPE S1 at a leaf assignment, spelled out once and reused with the values
that distinguish the three instances. -/
def mk (i0Qty o0Qty : Integer) (escH : ByteString) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (i1CS i1Tn : ByteString) (i1Qty : Integer) (mQ : Integer) : ScriptContext :=
  seizeShapedCtx
    (ByteString.mk "PROGLOGIC") (ByteString.mk "USERSTK") 300
      (ByteString.mk "MMM") (ByteString.mk "TOK") i0Qty
      (ByteString.mk "DTM")
    (ByteString.mk "WALLET") 100 i1CS i1Tn i1Qty
    (ByteString.mk "USERSTK") 300 o0Qty (ByteString.mk "DTM")
    escH 50 o1CS o1Tn o1Qty
    (ByteString.mk "MMM") (ByteString.mk "TOK") mQ
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
      (ByteString.mk "SEIZELOGIC")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "MMM") (ByteString.mk "ZZZ") (ByteString.mk "TLS")
      (ByteString.mk "ZZILS") (ByteString.mk "GS")
    (ByteString.mk "AASEIZE") (ByteString.mk "ZZILS") 0 0
    50

/-- INSTANCE 1 — accepting, "nothing moves": the pair keeps all 10 seized tokens,
output 1 is OUTSIDE the mini-ledger and holds an unrelated policy. -/
def ctxAccept : ScriptContext :=
  mk 10 12 (ByteString.mk "CHANGE") (ByteString.mk "ZZZP") (ByteString.mk "WT") 1
     (ByteString.mk "ZZZP") (ByteString.mk "WT") 1 2

/-- INSTANCE 2 — accepting, "residual output": 5 seized tokens leave the pair and
land in output 1, which IS at the base credential (`escH = plc`). This is the
shape of the real accepting seize goldens. -/
def ctxResidual : ScriptContext :=
  mk 9 4 (ByteString.mk "PROGLOGIC") (ByteString.mk "MMM") (ByteString.mk "TOK") 8
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

/-- INSTANCE 3 — THE EXCLUDED CASE: 6 seized tokens ESCAPE the mini-ledger
through output 1, which is at a non-base script credential. Ledger-legal, inside
SHAPE S1, and violating conjunct 2. Must be REJECTED. -/
def ctxEscape : ScriptContext :=
  mk 10 4 (ByteString.mk "CHANGE") (ByteString.mk "MMM") (ByteString.mk "TOK") 9
     (ByteString.mk "MMM") (ByteString.mk "TOK") 1 2

def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

def runAt (c : ScriptContext) (n : Nat) : Bool :=
  isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
            (WSC.seizeInputs ppCS c) n)

def firstAccept (c : ScriptContext) (lo hi : Nat) : Option Nat :=
  ((List.range (hi - lo)).map (fun i => lo + i)).find? (fun n => runAt c n)

#eval (validRewardingContext ctxAccept, validRewardingContext ctxResidual,
       validRewardingContext ctxEscape)

#eval (firstAccept ctxAccept 2500 3300, firstAccept ctxResidual 2700 3800,
       runAt ctxEscape 3800, runAt ctxEscape 20000)

end WSC.S1Probe
