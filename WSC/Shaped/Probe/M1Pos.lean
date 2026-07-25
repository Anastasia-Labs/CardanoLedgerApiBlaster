/- Z2: is a POSITIVE-mint SHAPE M1 context ledger-valid?  (If not, P4_burn_only_shaped
   would be vacuous on exactly the case it is supposed to exclude.) -/
import WSC.Props.Shaped.P4Shaped
import WSC.Goldens.Decode
import Blaster
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace WSC.Z2Probe.M1Pos
open CardanoLedgerApi.V3 (validMintingContext)
open PlutusCore.ByteString (ByteString)

/-- SHAPE M1 with q = +3: mint 3 tokens, input holds 2, output holds 5. -/
def ctxPos : CardanoLedgerApi.V3.ScriptContext :=
  mintShapedCtx (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 100 2 (ByteString.mk "DEST") 60 5
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
    (ByteString.mk "") 0 0 1 (ByteString.mk "")

#eval validMintingContext ctxPos
#eval (WSC.Goldens.conjuncts .minting ctxPos).filter (fun p => !p.2)
#eval mintPos (ByteString.mk "OWNCS") ctxPos.scriptContextTxInfo.txInfoMint
#eval P4ShapedWitness.isHaltB
  (appliedMintShaped900.exec (ByteString.mk "PARAMS") (ByteString.mk "MINTLOGIC")
    (ByteString.mk "OWNCS") (ByteString.mk "TOK") 3
    (ByteString.mk "OWNER") 100 2 (ByteString.mk "DEST") 60 5
    (ByteString.mk "MINTLOGIC") (ByteString.mk "ZZZ") 0 0 40
    (ByteString.mk "") 0 0 1 (ByteString.mk ""))
end WSC.Z2Probe.M1Pos
