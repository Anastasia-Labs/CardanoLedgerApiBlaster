/-
PROBE (task U1) — COST probe, NOT expected to complete: an UNSHAPED `#prep_uplc` of
`programmableLogicGlobal` at budget 3300 (what a Tier-A bridge for SHAPE G6 would
need).  MEASURED: no completion in 10 min; a second run still unfinished at >75 min (killed).
Compare 39 s at budget 1600.  See WSC/SHAPE-BRIDGE.md §6.
-/
import WSC.Prep.Global1600
import Blaster
set_option maxHeartbeats 0
namespace WSC
#prep_uplc appliedGlobalU3300 programmableLogicGlobal1600 globalInputs1600 3300
end WSC
