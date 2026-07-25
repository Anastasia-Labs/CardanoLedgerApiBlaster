-- Root of the `WSC` library: UPLC-level containment proofs for the WSC
-- (CIP-113 programmable tokens) production validators.
-- See WSC/ARCHITECTURE.md and WSC/flats/PROVENANCE.md.
import WSC.Imports
-- Explicit (also reached via WSC.Imports): the global/transfer validator's
-- prep only decodes on the CIP-153-capable PlutusCoreBlaster pinned by
-- lakefile.lean — see ARCHITECTURE.md ADDENDUM E11 "Substrate pins".
import WSC.Prep.Global
-- Second prep of the SAME global validator at CEK budget 1600 (task Y1): the
-- 600 prep above is provably VACUOUS (its own probe returns Valid), while 1600
-- exceeds the cheapest accepting golden's K = 1554, so it is the budget P5 is
-- stated against.  See WSC/Prep/Global1600.lean's header.
import WSC.Prep.Global1600
import WSC.Redeemer
import WSC.Spec
import WSC.Honest
import WSC.Props.P3_Base
-- P4/P4a (issuance minting policy) at budget 900: statements + the machine-checked
-- budget characterization and both positive witnesses. See the SOLVER COST stanza
-- in that file for what is and is not closed.
import WSC.Props.P4_Minting
-- Golden→Lean bridge + the three Y4 fidelity results (LR-CTX audit, real-suite
-- positive witness, redeemer/datum mirror gate). See WSC/LR-CTX-AUDIT.md.
import WSC.Goldens
-- P5 (escape-critical, NonMember/covering-node) at budget 1600: statement,
-- source-cited mirror of the three PNonMember checks, and the pure-Lean
-- reduction ladder.  READ the OBLIGATION STATUS block in that file: the
-- bytecode obligation is NOT discharged (blaster returned no verdict in 87 min).
import WSC.Props.P5_NonMember
-- Concrete non-vacuity witness for budget 1600 (real bytecode + real golden
-- NonMember ScriptContext: HALT at 1600, budget-ERROR at 1553).
import WSC.Props.P5_Witness1600
-- SOURCE MODEL of the global transfer validator (task Z4, ARCHITECTURE.md §2 B3
-- route): P1 (containment) and P6 (Member self-penalization) are unreachable at
-- UPLC (accepting runs cost 3,262/3,726 CEK steps), so they are proved against a
-- source-cited transcription bridged by ONE axiom.  The model's verdict equals
-- the real bytecode's on 4/4 global goldens, incl. the rejecting containment
-- violation.  READ the OBLIGATION STATUS block at the bottom of
-- WSC/Props/P1_Transfer.lean before citing anything from it.
import WSC.Model.GlobalModel
import WSC.Model.Ground
import WSC.Model.GlobalGoldens
import WSC.Props.P1_Transfer
import WSC.Props.P6_Member
-- P2 (seize) via the SOURCE-MODEL route (B3), task Z3: seize is unreachable at
-- UPLC (cheapest accepting run 2,570 CEK steps; prep at 2,000 unfinished in
-- 77 min; the budgets whose prep completes have vacuity probes returning Valid),
-- so it is proved against a source-cited transcription bridged by ONE axiom,
-- `WSC.SeizeModel.seizeModel_faithful`.  The model's verdict equals the real
-- bytecode's on 13/13 goldens, including the rejecting seize golden.  READ the
-- "HOW TO READ THIS FILE" block at the top of WSC/Props/P2_Seize.lean: conjunct 1
-- (structure preservation) is PROVEN unconditionally about the model, conjunct 2
-- (containment) is stated + verified on the goldens but NOT proven.
import WSC.Model.SeizeModel
import WSC.Model.SeizeDiff
import WSC.Props.P2_Seize
