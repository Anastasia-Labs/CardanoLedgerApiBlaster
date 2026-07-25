-- Root of the `WSC` library: UPLC-level containment proofs for the WSC
-- (CIP-113 programmable tokens) production validators.
-- See WSC/ARCHITECTURE.md and WSC/flats/PROVENANCE.md.
import WSC.Imports
-- Explicit (also reached via WSC.Imports): the global/transfer validator's
-- prep only decodes on the CIP-153-capable PlutusCoreBlaster pinned by
-- lakefile.lean — see ARCHITECTURE.md ADDENDUM E11 "Substrate pins".
import WSC.Prep.Global
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
