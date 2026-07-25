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
