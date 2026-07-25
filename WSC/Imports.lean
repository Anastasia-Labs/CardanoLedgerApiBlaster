/-
WSC/Imports.lean — aggregation of the imported + prepped production
validators (arch §0.1 idiom, §3 budgets; flats provenance in
WSC/flats/PROVENANCE.md).

The actual `#import_uplc` / `#prep_uplc` commands live in one module per
validator under WSC/Prep/ so each expensive prep elaboration is cached
independently:

* WSC/Prep/Base.lean    — `appliedBase`    (spending,  budget 600)
* WSC/Prep/Minting.lean — `appliedMinting` (minting,   budget 600)
* WSC/Prep/Seize.lean   — `appliedSeize`   (rewarding, budget 600)
* WSC/Prep/Global.lean  — `appliedGlobal`  (rewarding, budget 600; CIP-153
  builtins — requires the `cip153-value-builtins` PlutusCoreBlaster, see
  ARCHITECTURE.md "Substrate pins")

The .flat files are the raw TextEnvelope `cborHex` strings of the UNAPPLIED
production scripts, so `double_cbor_hex` is the correct decoder (TextEnvelope
cborHex = CBOR bytestring wrapping the CBOR-wrapped flat program). Parameter
count/order/type evidence (Plutarch `mk*` signature + offchain application
site, file:line) is documented above each inputs function in those modules.
-/
import WSC.Prep.Base
import WSC.Prep.Minting
import WSC.Prep.Seize
import WSC.Prep.Global
