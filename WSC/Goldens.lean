/-
WSC/Goldens.lean — aggregator for the golden→Lean bridge and the three fidelity
results built on it (task Y4).

* `WSC/Goldens/Vectors.lean`    — GENERATED: the 13 goldens' `serialiseData` hexes.
* `WSC/Goldens/Terms.lean`      — GENERATED: the same payloads as `Data` literals
                                  (Blaster cannot see through PCB's `partial`
                                  CBOR decoder).
* `WSC/Goldens/TermsCheck.lean` — GENERATED: proves the literals ≡ PCB's own
                                  CBOR decode of the same hexes.
* `WSC/Goldens/gen-vectors.py`  — the generator for all three (`--check` verifies
                                  the committed copies against the JSONs).
* `WSC/Goldens/Decode.lean`     — hex → `Data` → CLAB `ScriptContext`, plus the
                                  audit machinery.
* `WSC/Goldens/Audit.lean`      — RESULT A: the ADDENDUM E5 LR-CTX audit
                                  (write-up: `WSC/LR-CTX-AUDIT.md`).
* `WSC/Goldens/Witnesses.lean`  — RESULT B: real-suite positive witness for P3.
* `WSC/Goldens/RedeemerGate.lean` — RESULT C: ADDENDUM E8 mirror-instance gate.
-/
import WSC.Goldens.Vectors
import WSC.Goldens.Terms
import WSC.Goldens.TermsCheck
import WSC.Goldens.Decode
import WSC.Goldens.Audit
import WSC.Goldens.Witnesses
import WSC.Goldens.RedeemerGate
