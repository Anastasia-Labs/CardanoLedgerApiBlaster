/-
WSC/Shaped/Probe/GDestructure1600B.lean — PROBE (P4-technique transfer), v2,
stanza B. Split from WSC/Shaped/Probe/GDestructure1600.lean (read its header
first: v1's tactic-level form of these stanzas ended in a box-level OOM; v2 is
the statement-level re-cut, one blaster goal per module).

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT MODULE. Build deliberately:

    lake build WSC.Shaped.Probe.GDestructure1600B

**STANZA B — the P4-analog with real content.** Claim: an accepting run at
budget 1600 forces the validator's own params authentication (`phasCSH`,
ProgrammableLogicBase.hs:832 via `pparamsAtRefIdx` :824-838, applied at
:1196-1199 before the mint walk on EVERY `TransferAct` path) on the reference
input the redeemer names. Destructured skeleton, all stated in the theorem:

  * redeemer = `Constr 0 [f1, f2, f3, f4, I 0]` — a raw 5-field `TransferAct`
    spine with `plgrParamsRefIdx = 0` LITERAL; `f1..f4` symbolic `Data` (note:
    WEAKER than `IsData`-decodability — the proofs/index lists need not decode);
  * `txInfoReferenceInputs = pIn :: rTail` — head exposed, tail symbolic
    (`{ tin with … }` keeps the other 15 `TxInfo` fields as projections of a
    fully symbolic `tin`);
  * everything else symbolic: `tin`, the purpose, both currency symbols.

Postcondition vocabulary: `P5.dirNodeAuthH` — the audited mirror of `phasCSH`
(first non-ada policy of the value is the given symbol), the same mirror the
PROVED shaped P5 theorems validated against this bytecode.

The literal index is the point (P4_MintingIdx rung): SHAPING-RESULTS.md §2.4
measured that for THIS validator a free redeemer index is load-bearing (shape
G3: `⚠️ Undetermined` after a 906 s Z3 query, over an otherwise CLOSED shape),
and the P4 screenshot's `induction … generalizing n` escape is structurally
unavailable here — `txInfoReferenceInputs` is read at SEVERAL
redeemer-controlled indices at once (params :1196-1199 plus one directory node
per `NonMember` mint proof :996-1015, same list), so the tail-context instance
the induction hypothesis offers is not reachable from `accept` on the cons
context (contrast `txInfoWdrl` for the issuance policy at 900, which is
single-use — the C1 lookup — which is WHY the P4 induction closes).

Non-vacuity of the class: the SHAPE-G1 witness (K = 1402 post-#112, pinned
two-sided by `P5ShapedWitness.K_is_1402` — corrected 2026-08-02 from the
pre-#112 `K_is_1541` — accepted by the unshaped exec at 1600 —
`WSC.NonVacuity.globalNonVacuous_at_1600`) has a 5-field `TransferAct`
redeemer with `paramsRefIdx = 0` and its params input at reference index 0,
i.e. it inhabits exactly this skeleton.

House rules: explicit blaster timeout; `maxHeartbeats 0`; `warn.sorry false`.
Run under a hard `ulimit -v` — but see run 1 below before choosing the size.

MEASURED (2026-08-02, 32-core / 61 GB box, warm deps):

  * run 1, `ulimit -v` 14 GiB: **`INTERNAL PANIC: out of memory` at 1374 s.**
    ~20 min Lean-side optimization (RSS stable ≈4.2 GB), translation OK, a
    ~2-minute Z3 round, then a post-Z3 phase tripped the VIRTUAL-memory cap at
    just 5.2 GB RSS — lean's virt runs 2–3× its RSS in this phase. The cap was
    the failure, not the workload. (The `Name.append`/`EnvExtension` panic
    texts in the log are REPLAYED stored messages from `Contexts.olean` — they
    appear identically in the SUCCESSFUL stanza-A log — do not attribute
    failures to them.)
  * run 2, `ulimit -v` 28 GiB: **✅ Valid — module 2210 s ≈ 37 min wall,
    MaxRSS 4.9 GB** (~28 min Lean-side optimize, then Z3 within its cap).

Read together with stanza A (✅ Valid, 4.7 s): the statement-level destructure
transfers to this validator at budget 1600, and the per-leaf price of a
CONTENT-carrying leaf is ≈37 min / ≈5 GB — about three orders of magnitude
above the issuance policy's ≈2 s leaves at budget 900 (P4_MintingIdx), the
scaling being the residual size. Finite, but it prices a full P4-style
multi-leaf case tree out; choose single-leaf statement-level stanzas.
-/
import WSC.Props.P5_NonMember
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC
namespace GDestructureProbe

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext ScriptInfo TxInfo TxInInfo)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **STANZA B.** Accept at 1600 with a `TransferAct`-spined redeemer naming
params reference index 0 forces `phasCSH ppCS` (mirrored by `P5.dirNodeAuthH`)
on the first reference input. -/
theorem params_gate_at_idx0_1600 :
    ∀ (ppCS : CurrencySymbol) (tin : TxInfo) (sinfo : ScriptInfo)
      (f1 f2 f3 f4 : Data) (pIn : TxInInfo) (rTail : List TxInInfo),
      isSuccessful (appliedGlobal1600.prop ppCS
        ⟨{ tin with txInfoReferenceInputs := pIn :: rTail },
         Data.Constr 0 [f1, f2, f3, f4, Data.I 0], sinfo⟩) →
      P5.dirNodeAuthH ppCS pIn.txInInfoResolved = true := by
  blaster (timeout: 900)

end GDestructureProbe
end WSC
