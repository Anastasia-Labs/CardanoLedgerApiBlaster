/-
WSC/Shaped/Probe/GDestructure1600C.lean — PROBE (P4-technique transfer), v2,
stanza C: **P5's covering-node postcondition, UNSHAPED modulo a skeleton.**

⛔ NOT IMPORTED BY ANYTHING. NOT A RESULT MODULE. Build deliberately:

    lake build WSC.Shaped.Probe.GDestructure1600C

Read first, in this order: WSC/Shaped/Probe/GDestructure1600B.lean (the proven
statement-level-destructure pattern this module extends, and its measured
≈37 min / ≈5 GB price for a CONTENT-carrying leaf), then
WSC/Shaped/Probe/GDestructure1600.lean (the v1 post-mortem: tactic-level
`cases`/`match` on goals carrying the 1600-step residual is FORBIDDEN — it
multiplies the residual and took the box out with a kernel OOM), then
WSC/Props/P5_NonMember.lean (the audited mirrors reused here by name, and the
87-minute NO-VERDICT this stanza is trying to retire for one skeleton class).

════════════════════════════════════════════════════════════════════════════
WHAT THIS CLAIMS, AND WHY IT IS THE ESCAPE-CRITICAL ONE
════════════════════════════════════════════════════════════════════════════
Stanza B pinned the params-authentication gate (`phasCSH` on the reference
input the redeemer names as params). Stanza C goes after the property the whole
containment argument rests on — ADDENDUM E3's P5: **an accepting run that
classifies a minted policy `NonMember` really did check an authentic directory
node whose key interval strictly covers that policy.** Its fully symbolic form
(`WSC.P5_nonmember_covering_node_indexed`, WSC/Props/P5_NonMember.lean) is the
statement that consumed 87 minutes and returned NO verdict — not Valid, not
Undetermined, no counterexample.

The move is the same one that turned stanza B from a wall into a 37-minute
`✅ Valid`: put the destructuring INSIDE the `prop` application, so blaster sees
one goal with the constructors already concrete, and the two index projections
(`nthFrom … pIdx`, `nthFrom … nodeIdx`) and the positional mint-walk
classification (`nonMemberNodeIdxOf`) are DISCHARGED BY THE SKELETON instead of
being symbolic hypotheses the solver has to reason through.

Skeleton, all stated in the theorem (nothing is a tactic-side `cases`):

  * redeemer = `Constr 0 [f1, f2, f3, List [Constr 1 [I 1]], I 0]` — a raw
    5-field `TransferAct` spine (WSC/Redeemer.lean, `PLGRedeemer`, tags frozen
    by `makeIsDataIndexed` at ProgrammableLogicBase.hs:1067-1069, `TransferAct
    = 0`; field order :1039-1055, `plgrMintProofs` FOURTH and `plgrParamsRefIdx`
    FIFTH — both re-verified against WSC/Redeemer.lean before writing this).
    - `f1 f2 f3` symbolic `Data`: `transferProofs`, `transferWdrlIdxs`,
      `ownerWdrlIdxs`. Deliberately WEAKER than `IsData`-decodability — they
      need not be `Data.List`s of `Data.I` at all.
    - the FOURTH field is the mint-proof list, pinned to exactly ONE proof, the
      `NonMember` constructor: `Constr 1 [I 1]`. Encoding re-derived, not
      assumed: `MintProof` tags are `Member = 0`, `NonMember = 1`
      (ProgrammableLogicBase.hs:1035-1037), `NonMember` carries one `Integer`
      field (:1030-1033, Plutarch mirror `PNonMember` :943-948), so
      `IsData.toData (MintProof.NonMember 1) = mkDataConstr 1 [Data.I 1]
      = Data.Constr 1 [Data.I 1]` (WSC/Redeemer.lean:129-136;
      `mkDataConstr = Data.Constr`, CardanoLedgerApi/IsData/Class.lean:15).
      Node index `1` LITERAL.
    - the FIFTH field is `paramsRefIdx = 0` LITERAL.
  * `txInfoMint = [(Data.B cs, Data.Map m)]` — exactly ONE non-Ada mint entry,
    for `cs`, with the inner token map `m` fully symbolic. This is what makes
    the classification of `cs` POSITIONAL and unambiguous (ADDENDUM E8): the
    validator walks `mintedEntries = pto (pto totalMintValue)` in lockstep with
    the proof list (ProgrammableLogicBase.hs:982-1026), a missing proof is
    `"mint proof missing"` (:1018) and a spare one `"extra mint proof"` (:1024),
    so with one entry and one proof the `NonMember 1` proof IS the proof at
    `cs`'s position. (`MintValue = V2.Value = List (Data × Data)`,
    CardanoLedgerApi/V3/Contexts.lean:330.)
  * `txInfoReferenceInputs = pIn :: nIn :: rTail` — reference index 0 is `pIn`
    (so `paramsRefIdx = 0` resolves to it: `pparamsAtRefIdx`,
    ProgrammableLogicBase.hs:824-838, applied :1196-1199) and reference index 1
    is `nIn` (so the `NonMember 1` node lookup `phead # (pdropList # nodeIdx #
    refInputs)`, :997-998, resolves to it). `rTail` symbolic.
  * everything else symbolic: the whole rest of `tin` (15 fields, as
    projections of a free `TxInfo`), the script parameter `ppCS`, both currency
    symbols, and the rewarding credential.
  * purpose = `.RewardingScript cred`, `cred` symbolic — this validator is a
    rewarding script (SHAPE G1 uses `.RewardingScript (.ScriptCredential w0)`,
    WSC/Shaped/GlobalShaped.lean:203).

Hypothesis (one, and it is a NAMING projection, not an honesty assumption):
`P5.paramsDatumDirCSRaw pIn.txInInfoResolved = some dirCS` — position 0 of the
params UTxO's INLINE datum, read exactly as the bytecode reads it
(`punsafeCoerce @(PAsData PProgrammableLogicGlobalParams)`, :834-836; field
order normative, ProtocolParams.hs:44-68). It is left as a HYPOTHESIS rather
than substituted into the skeleton: it is a match-based projection, so
concretizing it would force a `Data.List (Data.B dirCS :: …)` datum shape into
the statement and thereby ASSUME more about the params input than the validator
does. Nothing else about `pIn` is assumed — in particular NOT that it is
NFT-authenticated; the validator's own `phasCSH` gate is what forces that on
the accept path (stanza B is precisely that claim).

Conclusion: `P5.dirNodeAuthH dirCS nIn.txInInfoResolved = true ∧
P5.coversCS cs nIn.txInInfoResolved = true` — verbatim the three `pand'List`
conditions of the `PNonMember` branch (ProgrammableLogicBase.hs:1009-1011):
:1011 `phasCSH # directoryNodeCS # …` ⟶ `dirNodeAuthH`, :1009 `nodeKey #< currCS`
and :1010 `currCS #< nodeNext` ⟶ `coversCS`. Both mirrors are reused BY NAME
from WSC/Props/P5_NonMember.lean (audited there); this module defines no new
postcondition vocabulary. `P5.nthFrom` is not needed in the statement because
the skeleton exposes the two indexed positions structurally — but the class is
the same one `P5.nthFrom … 0 = some pIn` / `… 1 = some nIn` names, and
`P5_exists_of_indexed` (proved, ibid.) lifts this conclusion to ADDENDUM E3's
∃-form given `nthFrom (pIn :: nIn :: rTail) 1 = some nIn`, which is `rfl`.

RELATION TO THE 87-MINUTE NO-VERDICT. `P5_nonmember_covering_node_indexed`
quantifies a FREE `ctx` plus five projection hypotheses (`transferParamsRefIdx`,
two `nthFrom`s at SYMBOLIC indices, `paramsDatumDirCSRaw`, `nonMemberNodeIdxOf`)
and `validRewardingContext ctx`. This stanza is that statement with the two
indices pinned to the literals 0 and 1, the mint list pinned to one entry, the
proof list pinned to one `NonMember`, and `validRewardingContext` DROPPED
(strictly stronger in that direction: no ledger normalization is assumed). It is
therefore a sub-class, not the whole obligation — what it can retire is the
no-verdict FOR THIS SKELETON CLASS, not P5 itself.

════════════════════════════════════════════════════════════════════════════
NON-VACUITY OF THE CLASS (checked by hand against SHAPE G1, no machine-checked
membership theorem in this probe — see the note at the end)
════════════════════════════════════════════════════════════════════════════
The SHAPE-G1 witness `WSC.P5ShapedWitness.ctx` (WSC/Props/Shaped/P5Shaped.lean:
438-448) is accepted by the UNSHAPED 1600 prep's executable term —
`P5ShapedWitness.exec_accepts_at_1600_unshaped : isSuccessful
(appliedGlobal1600.exec ppCS ctx)`, `native_decide`, and it is the witness
`WSC.NonVacuity.globalNonVacuous_at_1600` is built from. Layout check against
this skeleton, field by field:

  * redeemer: `globalShapedRedeemer = Data.Constr 0 [Data.List [], Data.List [],
    Data.List [], Data.List [Data.Constr 1 [Data.I 1]], Data.I 0]`
    (`globalShapedRedeemer_eq`, WSC/Shaped/GlobalShaped.lean:122-126) —
    matches with `f1 = f2 = f3 = Data.List []`, the same one-`NonMember 1`
    proof list, the same literal `paramsRefIdx = 0`. ✔
  * mint: `mintOne cs tn q = [(Data.B cs, Data.Map [(Data.B tn, Data.I q)])]`
    (WSC/Shaped/Shape.lean:67-69) — one entry for `cs`, matches with
    `m = [(Data.B tn, Data.I q)]`. ✔
  * reference inputs: `[globalShapedParamsIn …, globalShapedNode …]`
    (GlobalShaped.lean:185-187) — params FIRST, node SECOND, matches
    `pIn :: nIn :: rTail` with `rTail = []`. ✔
  * params datum: `paramsDatumDirCSRaw` on the shaped params input is
    `some dirCS` by `rfl` (`shape_paramsDirCS`, P5Shaped.lean:185-187) — the
    hypothesis is satisfiable and satisfied. ✔
  * purpose: `.RewardingScript (.ScriptCredential w0)` (GlobalShaped.lean:203) —
    matches `.RewardingScript cred`. ✔
  * postcondition non-triviality: at G1's leaves the conclusion is TRUE
    (`P5ShapedWitness.ctx_post`, `native_decide`) but it is NOT true by
    construction — `nCS`, `key`, `next` are free variables of the shape
    (GlobalShaped.lean:141-144), so the class contains contexts where the
    conclusion fails, and those must be the ones the bytecode rejects.

So the skeleton is inhabited by a real accepting run of this bytecode at this
budget. (What is NOT machine-checked here is the syntactic instantiation
`P5ShapedWitness.ctx = ⟨{tin with …}, Constr 0 […], .RewardingScript cred⟩` for
some `tin`; that would be a `rfl`-scale lemma and is deliberately out of scope
for a probe — the field-by-field reading above is the audit.)

DOC DRIFT NOTED (not fixed here, and not load-bearing for the above): several
headers, including stanza B's, cite `P5ShapedWitness.K_is_1541`. No declaration
by that name exists in the tree any more; the live two-sided pin is
`WSC.P5ShapedWitness.K_is_1402` (WSC/Props/Shaped/P5Shaped.lean:515-519), i.e.
K = 1402 after the PR #112 re-measure — still comfortably inside 1600, so the
non-vacuity argument is unaffected. Treat "1541" in sibling headers as stale.

House rules: explicit `(timeout: …)` on the blaster call (the default solver
timeout is INFINITE); `maxHeartbeats 0`; `warn.sorry false` (blaster closes
Valid via `admit`). Run under a hard `ulimit -v` ≥ 28 GiB — stanza B's run 1
died of a 14 GiB VIRTUAL cap at only 5.2 GB RSS, and v1 of this probe family
took the whole WSL VM down with a 46 GB kernel OOM.

════════════════════════════════════════════════════════════════════════════
MEASURED (2026-08-03, 32-core / 61 GB box, warm deps, `ulimit -v` 28 GiB,
`timeout -s KILL 5400 lake build WSC.Shaped.Probe.GDestructure1600C`)
════════════════════════════════════════════════════════════════════════════
**`✅ Valid`** — verdict line, verbatim from the log
(.lake/wsc-probe-logs/g1600C-run1.log:773):

    info: WSC/Shaped/Probe/GDestructure1600C.lean:216:2: ✅ Valid

(216 was the `blaster` call's line in the file AS RUN, i.e. before this MEASURED
block was appended to the header. The line number moves every time this header
is edited; it always points at the single `blaster` call at the bottom of the
file, and each rebuild below re-reports it.)

  * module elaboration: **102 s** (`ℹ [354/354] Built
    WSC.Shaped.Probe.GDestructure1600C (102s)`), whole build **100.34 s wall**
    (`Elapsed (wall clock) time 1:40.34`; the two differ because `lake`
    overlaps the replay of the 353 cached deps with this module's job).
  * **MaxRSS 7 426 708 kB ≈ 7.4 GB** (`/usr/bin/time -v`, whole process tree,
    so this includes the z3 child).
  * exit 0, no OOM, Z3 well inside its 900 s cap. No retry, no cap change.
  * REPRODUCED on the final text of this file
    (.lake/wsc-probe-logs/g1600C-run2-header.log): same
    `✅ Valid`, at `GDestructure1600C.lean:265:2`, module **98 s**, whole build
    **96.48 s wall**, **MaxRSS 7 428 988 kB ≈ 7.4 GB**, exit 0.
  * REPRODUCED again after the final header edit
    (.lake/wsc-probe-logs/g1600C-run3-final.log): `✅ Valid`, module **97 s**,
    whole build **95.43 s wall**, **MaxRSS 7 428 148 kB ≈ 7.4 GB**, exit 0. So
    the module in the tree is green as written; three runs give 102/98/97 s and
    a MaxRSS spread under 0.03 %.
  * (The `Name.append` / `EnvExtension` panic backtraces earlier in the log are
    REPLAYED stored messages from `Contexts.olean`, identical in the SUCCESSFUL
    stanza-A/B logs — do not attribute anything to them. Likewise
    `info: WSC/Prep/Global.lean:84:41: ✅ Valid` is a replayed message from a
    DEPENDENCY, the budget-600 vacuity probe, not this module's verdict.)

WHAT THIS RETIRES. For THIS SKELETON CLASS, the P5 obligation that returned NO
verdict in 87 minutes over a fully symbolic `ctx`
(`WSC.P5_nonmember_covering_node_indexed`, WSC/Props/P5_NonMember.lean, the
OBLIGATION STATUS table) is now discharged against the REAL production transfer
bytecode at budget 1600 — in 102 seconds. It does NOT discharge P5 in general:
the node index, the params index, the mint-entry count and the proof-list length
are pinned to literals here, and `validRewardingContext` is not assumed.
This is the library's first unshaped-modulo-skeleton P5 result: unlike
`WSC.P5_shaped_indexed` (WSC/Props/Shaped/P5Shaped.lean), which is stated over
the fully concrete SHAPE-G1 `globalShapedCtx` term with only leaf VALUES free,
the context here is a free `TxInfo` with three fields destructured — 15 of its
18 fields, the whole input/output/withdrawal/redeemer-map structure, and the
reference-input tail are unconstrained.

COST SURPRISE, AND THE LESSON. Stanza B — ONE content leaf, a strictly SIMPLER
postcondition (`dirNodeAuthH` alone), a strictly SMALLER skeleton
(`pIn :: rTail`, no mint pin, symbolic purpose) — cost **2210 s / 4.9 GB**.
Stanza C costs **102 s / 7.4 GB**: ~21× FASTER for a strictly stronger claim
over a strictly more destructured statement, at ~1.5× the memory. So the
per-leaf price is NOT monotone in the strength of the postcondition; it is
dominated by how much of the residual the skeleton lets Blaster fold away
BEFORE the SMT translation. Pinning `txInfoMint` to a single entry and the
purpose to `.RewardingScript` collapses the mint walk (:982-1026) and the
purpose dispatch, which is evidently where stanza B's 28 minutes of Lean-side
optimization went. Practical rule for the next rung: MORE statement-level
concretization can be CHEAPER, so do not ration the skeleton to keep the class
wide — cut a narrow, fast leaf first and widen it afterwards.

Whether the same trick rescues the un-pinned indices (SHAPING-RESULTS.md §2.4's
shape G3 went `⚠️ Undetermined` after a 906 s Z3 query on a free redeemer index)
is NOT answered by this run and remains the open question for the class.
-/
import WSC.Props.P5_NonMember
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC
namespace GDestructureProbe

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptInfo TxInfo TxInInfo)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils (isSuccessful)

/-- **STANZA C — P5's covering-node postcondition, unshaped modulo a skeleton.**

If the real compiled transfer validator accepts, within 1600 CEK steps, a
transaction that

* mints exactly one non-Ada policy `cs` (inner token map symbolic),
* carries a `TransferAct` redeemer whose mint-proof list is exactly one
  `NonMember 1` and whose `paramsRefIdx` is `0` (the other three fields
  symbolic `Data`),
* has the params UTxO at reference index 0 and the claimed directory node at
  reference index 1 (tail symbolic), everything else about the `TxInfo`
  symbolic,

and the params datum names `dirCS` as the directory policy, THEN the reference
input at index 1 really is authenticated as a directory node of `dirCS` and its
`(key, next)` interval strictly covers `cs`.

Conclusion = ProgrammableLogicBase.hs:1009-1011 verbatim, via the audited
mirrors of WSC/Props/P5_NonMember.lean. -/
theorem p5_covering_node_at_1600 :
    ∀ (ppCS dirCS cs : CurrencySymbol) (tin : TxInfo) (cred : Credential)
      (f1 f2 f3 : Data) (m : List (Data × Data))
      (pIn nIn : TxInInfo) (rTail : List TxInInfo),
      P5.paramsDatumDirCSRaw pIn.txInInfoResolved = some dirCS →
      isSuccessful (appliedGlobal1600.prop ppCS
        (ScriptContext.mk
          { tin with
              txInfoReferenceInputs := pIn :: nIn :: rTail
            , txInfoMint := [(Data.B cs, Data.Map m)] }
          (Data.Constr 0 [f1, f2, f3, Data.List [Data.Constr 1 [Data.I 1]], Data.I 0])
          (ScriptInfo.RewardingScript cred))) →
      P5.dirNodeAuthH dirCS nIn.txInInfoResolved = true
      ∧ P5.coversCS cs nIn.txInInfoResolved = true := by
  blaster (timeout: 900)

end GDestructureProbe
end WSC
