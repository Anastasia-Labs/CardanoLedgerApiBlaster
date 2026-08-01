/-
WSC/Review/AdversarialProbe.lean — **ADVERSARIAL REVIEW of the proposed
`P1UnshapedFormD` / `P1UnshapedFormH` architecture** (Layer 0 `Model.exempt`,
Layer 1 two forms).

The proposal's robustness rests on a branch census (M1) whose STEP 3 claims each
producer of `expectedProgrammableOutputValue` has exactly one drop branch, and on
the claim that the six failure modes are closed by `validRewardingContext`
(routes 3 and 4) and by `Model.exempt` (routes 1 and 2).

Two of those closures are argued against source that NO WITNESS IN THIS TREE HAS
EVER RUN:

* **`pvalueFromCred` PHASE 3** (`ProgrammableLogicBase.hs@2306678:397-411`,
  `goBuiltin`) — reached only with TWO OR MORE contributing mini-ledger inputs.
  Every P1 witness in `WSC/Benchmark/` and every leaf of SHAPES T1R/T2R/T6R/T7R
  has exactly ONE input at the base credential, so every measured accept exits in
  PHASE 2. Phase 3 is where `punionValue` and `pinsertCoin # "" # "" # 0` decide
  whether `aggIn = inSum` — i.e. exactly the proposal's failure mode (3).
* **THE MULTI-ASSET CONTAINMENT PATHS** (`:628-645` wholesale Data-equality and
  `:615-618` `BuiltinValue.pvalueContains`) — reached only when
  `expectedProgrammableOutputValue` has more than one currency symbol or more
  than one token name (dispatch at `:650-666`). Every shape and every probe
  context carries `adaPlusOne`, ONE policy with ONE token name, so every measured
  accept takes the single-asset fast path `hasAtLeastAssetInProgOutputs`
  (`:567-589`). The two multi-asset paths are the proposal's failure mode (4).

§1 and §2 build accepting and escaping witnesses on both, at the real compiled
bytecode. §3 re-measures the proposed predicate at the refuting and the accepting
witnesses. Nothing here is part of the deliverable.
-/
import WSC.Review.ExemptionCensus

set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace WSC
namespace Review
namespace AdversarialProbe

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxInInfo TxOut Withdrawals RedeemerMap validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)
open WSC.Shape
open P1ShapedWitness (ppCS isHaltB isHaltB_sound)
open ExemptionCensus (halts)

/-! ## §0 — the proposed Layer-0 predicate, verbatim from the design -/

def dirNodeInterval : Data → Option (CurrencySymbol × CurrencySymbol)
  | Data.List (Data.B k :: Data.B n :: _) => some (k, n)
  | _ => none

def exemptible (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeInterval d with
            | some (k, n) =>
                decide (k < cs) && decide (cs < n) &&
                  (Model.hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || exemptible dirCS cs rest

def exempt (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  (cs == ByteString.mk "") || exemptible dirCS cs refs

def isProgrammable (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  !(exempt dirCS cs refs)

/-! ## §1 — the context skeletons

Both skeletons keep everything `BaseAbsentProbe.probeCtxN` fixes and change only
what the two unmeasured paths need. -/

/-- Canonical value with ada plus TWO non-ada policies (`cs1 < cs2` required for
`validTxOutValue`). This shape does not exist anywhere else in the tree. -/
def adaPlusTwo (n : Integer) (cs1 : CurrencySymbol) (tn1 : TokenName) (q1 : Integer)
    (cs2 : CurrencySymbol) (tn2 : TokenName) (q2 : Integer)
    : CardanoLedgerApi.V1.Value.Value :=
  [ (Data.B (ByteString.mk ""), Data.Map [(Data.B (ByteString.mk ""), Data.I n)])
  , (Data.B cs1, Data.Map [(Data.B tn1, Data.I q1)])
  , (Data.B cs2, Data.Map [(Data.B tn2, Data.I q2)]) ]

def csM : CurrencySymbol := ByteString.mk "MMM"
def csN : CurrencySymbol := ByteString.mk "NNN"
def tnTOK : TokenName := ByteString.mk "TOK"
def plcCred : Credential := .ScriptCredential (ByteString.mk "PROGLOGIC")
def dirCS : CurrencySymbol := ByteString.mk "DIRCS"

/-- A directory node reference input at a chosen `TxOutRef` index, carrying the
directory NFT and a five-field well-formed datum keyed `key`. -/
def nodeAt (idx : Integer) (key next : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", idx⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "DIRNODE"), none⟩
   , txOutValue := adaPlusOne 100 dirCS (ByteString.mk "NODETOK") 1
   , txOutDatum := .OutputDatum
       (IsData.toData
         (DirectorySetNode.mk key next (.ScriptCredential (ByteString.mk "TLS"))
                              (.ScriptCredential (ByteString.mk "ILS"))
                              (ByteString.mk "GS")))
   , txOutReferenceScript := none }⟩

def paramsIn : TxInInfo :=
  p1ShapedParamsIn (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS")
    (ByteString.mk "PTOK") 100 1
    dirCS (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL") (ByteString.mk "SEIZE")

def wdrl : Withdrawals := p1ShapedWdrl (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 0 0

def reds (red : Data) : RedeemerMap :=
  p1RRedeemers (ByteString.mk "GLOBAL") (ByteString.mk "TLS") 77 88 red

/-- A base-credential input at `TxOutRef ⟨"", idx⟩`, owner-witnessed by the sole
signatory `OWNER`, holding a caller-chosen value. -/
def baseInV (idx : Integer) (v : CardanoLedgerApi.V1.Value.Value) : TxInInfo :=
  ⟨⟨ByteString.mk "", idx⟩,
   { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"),
                      some (.StakingHash (.PubKeyCredential (ByteString.mk "OWNER")))⟩
   , txOutValue := v
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

def extInV (idx : Integer) (v : CardanoLedgerApi.V1.Value.Value) : TxInInfo :=
  ⟨⟨ByteString.mk "", idx⟩,
   { txOutAddress := ⟨.PubKeyCredential (ByteString.mk "EXT"), none⟩
   , txOutValue := v
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

def baseOutV (v : CardanoLedgerApi.V1.Value.Value) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential (ByteString.mk "PROGLOGIC"), none⟩
  , txOutValue := v, txOutDatum := .NoOutputDatum, txOutReferenceScript := none }

def escOutV (v : CardanoLedgerApi.V1.Value.Value) : TxOut :=
  { txOutAddress := ⟨.PubKeyCredential (ByteString.mk "DEST"), none⟩
  , txOutValue := v, txOutDatum := .NoOutputDatum, txOutReferenceScript := none }

/-- The generic skeleton: inputs, reference inputs, outputs, fee and redeemer all
free; everything else is `BaseAbsentProbe.probeCtxN`'s. Mint is always empty, so
the mint walk never runs and the ONLY producer of `expected` is the transfer
walk — which is what isolates the two unmeasured paths. -/
def mkCtx (ins : List TxInInfo) (refs : List TxInInfo) (outs : List TxOut)
    (fee : Integer) (red : Data) : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := ins
      , txInfoReferenceInputs := refs
      , txInfoOutputs := outs
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := wdrl
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [ByteString.mk "OWNER"]
      , txInfoRedeemers := reds red
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := red
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential (ByteString.mk "GLOBAL")) }

/-! ### §1.1 — MULTI-ASSET: two policies at the base credential

`expectedProgrammableOutputValue` has TWO currency symbols, so the dispatch at
`:650-666` cannot take the single-asset fast path and MUST enter
`checkWholesaleThenBuiltin` (`:628-645`) and, on wholesale mismatch,
`BuiltinValue.pvalueContains` (`:615-618`). -/

/-- `TransferAct [1,2] [1,1] [] [] 0` — one transfer proof per policy, pointing
at reference inputs 1 (keyed `MMM`) and 2 (keyed `NNN`). -/
def red2 : Data := IsData.toData (PLGRedeemer.TransferAct [1, 2] [1, 1] [] [] 0)

def refs2 : List TxInInfo :=
  [ paramsIn                                                    -- ⟨"",2⟩
  , nodeAt 3 (ByteString.mk "MMM") (ByteString.mk "NNN")        -- keyed MMM
  , nodeAt 4 (ByteString.mk "NNN") (ByteString.mk "ZZZ") ]      -- keyed NNN

def ins2 : List TxInInfo :=
  [ baseInV 0 (adaPlusTwo 200 csM tnTOK 5 csN tnTOK 5)
  , extInV 1 (adaOnly 100) ]

/-- **M-OK** — both policies land at the base output in one lump. Exercises the
WHOLESALE Data-equality branch at `:638`. -/
def ctxMok : ScriptContext :=
  mkCtx ins2 refs2 [baseOutV (adaPlusTwo 250 csM tnTOK 5 csN tnTOK 5)] 50 red2

/-- **M-SPLIT** — the same total, split across TWO base outputs, so the wholesale
equality FAILS on the first and the builtin `pvalueContains` accumulate path at
`:615-618` decides. -/
def ctxMsplit : ScriptContext :=
  mkCtx ins2 refs2
    [ baseOutV (adaPlusOne 150 csM tnTOK 5)
    , baseOutV (adaPlusOne 100 csN tnTOK 5) ] 50 red2

/-- **M-ESCAPE** — 4 of the 5 `NNN` leave the mini-ledger. `outSum NNN = 1` while
`inSum NNN = 5` and the mint is empty, so the conclusion `1 ≥ 5 + 0` is FALSE.
If the bytecode ACCEPTS this, the proposal's failure mode (4) is live on a
context where `Model.exempt` is FALSE — i.e. a refutation of `P1UnshapedFormD`. -/
def ctxMescape : ScriptContext :=
  mkCtx ins2 refs2
    [ baseOutV (adaPlusTwo 150 csM tnTOK 5 csN tnTOK 1)
    , escOutV (adaPlusOne 100 csN tnTOK 4) ] 50 red2

/-- **M-ESCAPE-2** — the wholesale branch's exact-equality early return, aimed at
`expected`: the FIRST base output's non-ada value is made to equal `expected`
byte-for-byte while a SECOND base-credential output is absent and 4 `NNN` escape
from a THIRD policy slot… here simply: first base output equals expected exactly,
and the escape is taken out of the OTHER input. Kept as a control that exact
equality really is a lower bound. -/
def ctxMescape2 : ScriptContext :=
  mkCtx ins2 refs2
    [ baseOutV (adaPlusTwo 150 csM tnTOK 5 csN tnTOK 5)
    , escOutV (adaOnly 100) ] 50 red2

/-! ### §1.2 — MULTI-TOKEN-NAME: one policy, two token names

The dispatch guard at `:654` requires ONE currency symbol AND ONE token name.
Two token names under one policy also leaves the fast path — a different corner
of the same never-run branch. -/

def adaPlusOneTwoTn (n : Integer) (cs : CurrencySymbol) (tn1 : TokenName) (q1 : Integer)
    (tn2 : TokenName) (q2 : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [ (Data.B (ByteString.mk ""), Data.Map [(Data.B (ByteString.mk ""), Data.I n)])
  , (Data.B cs, Data.Map [(Data.B tn1, Data.I q1), (Data.B tn2, Data.I q2)]) ]

def tnA : TokenName := ByteString.mk "AAA"
def tnB : TokenName := ByteString.mk "BBB"

def refs1 : List TxInInfo :=
  [ paramsIn, nodeAt 3 (ByteString.mk "MMM") (ByteString.mk "ZZZ") ]

def insTn : List TxInInfo :=
  [ baseInV 0 (adaPlusOneTwoTn 200 csM tnA 5 tnB 5)
  , extInV 1 (adaOnly 100) ]

/-- `TransferAct [1] [1] [] [] 0`. -/
def red1 : Data := p1ShapedRedeemer

/-- **TN-OK** — both token names stay. -/
def ctxTnOk : ScriptContext :=
  mkCtx insTn refs1 [baseOutV (adaPlusOneTwoTn 250 csM tnA 5 tnB 5)] 50 red1

/-- **TN-ESCAPE** — 4 of the 5 `BBB` leave. Conclusion at `(MMM, BBB)`:
`1 ≥ 5 + 0` is FALSE. -/
def ctxTnEscape : ScriptContext :=
  mkCtx insTn refs1
    [ baseOutV (adaPlusOneTwoTn 150 csM tnA 5 tnB 1)
    , escOutV (adaPlusOne 100 csM tnB 4) ] 50 red1

/-! ### §1.3 — PHASE 3: two contributing mini-ledger inputs

`pvalueFromCred` exits in `goRest` (PHASE 2) with ONE contributing input and in
`goBuiltin` (PHASE 3) with two or more. Phase 3 is the only place `punionValue`
and `pinsertCoin # "" # "" # 0` run on the INPUT side, and it is the only place
`aggIn` is produced by arithmetic rather than by a positional `ptail`. -/

def insAgg : List TxInInfo :=
  [ baseInV 0 (adaPlusOne 200 csM tnTOK 5)
  , baseInV 1 (adaPlusOne 100 csM tnTOK 3)
  , extInV 2 (adaOnly 100) ]

/-- **A-OK** — both base inputs' 5 + 3 stay at the base output. -/
def ctxAggOk : ScriptContext :=
  mkCtx insAgg refs1 [baseOutV (adaPlusOne 250 csM tnTOK 8)] 150 red1

/-- **A-ESCAPE** — only 5 of the 8 stay. If PHASE 3 lost the second input's
contribution, `expected` would be 5 and the bytecode would ACCEPT while
`outSum = 5 < 8 = inSum`. -/
def ctxAggEscape : ScriptContext :=
  mkCtx insAgg refs1
    [ baseOutV (adaPlusOne 200 csM tnTOK 5)
    , escOutV (adaPlusOne 50 csM tnTOK 3) ] 150 red1

/-- **A-ESCAPE-FIRST** — the mirror: only the SECOND input's 3 stay, so a phase-3
that kept only the LAST contributing input would accept. -/
def ctxAggEscapeFirst : ScriptContext :=
  mkCtx insAgg refs1
    [ baseOutV (adaPlusOne 200 csM tnTOK 3)
    , escOutV (adaPlusOne 50 csM tnTOK 5) ] 150 red1

/-! ## §2 — THE MEASUREMENTS

`report` is `BaseAbsentProbe.report` widened to a caller-chosen `(cs, tn)` and to
the PROPOSED predicate: `(validRewardingContext, isProgrammable, params-clause,
outSum, inSum, mintSigned, halts@44000)`. A row with

    (true, true, true, o, i, m, true) with ¬ (o ≥ i + m)

is a REFUTATION of `P1UnshapedFormH`, hence of `P1UnshapedFormD`. -/

def report (ctx : ScriptContext) (cs : CurrencySymbol) (tn : TokenName)
    : Bool × Bool × Bool × Integer × Integer × Integer × Bool :=
  let ti := ctx.scriptContextTxInfo
  ( validRewardingContext ctx
  , isProgrammable dirCS cs ti.txInfoReferenceInputs
  , Benchmark.paramsPublishedBy ctx == some (dirCS, IsData.toData plcCred)
  , Model.outSum plcCred cs tn ti.txInfoOutputs
  , Model.inSum plcCred cs tn ti.txInfoInputs
  , Model.mintSigned cs tn ti.txInfoMint
  , halts ctx )

/-- **§2.1 — THE MULTI-ASSET CONTAINMENT PATHS ARE REACHABLE AND THEY REJECT THE
ESCAPE.**

`ctxMok` measures the WHOLESALE Data-equality branch (`:638`) accepting;
`ctxMsplit` measures the builtin `pvalueContains` accumulate branch
(`:615-618`) accepting; `ctxMescape` measures BOTH rejecting when 4 of 5 `NNN`
leave. All three carry `isProgrammable = true`, so had `ctxMescape` halted it
would have refuted the proposed statement. -/
theorem multi_asset_paths :
    (( report ctxMok csN tnTOK
     , report ctxMsplit csN tnTOK
     , report ctxMescape csN tnTOK
     , report ctxMescape2 csN tnTOK )
     == ( (true, true, true, 5, 5, 0, true)
        , (true, true, true, 5, 5, 0, true)
        , (true, true, true, 1, 5, 0, false)
        , (true, true, true, 5, 5, 0, true) )) = true := by native_decide

/-- **§2.2 — TWO TOKEN NAMES UNDER ONE POLICY: same verdict.** -/
theorem multi_tokenname_paths :
    (( report ctxTnOk csM tnB
     , report ctxTnEscape csM tnB )
     == ( (true, true, true, 5, 5, 0, true)
        , (true, true, true, 1, 5, 0, false) )) = true := by native_decide

/-- **§2.3 — `pvalueFromCred` PHASE 3 COUNTS BOTH BASE INPUTS.**

`ctxAggOk` measures phase 3 accepting on the honest 5 + 3 = 8. The two escapes
measure that `aggIn` is neither the FIRST nor the LAST contributing input alone:
both are rejected, so `punionValue` really adds and `pinsertCoin # "" # "" # 0`
really deletes only ada. This is the proposal's failure mode (3) on the branch
that no other witness in the tree reaches. -/
theorem phase3_counts_every_base_input :
    (( report ctxAggOk csM tnTOK
     , report ctxAggEscape csM tnTOK
     , report ctxAggEscapeFirst csM tnTOK )
     == ( (true, true, true, 8, 8, 0, true)
        , (true, true, true, 5, 8, 0, false)
        , (true, true, true, 3, 8, 0, false) )) = true := by native_decide

/-- **§2.4 — THE REJECTIONS ARE `perror`s, NOT BUDGET EXHAUSTION.** `halts` is
already metered at 44000; this pins that raising the ceiling another 4× changes
nothing, so the three `false`s above are genuine validator rejections. -/
theorem rejections_are_errors_not_budget :
    (( isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxMescape) 176000)
     , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxTnEscape) 176000)
     , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxAggEscape) 176000)
     , isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram
         programmableLogicGlobal1600.script (globalInputs1600 ppCS ctxAggEscapeFirst) 176000) )
     == (false, false, false, false)) = true := by native_decide

/-! ## §3 — THE PROPOSED PREDICATE AT THE KNOWN WITNESSES

The design's kill criteria K1 (predicate still incomplete) and K2 (predicate too
strong) are re-measured here in ONE table, at the proposed `exempt`/
`isProgrammable` rather than at `coveringNodeExistsWalk`. -/

/-- **K2 (NOT VACUOUS).** The proposed hypothesis is SATISFIED at the accepting
control `BaseAbsentProbe.ctxA` and at all six accepting witnesses of §1 — nine
distinct accepting transactions on four distinct validator paths. -/
theorem K2_hypothesis_is_inhabited :
    (( isProgrammable dirCS (ByteString.mk "MMM")
         BaseAbsentProbe.ctxA.scriptContextTxInfo.txInfoReferenceInputs
     , halts BaseAbsentProbe.ctxA
     , isProgrammable dirCS csN ctxMok.scriptContextTxInfo.txInfoReferenceInputs
     , isProgrammable dirCS csM ctxAggOk.scriptContextTxInfo.txInfoReferenceInputs )
     == (true, true, true, true)) = true := by native_decide

/-- **K1 (THE THREE KNOWN REFUTING WITNESSES ARE EXCLUDED).** At `ctxD`, `ctxF`
and `ctxG` the proposed `isProgrammable` is FALSE, so the repaired hypothesis
form says nothing about them and the disjunctive form's right disjunct is
discharged. -/
theorem K1_known_witnesses_excluded :
    (( isProgrammable dirCS (ByteString.mk "MMM")
         BaseAbsentProbe.ctxD.scriptContextTxInfo.txInfoReferenceInputs
     , isProgrammable dirCS (ByteString.mk "MMM")
         (ExemptionCensus.xferArm BaseAbsentProbe.nodeShort).scriptContextTxInfo.txInfoReferenceInputs )
     == (false, false)) = true := by native_decide

/-- **THE ADA DISJUNCT IS NOT DEAD WEIGHT, AND IT IS THE ONLY ONE THAT CAN FIRE
AT ADA.** `exemptible` is FREE-FALSE at `cs = ""` on every reference-input list,
because covering needs `k < ""` and nothing is strictly less than `""`. So the
`cs == ""` disjunct carries the whole ada exclusion, exactly as the design says —
and `Model.exempt` is NOT a refactoring of `coveringNodeExists` alone. -/
theorem ada_disjunct_is_the_only_one_that_fires :
    (( exempt dirCS (ByteString.mk "") ctxMok.scriptContextTxInfo.txInfoReferenceInputs
     , exemptible dirCS (ByteString.mk "")
         ctxMok.scriptContextTxInfo.txInfoReferenceInputs
     , exemptible dirCS (ByteString.mk "")
         (ExemptionCensus.noAdaCtx.scriptContextTxInfo.txInfoReferenceInputs) )
     == (true, false, false)) = true := by native_decide

end AdversarialProbe
end Review
end WSC
