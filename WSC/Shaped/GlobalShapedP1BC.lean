/-
WSC/Shaped/GlobalShapedP1BC.lean — **the NODE-REALIZABLE re-cut of SHAPES T3 and
T4: SHAPE T3R (containment dispatch PATHS B/C) and SHAPE T4R (input-side builtin
accumulation)** (task H2).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
`poutputsContainExpectedValueAtCred` (ProgrammableLogicBase.hs:518-670 at
wsc-poc main `2306678`) dispatches containment THREE ways:

* **PATH A** — `hasAtLeastAssetInProgOutputs` (:567-589), the single-asset
  accumulate-scan. Taken iff the expected value is exactly ONE currency symbol
  carrying exactly ONE token name (the guard at :654:
  `(pnull # csPairsRest) #&& (pelimList (\_ tnRest -> pnull # tnRest) False tnPairs)`).
* **PATH B** — the wholesale `Data`-equality fast path inside
  `checkWholesaleThenBuiltin` (:628-645): at the FIRST output whose payment
  credential is `progLogicCred`, `(pmapData # (ptail # (pasMap # txOutValueData)))
  #== expectedMapData` — one `equalsData` on the output's non-ada value map.
  True ⇒ accept immediately.
* **PATH C** — `checkByBuiltinContains` (:615-618): the CIP-153 builtin
  `pvalueContains` applied to `accumulateOutputsAtCred` (:599-614, which sums
  EVERY mini-ledger output with `punionValue`/`punValueData`) against the
  expected value. Reached when PATH B's equality fails, or when the output walk
  finds no mini-ledger output at all (the `pelimList` base case, :644).

ARCHITECTURE.md Tier 3.1 requires each of the three to independently imply the
aggregate bound. Until task H2 only PATH A was reachable at UPLC: SHAPES
T1R/T2R/T6R/T7R/T8R all carry a single-token expected value.

SHAPE T3 (`WSC/Shaped/GlobalShapedP1.lean:416-500`) was cut for exactly this
gap — two token names per policy — but it is **PRE-RE-CUT and provably
unbuildable on a node**: 1 script input + 0 mint policies + 2 script withdrawals
means Conway's `hasExactSetOfRedeemers` demands 3 redeemer entries and SHAPE T3
supplies 1 (audit **F2**; the count is spelled out in
`WSC/Shaped/Probe/T3PrepFAILS.lean`). A P1 theorem there would range over an
EMPTY class. SHAPE T4 (`WSC/Shaped/GlobalShapedP1Agg.lean:76-135`) is unbuildable
for the same reason, worse: 2 script inputs + 2 script withdrawals ⇒ 4 entries
demanded, 1 supplied.

The two shapes below are those transactions with a redeemer map that COVERS
every script witness the transaction needs. **Nothing else changes**: every
amount, policy, credential and hash that was symbolic stays symbolic, and P1's
two design requirements — a NON-BASE input and a NON-BASE output, so `isBalanced`
alone cannot force the conclusion — are preserved verbatim.

════════════════════════════════════════════════════════════════════════════
THE TWO RE-CUTS, COUNTED
════════════════════════════════════════════════════════════════════════════
| shape | old cut | new cut | needed-script coverage |
|---|---|---|---|
| **T3R** (P1, PATHS B/C) | 2 script wdrl, **1** redeemer | 2 script wdrl, **3** redeemers | input `⟨"",0⟩` at `ScriptCredential plc` ⟶ `Spending ⟨"",0⟩`; wdrls `w0`,`w1` ⟶ two `Rewarding`; no mint |
| **T4R** (P1, input-side builtin accumulation) | 2 script wdrl, **1** redeemer | 2 script wdrl, **4** redeemers | inputs `⟨"",0⟩` AND `⟨"",1⟩` at `ScriptCredential plc` ⟶ two `Spending`; wdrls `w0`,`w1` ⟶ two `Rewarding`; no mint |

T3R reuses `p1RRedeemers` verbatim — SHAPE T3's input/withdrawal skeleton is
SHAPE T1's, so its coverage obligation is identical to SHAPE T1R's. T4R needs a
new 4-entry map because it spends a SECOND script input.

Ascending in `ltScriptPurpose` (`CardanoLedgerApi/V3/Contexts.lean:101-121`):
`Spending ⟨"",0⟩ < Spending ⟨"",1⟩` (TxOutRef order, same tx id, `0 < 1`),
`Spending < Rewarding`, and `Rewarding (ScriptCredential w0) < Rewarding
(ScriptCredential w1)` iff `w0 < w1` — which `validWithdrawals` already forces
on the withdrawal map itself.

════════════════════════════════════════════════════════════════════════════
WHY THE WITHDRAWAL MAP STAYS TWO-SCRIPT (lever (i) of GlobalShapedR does not apply)
════════════════════════════════════════════════════════════════════════════
Both shapes carry `transferWdrlIdxs = [1]`, and the transfer walk's
positive-proof branch requires
`directoryNodeDatumFTransferLogicScript #== pfstBuiltin # (phead #
(pdropList # 1 # withdrawalEntries))` (:913-915). The node datum's
`transferLogicScript` is a `ScriptCredential`, so withdrawal entry 1 MUST be a
script credential — a pubkey entry there would make the accepting branch of
these very shapes unreachable. Both script withdrawals therefore get `Rewarding`
entries, exactly as at SHAPE T1R.

════════════════════════════════════════════════════════════════════════════
WHAT EACH SHAPE ACTUALLY EXERCISES — the claim, and where it is BACKED
════════════════════════════════════════════════════════════════════════════
**SHAPE T3R leaves PATH A, and this is forced by the shape, not assumed.** The
mint field is EMPTY, so `expectedProgrammableOutputValue` is
`totalProgTokenValue_` outright — the `pif (pnull # pto (pto
mintValueNoGuarantees))` at `:1226-1229` takes its THEN branch, so there is no
`punionValue` and no filter in the transfer path at all. And
`pcheckTransferLogicAndGetProgrammableValue` (`:855-935`) `pcons`es each
currency-symbol pair through UNCHANGED when its positive proof passes
(`:917-926`) — it selects whole policies, never individual token names. So the
expected value is literally the mini-ledger input's non-ada value map: ONE
currency symbol with TWO token names. The PATH A guard at `:654` is FALSE
and `checkWholesaleThenBuiltin` runs. Executable evidence
that this is what the bytecode really does — two rejections that a single-asset
scan could not produce — is in `WSC/Props/Shaped/P1ShapedBC.lean`
(`T3R_not_path_A`).

**Which of B or C then runs is a function of the leaves**, and the theorem
quantifies over both:
* PATH B accepts iff output 0's non-ada map equals the expected map
  byte-for-byte, i.e. iff `qOut0 = qIn0 ∧ qOut1 = qIn1`;
* otherwise PATH C runs.
`P1ShapedBC.lean` pins one witness of each. It PROVES the PATH C one is on PATH
C (`T3R_pathC_is_taken`, a two-witness argument), and evaluates PATH B's own
condition in ground-truth vocabulary (`T3R_pathB_condition`) while separating its
EXECUTION only by cost (K 1936 vs 2228) — because on ledger-valid contexts with
node-representable quantities PATH B implies PATH C, so no accept/reject test can
isolate it. Read that module's header before quoting either.

**SHAPE T4R enters `pvalueFromCred`'s PHASE 3.** With ONE contributing input the
walk finishes in PHASE 2 `goRest` (:411-427) and produces the input value by
`ptail # (pasMap # firstVd)` — a positional drop of the ada entry, no arithmetic.
With TWO it enters PHASE 3 `goBuiltin` (:396-410), which converts each input
value with `punValueData`, merges with `punionValue`, and bridges back through
`pasMap # (pvalueData # (pinsertCoin # "" # "" # 0 # acc))`. The mini-ledger
input total is then the output of real builtin addition on symbolic quantities.
T4R keeps SHAPE T4's single token name, so its containment dispatch is PATH A:
T4R is the INPUT-side axis, T3R is the OUTPUT-side one.
-/
import WSC.Shaped.GlobalShapedP1
import WSC.Shaped.GlobalShapedP1Agg
import WSC.Shaped.GlobalShapedR
import WSC.Shaped.Shape
import WSC.Redeemer

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash ScriptPurpose
                          TokenName TxInInfo TxOutRef TxInfo MintValue RedeemerMap
                          Withdrawals rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-! ## §0 The pieces of SHAPE T3R, named

SHAPE T3 spells its four value-carrying UTxOs inline
(`WSC/Shaped/GlobalShapedP1.lean:422-474`). They are given names here so the
re-cut context, the witnesses and the realizability proofs can all refer to the
same definitions; the `Data` they build is unchanged. -/

/-- SHAPE T3/T3R's mini-ledger input (`TxOutRef ⟨"",0⟩`): at the base credential
`ScriptCredential plc`, owner-witnessed by the signatory `owner`, carrying ada
plus ONE policy with TWO token names. -/
def p1TwoBaseIn (plc owner : ByteString) (inAda : Integer)
    (cs tn0 tn1 : ByteString) (qIn0 qIn1 : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential plc, some (.StakingHash (.PubKeyCredential owner))⟩
   , txOutValue := adaPlusTwoTn inAda cs tn0 tn1 qIn0 qIn1
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- SHAPE T3/T3R's EXTERNAL input (`TxOutRef ⟨"",1⟩`), at a pubkey address:
the ledger-legal source that makes an escape balance. `pvalueFromCred` skips it
(:443/:392-410 `withContributing`'s payment gate). -/
def p1TwoExtIn (ext : ByteString) (in2Ada : Integer)
    (cs tn0 tn1 : ByteString) (qX0 qX1 : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.PubKeyCredential ext, none⟩
   , txOutValue := adaPlusTwoTn in2Ada cs tn0 tn1 qX0 qX1
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- SHAPE T3/T3R's mini-ledger OUTPUT — the one the containment check has to
find, and the one PATH B's wholesale `Data` equality compares against. -/
def p1TwoBaseOut (plc : ByteString) (outAda : Integer)
    (cs tn0 tn1 : ByteString) (qOut0 qOut1 : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential plc, none⟩
  , txOutValue := adaPlusTwoTn outAda cs tn0 tn1 qOut0 qOut1
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- SHAPE T3/T3R's ESCAPE output: a pubkey address holding the same policy and
both token names. Without it `isBalanced` alone would force the conclusion. -/
def p1TwoEscOut (dest : ByteString) (escAda : Integer)
    (cs tn0 tn1 : ByteString) (qE0 qE1 : Integer) : TxOut :=
  { txOutAddress := ⟨.PubKeyCredential dest, none⟩
  , txOutValue := adaPlusTwoTn escAda cs tn0 tn1 qE0 qE1
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-! ## §1 SHAPE T3R — the re-cut of SHAPE T3 (containment PATHS B/C) -/

/-- **SHAPE T3R.** SHAPE T3 verbatim
(`WSC/Shaped/GlobalShapedP1.lean:418-474`, whose FIXED/SYMBOLIC split and whose
"WHY THE MINIMAL P1 SHAPE IS NOT 1 INPUT, 1 OUTPUT" stanza both still apply word
for word) with exactly ONE change: `txInfoRedeemers` grows from 1 entry to the
3-entry `p1RRedeemers`, so the `ScriptCredential plc` input and BOTH script
withdrawals are covered and the class is node-realizable.

`rBase` and `rTls` are the two new free Integers in the redeemer slots the
running validator never reads. -/
def p1BCShapedCtx
    (cs tn0 tn1 : ByteString)
    (plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rTls : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1TwoBaseIn plc owner inAda cs tn0 tn1 qIn0 qIn1
          , p1TwoExtIn ext in2Ada cs tn0 tn1 qX0 qX1 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1TwoBaseOut plc outAda cs tn0 tn1 qOut0 qOut1
          , p1TwoEscOut dest escAda cs tn0 tn1 qE0 qE1 ]
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := p1RRedeemers w0 w1 rBase rTls p1ShapedRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- Parameter evidence as `WSC/Prep/Global1600.lean`: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1176-1177). -/
def p1BCShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn0 tn1 : ByteString)
    (plc owner : ByteString) (inAda qIn0 qIn1 : Integer)
    (ext : ByteString) (in2Ada qX0 qX1 : Integer)
    (outAda qOut0 qOut1 : Integer)
    (dest : ByteString) (escAda qE0 qE1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rTls : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1BCShapedCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rTls fee)

/-! ## §2 SHAPE T4R — the re-cut of SHAPE T4 (input-side builtin accumulation) -/

/-- The redeemer map of SHAPE T4R: TWO `Spending` entries (the shape spends two
script inputs, `⟨"",0⟩` and `⟨"",1⟩`) then the two `Rewarding` entries covering
the two script withdrawals. Ascending: `Spending ⟨"",0⟩ < Spending ⟨"",1⟩ <
Rewarding w0 < Rewarding w1`, the last step iff `w0 < w1`. -/
def p1AggRRedeemers (w0 w1 : ScriptHash) (rBase0 rBase1 rTls : Integer)
    (own : Data) : RedeemerMap :=
  [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I rBase0)
  , (.Spending ⟨ByteString.mk "", 1⟩, Data.I rBase1)
  , (.Rewarding (.ScriptCredential w0), own)
  , (.Rewarding (.ScriptCredential w1), Data.I rTls) ]

/-- **SHAPE T4R.** SHAPE T4 verbatim
(`WSC/Shaped/GlobalShapedP1Agg.lean:76-135`) with exactly one change: the
redeemer map grows from 1 entry to the 4-entry `p1AggRRedeemers`. Two mini-ledger
inputs with INDEPENDENT symbolic quantities, so `pvalueFromCred` runs its PHASE 3
`goBuiltin` and the input total is produced by the CIP-153 builtins
`punValueData`/`punionValue`/`pinsertCoin`/`pvalueData`. -/
def p1AggRCtx
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase0 rBase1 rTls : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn plc owner inAda0 cs tn qIn0
          , p1ShapedBaseIn2 plc owner inAda1 cs tn qIn1
          , p1ShapedExtIn2 ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda cs tn qOut
          , p1ShapedEscOut dest escAda cs tn qEsc ]
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := p1AggRRedeemers w0 w1 rBase0 rBase1 rTls p1ShapedRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1AggRInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda0 qIn0 inAda1 qIn1 : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase0 rBase1 rTls : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1AggRCtx cs tn plc owner inAda0 qIn0 inAda1 qIn1 ext in2Ada qIn2
        outAda qOut dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1
        rBase0 rBase1 rTls fee)

/-- AUDIT, spelled out: SHAPE T3R's redeemer map is the SHAPE T1R map, and SHAPE
T4R's has the second `Spending` entry the second script input needs. Both are
strictly ascending under `ltScriptPurpose` for the concrete leaves below. -/
theorem p1AggRRedeemers_eq (w0 w1 : ScriptHash) (rBase0 rBase1 rTls : Integer) (own : Data) :
    p1AggRRedeemers w0 w1 rBase0 rBase1 rTls own =
      [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I rBase0)
      , (.Spending ⟨ByteString.mk "", 1⟩, Data.I rBase1)
      , (.Rewarding (.ScriptCredential w0), own)
      , (.Rewarding (.ScriptCredential w1), Data.I rTls) ] := rfl

end WSC
