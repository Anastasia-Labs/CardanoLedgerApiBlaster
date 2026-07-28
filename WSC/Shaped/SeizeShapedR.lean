-- ⚠️ PRE-#112: this module is about wsc-poc bytecode SUPERSEDED by PR #112 (main @ 2306678). Do NOT quote its results as statements about production. See WSC/IMPACT-PR112.md.
/-
WSC/Shaped/SeizeShapedR.lean — **SHAPE S1R: the NODE-REALIZABLE re-cut of
SHAPE S1**, the production clawback validator `programmableSeize` (task C2).

════════════════════════════════════════════════════════════════════════════
THE RE-CUT
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/ShapeRealizability.lean`'s `s1_class_is_empty_under_coverage`
proves SHAPE S1 empty as a class of ledger transactions: two SCRIPT withdrawals,
ONE redeemer entry. SHAPE S1R changes the redeemer map and **nothing else** — the
inputs, reference inputs, outputs, mint field, withdrawal map, validity range,
redeemer payload and script info are `WSC/Shaped/SeizeShaped.lean`'s components,
re-used verbatim, so every "NOT TRUE BY CONSTRUCTION" fact and every DEFECT-D4
scope loss of SHAPE S1 carries over unchanged and can be read from that header.

| | SHAPE S1 | **SHAPE S1R** | `seize-1-input` | `seize-2-inputs-partial-with-noise` |
|---|---|---|---|---|
| inputs (script / total) | 1 / 2 | **1 / 2** | 1 / 2 | 2 / 3 |
| mint policies | 1 | **1** | 0 | 0 |
| withdrawals (script / total) | 2 / 2 | **2 / 2** | 2 / 2 | 2 / 2 |
| redeemer entries | 1 | **4** | 3 | 4 |
| coverage `#red = #scriptIn + #mintPol + #scriptWdrl` | 1 ≠ 4 ✗ | **4 = 4 ✓** | 3 = 3 ✓ | 4 = 4 ✓ |

SHAPE S1R needs FOUR entries where `seize-1-input` needs three, for one reason
that is a feature of the shape rather than of the re-cut: **SHAPE S1 carries a
NON-EMPTY mint field** (`mintOne mCS mTn mQ`, with `mCS` a free variable distinct
from the seized policy `key` and `mQ` of free sign) so that the seize-time mint is
real and `WSC.mintOf` is load-bearing in P2's containment conjunct. Both seize
goldens have an EMPTY mint. A minted policy is a script witness, so coverage adds
a `Minting mCS` entry. `validMintValue` forbids the ada symbol in the mint field
(`CardanoLedgerApi/V3/Contexts.lean:836-848`, the fold starts at `adaSymbol` and
demands `prev_cs < cs`), so `mCS` is never ada and the entry is never an EXTRA
redeemer.

════════════════════════════════════════════════════════════════════════════
THE FOUR ENTRIES, AND WHY EACH IS FORCED
════════════════════════════════════════════════════════════════════════════
1. `Spending ⟨"",0⟩` — input 0 sits at `ScriptCredential mlH`. When `mlH = plc`
   (the mini-ledger case the whole property is about) this input is a mini-ledger
   UTxO and `WSC.LR_SPEND_RUNS_VALIDATOR` runs the base validator on it, which is
   exactly the route by which `ShapeRealizability.t1_class_is_empty` is
   UNCONDITIONAL for SHAPE T1. SHAPE S1R carries the entry, so that route is shut.
   Input 1 is at a PUBKEY address and needs none.
2. `Minting mCS` — see above.
3. `Rewarding (ScriptCredential w0)` — the seize validator's OWN purpose. Its
   payload IS `seizeShapedRedeemer`, so `validScriptInfo`'s
   `findRedeemer purpose … == some ctx.scriptContextRedeemer` holds
   (`CardanoLedgerApi/V3/Contexts.lean:1035-1037`).
4. `Rewarding (ScriptCredential w1)` — the ISSUER-LOGIC script the validator
   requires at `issuerWdrlIdx = 1`: condition 3,
   `pisScriptInvokedEntries # directoryNodeDatumFIssuerLogicScript #
   withdrawalEntries` (ProgrammableLogicBase.hs:1298), which forces `w1` to equal
   the node datum's `ilsH`. A script withdrawal the validator itself demands, so
   its redeemer entry is not optional.

Both `Rewarding` credentials must therefore stay SCRIPT credentials: the task's
"pubkey wherever the validator does not dereference a script" has no room here.

`spRed`, `mtRed` and `ilRed` — the base validator's, the mint policy's and the
issuer-logic script's own redeemer payloads — are three NEW FREE `ByteString`
leaves carried as `Data.B`. The seize validator destructures `ptxInfo'redeemers`
in its `PTxInfo` pattern (ProgrammableLogicBase.hs:1267) and never uses it, so
none of the three is ever forced; that is also why the re-cut costs no CEK steps.

REDEEMER-MAP ORDER: `Spending < Minting < Rewarding` under CLAB's corrected
`ltScriptPurpose` for every assignment, and `Rewarding w0 < Rewarding w1` under
the `w0 < w1` that `validWithdrawals` already forces on the withdrawal map. So
`validRedeemerMap` adds NO side condition SHAPE S1 did not already carry.
-/
import WSC.Prep.Seize
import WSC.Shaped.Shape
import WSC.Shaped.SeizeShaped
import WSC.Redeemer
import WSC.Realizability
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol ScriptContext ScriptHash
                          StakingCredential TokenName TxInInfo TxOutRef TxInfo
                          ScriptPurpose Withdrawals rewardingInputs findRedeemer)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- **SHAPE S1R's redeemer map — the whole content of the re-cut.** One entry per
script witness, in `ltScriptPurpose` order. -/
def seizeRRedeemerMap (mCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (spRed mtRed ilRed : ByteString) : List (ScriptPurpose × Data) :=
  [ (.Spending ⟨ByteString.mk "", 0⟩, Data.B spRed)
  , (.Minting mCS, Data.B mtRed)
  , (.Rewarding (.ScriptCredential w0), seizeShapedRedeemer)
  , (.Rewarding (.ScriptCredential w1), Data.B ilRed) ]

/-- **SHAPE S1R.** Every component but the redeemer map is
`WSC/Shaped/SeizeShaped.lean`'s, re-used by name — so the two shapes are
byte-identical except in `txInfoRedeemers`. -/
def seizeRCtx
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ seizeShapedIn0 mlH inStk i0Ada mlCS mlTn i0Qty dIn
          , seizeShapedIn1 wallet i1Ada i1CS i1Tn i1Qty ]
      , txInfoReferenceInputs :=
          [ seizeShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , seizeShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ seizeShapedOut0 mlH oStk o0Ada mlCS mlTn o0Qty dOut
          , seizeShapedOut1 escH o1Ada o1CS o1Tn o1Qty ]
      , txInfoFee := fee
      , txInfoMint := mintOne mCS mTn mQ
      , txInfoTxCerts := []
      , txInfoWdrl := seizeShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := seizeShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-! ### REDEEMER COVERAGE AT SHAPE S1R — for every leaf assignment -/

section Find
variable (mCS : CurrencySymbol) (w0 w1 : ScriptHash) (spRed mtRed ilRed : ByteString)

theorem seizeR_findSpending :
    findRedeemer (.Spending ⟨ByteString.mk "", 0⟩) (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed)
      = some (Data.B spRed) := by
  rw [seizeRRedeemerMap, Realizability.findRedeemer_cons_hit]

theorem seizeR_findMinting :
    findRedeemer (.Minting mCS) (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed)
      = some (Data.B mtRed) := by
  rw [seizeRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.spending_beq_minting ..),
    Realizability.findRedeemer_cons_hit]

theorem seizeR_findRewarding0 :
    findRedeemer (.Rewarding (.ScriptCredential w0))
      (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) = some seizeShapedRedeemer := by
  rw [seizeRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.spending_beq_rewarding ..),
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_hit]

end Find

theorem seizeR_findRewarding1 (mCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (spRed mtRed ilRed : ByteString) (hne : w0 ≠ w1) :
    findRedeemer (.Rewarding (.ScriptCredential w1))
      (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) = some (Data.B ilRed) := by
  rw [seizeRRedeemerMap,
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.spending_beq_rewarding ..),
    Realizability.findRedeemer_cons_miss _ _ _ _ (Realizability.minting_beq_rewarding ..),
    Realizability.findRedeemer_cons_miss _ _ _ _
      (Realizability.rewarding_beq_rewarding_of_ne w0 w1 (Ne.symm hne)),
    Realizability.findRedeemer_cons_hit]

/-- Unconditional form of `seizeR_findRewarding1`. -/
theorem seizeR_findRewarding1_ne (mCS : CurrencySymbol) (w0 w1 : ScriptHash)
    (spRed mtRed ilRed : ByteString) :
    findRedeemer (.Rewarding (.ScriptCredential w1))
      (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none := by
  by_cases h : w0 = w1
  · subst h; rw [seizeR_findRewarding0]; exact Option.noConfusion
  · rw [seizeR_findRewarding1 _ _ _ _ _ _ h]; exact Option.noConfusion

section Cover
variable (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
         (dIn : ByteString)
         (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
         (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
         (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
         (mCS mTn : ByteString) (mQ : Integer)
         (pHash pCS pTn : ByteString) (pAda pQty : Integer)
         (dirCS plc glc slc : ByteString)
         (nHash nCS nTn : ByteString) (nAda nQty : Integer)
         (key next tlsH ilsH gsCS : ByteString)
         (w0 w1 : ByteString) (a0 a1 : Integer)
         (spRed mtRed ilRed : ByteString) (fee : Integer)

private abbrev sCtx : ScriptContext :=
  seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
    oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
    pHash pCS pTn pAda pQty dirCS plc glc slc
    nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee

/-- **SHAPE S1R's BOTH script withdrawals are covered**, under the `w0 ≠ w1` that
`validWithdrawals` forces. -/
theorem seizeR_wdrl_covered (hne : w0 ≠ w1) :
    Realizability.WdrlCovered
      (sCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro h n hmem
  simp [sCtx, seizeRCtx, seizeShapedWdrl] at hmem
  show findRedeemer (.Rewarding (.ScriptCredential h))
        (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [seizeR_findRewarding0]; exact Option.noConfusion
  · rw [seizeR_findRewarding1 _ _ _ _ _ _ hne]; exact Option.noConfusion

/-- **SHAPE S1R's ONE script input is covered.** Input 0 sits at
`ScriptCredential mlH` and the redeemer map's entry 0 is `Spending ⟨"",0⟩`, its
`TxOutRef`. Input 1 is at a pubkey address. This is the clause that shuts the
UNCONDITIONAL emptiness route of `ShapeRealizability.t1_class_is_empty`. -/
theorem seizeR_spend_covered :
    Realizability.SpendCovered
      (sCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro i hin hscript
  simp [sCtx, seizeRCtx] at hin
  rcases hin with rfl | rfl
  · show findRedeemer (.Spending ⟨ByteString.mk "", 0⟩)
          (seizeRRedeemerMap mCS w0 w1 spRed mtRed ilRed) ≠ none
    rw [seizeR_findSpending]; exact Option.noConfusion
  · simp [seizeShapedIn1, CardanoLedgerApi.V2.isScriptCredentialAddress] at hscript

/-- **SHAPE S1R's single minted policy is covered.** -/
theorem seizeR_mint_covered :
    Realizability.MintCovered
      (sCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 spRed mtRed ilRed fee) := by
  intro cs m hmem
  simp [sCtx, seizeRCtx, Shape.mintOne] at hmem
  obtain ⟨rfl, -⟩ := hmem
  show findRedeemer (.Minting _) (seizeRRedeemerMap _ w0 w1 spRed mtRed ilRed) ≠ none
  rw [seizeR_findMinting]; exact Option.noConfusion

end Cover

/-- Parameter evidence unchanged from WSC/Prep/Seize.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1290-1291). -/
def seizeRInputs
    (protocolParamsCS : CurrencySymbol)
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString)
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    (oStk : ByteString) (o0Ada o0Qty : Integer) (dOut : ByteString)
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer)
    (mCS mTn : ByteString) (mQ : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (spRed mtRed ilRed : ByteString)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (seizeRCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 spRed mtRed ilRed fee)

#prep_uplc appliedSeizeRShaped3800 programmableSeize seizeRInputs 3800

end WSC
