-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Shaped/GlobalShapedP1.lean — the SHAPES for **P1 (containment)** against the
production transfer validator `programmableLogicGlobal` (task V1).

⚠ NODE-REALIZABILITY (task C1): SHAPES T1/T2 below are EMPTY as classes of
ledger transactions (one-entry redeemer map vs a script-credential input and two
script withdrawals). The re-cut, redeemer-covered versions are SHAPES T1R/T2R in
WSC/Shaped/GlobalShapedR.lean; the shapes here are kept because the emptiness
proofs and the historical P1 theorems are stated over them.

Mechanism (i) of WSC/Shaped/Shape.lean: the shape is baked into the `#prep_uplc`
inputs function, so the CEK symbolic run sees a closed `Data` SKELETON and only
the scalar leaves stay symbolic. Vocabulary and doctrine: WSC/Shaped/Shape.lean.

════════════════════════════════════════════════════════════════════════════
WHY THE MINIMAL P1 SHAPE IS NOT "1 INPUT, 1 OUTPUT"
════════════════════════════════════════════════════════════════════════════
The task brief suggests starting from one mini-ledger input and one mini-ledger
output. That shape is UNUSABLE for P1, and the reason is a ledger rule, not a
solver limit:

`validRewardingContext` includes `isBalanced`
(CardanoLedgerApi/V3/Contexts.lean:1180-1187), i.e.
`merge (withoutLovelace valueSpent) txInfoMint == withoutLovelace valueProduced`.
With exactly one input and one output — both carrying the policy — the balance
rule ALONE forces `qOut = qIn + mint`, so `outAtBase ≥ inAtBase + mintOf` would
be HYPOTHESIS-IMPLIED and the theorem worthless (arch Tier 0.1 anti-tautology).

Containment is a statement about the MINI-LEDGER sub-balance, so the shape must
give the transaction a way to move the policy OUT of the mini-ledger that the
ledger itself permits. The minimal such shape has

  * a second INPUT at a NON-base (pubkey) address carrying the same policy — the
    external source that funds a would-be escape, and
  * a second OUTPUT at a NON-base (pubkey) address carrying the same policy — the
    escape route itself.

Then the ledger balance only says `qIn + qIn2 = qOut + qEsc`, which is satisfied
both by containment-respecting assignments (`qOut ≥ qIn`) and by escaping ones
(`qOut < qIn`, the difference landing in `qEsc`). The theorem therefore has to be
earned from the bytecode, and `P1ShapedWitness.exec_rejects_escape` in
WSC/Props/Shaped/P1Shaped.lean exhibits a ledger-legal SHAPE-T1 context that
violates containment and shows the real CEK rejecting it.

════════════════════════════════════════════════════════════════════════════
SHAPE T1 — "one mini-ledger input, one mini-ledger output, one registered
policy, no mint, with an external source and an escape route"
════════════════════════════════════════════════════════════════════════════
FIXED (the published scope — quote this with any theorem stated against this
prep):
* purpose REWARDING, own credential = `ScriptCredential w0`; script info
  `RewardingScript (ScriptCredential w0)`;
* exactly 2 inputs, in this order:
  - index 0: at `ScriptCredential plc` (the mini-ledger base credential the
    params datum publishes) with staking credential
    `StakingHash (PubKeyCredential owner)` and `owner` the sole signatory, so
    `pvalueFromCred`'s owner-witness gate (:432-434) is CLEARED and the input
    genuinely contributes; value = ada + exactly one policy/token;
  - index 1: at `PubKeyCredential ext`, value = ada + the SAME policy/token —
    the external source (skipped by `pvalueFromCred`, :443);
* exactly 2 reference inputs: index 0 the protocol-params node, index 1 the
  candidate directory node; both at SCRIPT addresses, both with INLINE datums,
  both ada plus exactly one other policy carrying exactly one token name;
* exactly 2 outputs, in this order:
  - index 0: at `ScriptCredential plc` — the mini-ledger output;
  - index 1: at `PubKeyCredential dest` — the escape route;
  both ada plus exactly one policy/token, the SAME policy/token;
* mint field EMPTY (pure transfer). So the mint walk is never called
  (:1219-1222) and `mintOf = 0`; the SIGNED form is still what is stated, and
  SHAPE T2 below carries a nonzero symbolic mint;
* withdrawal map: exactly 2 entries, both SCRIPT credentials;
* exactly 1 redeemer-map entry, for the own `Rewarding` purpose;
* empty certificate / datum / vote / proposal lists; exactly 1 signatory;
* redeemer = `TransferAct [1] [1] [] [] 0` (FIVE fields since PR #112,
  `ownerWdrlIdxs` third and empty — this shape's mini-ledger input is
  pubkey-owner-witnessed, so it is never read): the transfer proof points at reference
  index 1 (the directory node), the transfer withdrawal index at withdrawal
  entry 1, no mint proofs, params at reference index 0. All four are
  self-validating hints re-checked by `pcheckedDrop`/`phead` plus the branch
  conditions — exactly the fields Shape.lean's doctrine permits to fix;
* the `TxOutRef`s are `⟨"",0⟩`, `⟨"",1⟩` (inputs) and `⟨"",2⟩`, `⟨"",3⟩`
  (reference inputs); tx id `""`; validity interval the finite closed `[0,1]`.

SYMBOLIC — in particular EVERY quantity the postcondition talks about:
* `qIn` (mini-ledger input amount), `qOut` (mini-ledger output amount), `qIn2`
  (external input amount), `qEsc` (escape amount) — the containment inequality
  is about exactly these and none of them is fixed;
* `cs` (the policy) and `tn` (the token name);
* `plc` (the mini-ledger base script hash — read out of the params datum, and
  the payment credential of input 0 and output 0), `owner`, `ext`, `dest`;
* `dirCS` (the directory policy the params datum publishes) and `nCS` (the
  directory node's first non-ada value policy) — DIFFERENT variables, so the
  node's authentication has to be earned;
* `key`, `next` (the node's interval), `tlsH` (its transfer-logic script hash),
  `w0`, `w1` (the withdrawal credentials) — so the positive-proof branch's three
  conjuncts (:911-917) are all earned;
* `pCS` (the params node's first non-ada policy) vs the script parameter `ppCS`
  — again different variables, so `pparamsAtRefIdx`'s `phasCSH` gate (:832) is
  not pre-satisfied;
* every ada amount, every withdrawal amount, the fee, all hashes.

WHICH CONTAINMENT DISPATCH PATH SHAPE T1 EXERCISES (arch Tier 3.1). After the
transfer walk the expected value is a single currency symbol with a single token
name, so the dispatch at ProgrammableLogicBase.hs:676-699 takes **PATH A**, the
single-asset accumulate-scan `hasAtLeastAssetInProgOutputs` (:604-618). SHAPE T3
below has a TWO-token-name expected value and therefore takes the OTHER arm,
`checkWholesaleThenBuiltin` — **PATH B then PATH C** (:648-674 / :619-647).

════════════════════════════════════════════════════════════════════════════
SHAPE T2 — SHAPE T1 plus a NONZERO SYMBOLIC MINT (the signed form bites)
════════════════════════════════════════════════════════════════════════════
Identical to T1 except: `txInfoMint = [(cs, {tn: q})]` with `q` a free Integer of
UNCONSTRAINED SIGN, and the redeemer is `TransferAct [1] [1] [Member] 0`. The
mint walk (:976-1026) now runs, the `Member` proof retains the entry (:993-994),
`pcurrencyPairsUnionFast` adds it to the transfer value (:1235-1243) and
`pfilterPositiveCurrencyPairs` (:257-298) drops the slot if the sum is `≤ 0`.
This is the shape on which ARCHITECTURE §3-P1's `mintPos` form is REFUTED and the
signed form `outAtBase ≥ inAtBase + mintOf` is the one that holds; see
`P1_T2` and `P1ShapedWitness.mintPos_form_REFUTED` in
WSC/Props/Shaped/P1Shaped.lean.

════════════════════════════════════════════════════════════════════════════
SHAPE T3 — TWO TOKEN NAMES (the other containment dispatch arm)
════════════════════════════════════════════════════════════════════════════
Identical to T1 except every value carrying the policy carries TWO token names
`tn0 < tn1` with independent symbolic quantities. The expected value then has one
currency symbol with two token names, so the dispatch takes
`checkWholesaleThenBuiltin` (Path B, falling through to Path C).

**SHAPE T3 HAS NO WORKING PREP.** `#prep_uplc` over it emits a kernel-ill-typed
term at the CIP-153 `pvalueContains` residual — an upstream Blaster defect,
reproduced with the full error text in WSC/Shaped/Probe/T3PrepFAILS.lean and
recorded in WSC/status-fragments/V1-P1-shaped.md. The shape definitions below are
kept because they document the intended second dispatch arm and because the
defect must stay reproducible. The shapes that DO prep are T1/T2 (here),
T6/T7 (WSC/Shaped/GlobalShapedP1Out.lean) and, for K measurement only,
T4/T5 (WSC/Shaped/GlobalShapedP1Agg.lean).
-/
import WSC.Shaped.Shape
import WSC.Redeemer
import WSC.Model.Ground
import CardanoLedgerApi.V3

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash
                          TokenName TxInInfo TxOutRef TxInfo MintValue
                          Withdrawals rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-! ## Shared pieces -/

/-- Canonical `Value` with ada plus ONE policy carrying TWO token names (SHAPE
T3). Sorted iff `"" < cs` and `tn0 < tn1`, which `validTxOutValue` demands. -/
def adaPlusTwoTn (n : Integer) (cs : CurrencySymbol) (tn0 tn1 : TokenName)
    (q0 q1 : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [ (Data.B adaCS, Data.Map [(Data.B adaTN, Data.I n)])
  , (Data.B cs, Data.Map [(Data.B tn0, Data.I q0), (Data.B tn1, Data.I q1)]) ]

/-- SHAPE T1/T3's redeemer: `TransferAct [1] [1] [] [] 0` — one transfer proof
naming reference index 1, one withdrawal-index cursor naming withdrawal entry 1,
an EMPTY owner-withdrawal-index list, NO mint proofs, params at reference index 0.
Built through WSC/Redeemer.lean's audited `IsData PLGRedeemer` mirror
(ProgrammableLogicBase.hs:1039-1055 for the field order).

**PR #112 (main @ 2306678): FIVE fields, `ownerWdrlIdxs` THIRD.** Unlike SHAPES
G1/G6, this shape DOES have a mini-ledger input — `p1ShapedBaseIn` sits at
`ScriptCredential plc`, which is `progLogicCred`, so `withContributing`'s payment
gate (ProgrammableLogicBase.hs:351-352) PASSES and the owner-witness arm really
runs. `[]` is still forced, and forced for a sharper reason: that input's staking
credential is `StakingHash (PubKeyCredential owner)` with `owner` in
`txInfoSignatories`, so `pasConstr`'s tag test at `:371` sees tag 0 and takes the
PUBKEY branch `:372-376` (`ptxSignedByPkh`), which calls `k resolvedOutValueData
idxs` WITHOUT advancing the cursor and without touching `withdrawalEntries`. Only
the script branch `:386-393` consumes an index. A non-empty list here would be
inert, not merely wrong. Corroborated externally: all four regenerated transfer
goldens carry `ownerWdrlIdxs = []` (WSC/Goldens/RedeemerGate.lean:286-332), and
they too spend pubkey-stake-owned mini-ledger inputs.

⚠ COVERAGE CONSEQUENCE, stated not papered over: because every shape in this
library witnesses its mini-ledger owner by SIGNATURE, no shaped theorem exercises
the new indexed script-owner lookup at `:386-393`. That path is covered instead by
SHAPE T8R (WSC/Shaped/GlobalShapedR.lean §7), which was cut for exactly this gap. -/
def p1ShapedRedeemer : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [] 0)

/-- AUDIT: the shaped redeemer's `Data` encoding, spelled out. FIVE fields
post-#112; `ownerWdrlIdxs` is the third element, `Data.List []`. -/
theorem p1ShapedRedeemer_eq :
    p1ShapedRedeemer =
      Data.Constr 0 [Data.List [Data.I 1], Data.List [Data.I 1], Data.List [],
                     Data.List [], Data.I 0] := by
  native_decide

/-- SHAPE T2's redeemer: `TransferAct [1] [1] [] [Member] 0` — the extra `Member`
mint proof the nonzero mint field requires (:1018 errors without it).
`MintProof.Member = 0` (:1030-1037). FIVE fields post-#112; see
`p1ShapedRedeemer` for why `ownerWdrlIdxs = []` is forced. -/
def p1ShapedRedeemerMint : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [] [MintProof.Member] 0)

theorem p1ShapedRedeemerMint_eq :
    p1ShapedRedeemerMint =
      Data.Constr 0 [Data.List [Data.I 1], Data.List [Data.I 1], Data.List [],
                     Data.List [Data.Constr 0 []], Data.I 0] := by
  native_decide

/-- SHAPE T1's protocol-params reference input (reference index 0). Its datum
publishes `directoryNodeCS = dirCS` and `progLogicCred = ScriptCredential plc`;
`pCS`, its own first non-ada policy, is a DIFFERENT variable from the script
parameter, so `pparamsAtRefIdx`'s `phasCSH` gate (:832) is not pre-satisfied. -/
def p1ShapedParamsIn
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 2⟩,
   { txOutAddress := ⟨.ScriptCredential pHash, none⟩
   , txOutValue := adaPlusOne pAda pCS pTn pQty
   , txOutDatum := .OutputDatum
       (IsData.toData
         (GlobalParams.mk dirCS (.ScriptCredential plc) (.ScriptCredential glc)
                          (.ScriptCredential slc)))
   , txOutReferenceScript := none }⟩

/-- SHAPE T1's directory node (reference index 1) — the node the single transfer
proof points at. `key`, `next`, `tlsH` and `nCS` are all free. -/
def p1ShapedNode
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 3⟩,
   { txOutAddress := ⟨.ScriptCredential nHash, none⟩
   , txOutValue := adaPlusOne nAda nCS nTn nQty
   , txOutDatum := .OutputDatum
       (IsData.toData
         (DirectorySetNode.mk key next (.ScriptCredential tlsH)
                              (.ScriptCredential ilsH) gsCS))
   , txOutReferenceScript := none }⟩

/-- SHAPE T1's withdrawal map: two script credentials. Entry 0 is the own
(global) credential and seeds `cachedTransferScript0` (:1201); entry 1 is the one
the redeemer's `transferWdrlIdxs = [1]` names on a cache miss (:913-915). -/
def p1ShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-! ## SHAPE T1 — pure transfer, single asset, PATH A -/

/-- The mini-ledger input: at the base credential, owner-witnessed by a
signatory. -/
def p1ShapedBaseIn (plc owner : ByteString) (inAda : Integer)
    (cs tn : ByteString) (qIn : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential plc, some (.StakingHash (.PubKeyCredential owner))⟩
   , txOutValue := adaPlusOne inAda cs tn qIn
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- The external (non-mini-ledger) input: the ledger-legal source that makes an
escape balance. `pvalueFromCred` SKIPS it (:443). -/
def p1ShapedExtIn (ext : ByteString) (in2Ada : Integer)
    (cs tn : ByteString) (qIn2 : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.PubKeyCredential ext, none⟩
   , txOutValue := adaPlusOne in2Ada cs tn qIn2
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- The mini-ledger output — the one the containment check has to find. -/
def p1ShapedBaseOut (plc : ByteString) (outAda : Integer)
    (cs tn : ByteString) (qOut : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential plc, none⟩
  , txOutValue := adaPlusOne outAda cs tn qOut
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- The ESCAPE output: a pubkey address holding the same policy. -/
def p1ShapedEscOut (dest : ByteString) (escAda : Integer)
    (cs tn : ByteString) (qEsc : Integer) : TxOut :=
  { txOutAddress := ⟨.PubKeyCredential dest, none⟩
  , txOutValue := adaPlusOne escAda cs tn qEsc
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- **SHAPE T1.** See the module header for the full FIXED / SYMBOLIC split. -/
def p1ShapedCtx
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn plc owner inAda cs tn qIn
          , p1ShapedExtIn ext in2Ada cs tn qIn2 ]
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
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), p1ShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- Parameter evidence unchanged from WSC/Prep/Global1600.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1176-1177). -/
def p1ShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

/-! ## SHAPE T2 — SHAPE T1 with a nonzero symbolic mint -/

/-- **SHAPE T2.** Identical to T1 except `txInfoMint = [(cs,{tn:q})]` with `q`
free (sign unconstrained) and the redeemer carrying one `Member` mint proof. -/
def p1ShapedMintCtx
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseIn plc owner inAda cs tn qIn
          , p1ShapedExtIn ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda cs tn qOut
          , p1ShapedEscOut dest escAda cs tn qEsc ]
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), p1ShapedRedeemerMint)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemerMint
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1ShapedMintInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 fee)

/-! ## SHAPE T3 — two token names, the OTHER containment dispatch arm -/

/-- **SHAPE T3.** Identical to T1 except every value carrying the policy carries
TWO token names with independent symbolic quantities, so the expected value has
one currency symbol with two token names and the dispatch (:676-699) takes
`checkWholesaleThenBuiltin` — Path B, falling through to Path C. -/
def p1ShapedTwoCtx
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
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ ⟨⟨ByteString.mk "", 0⟩,
             { txOutAddress :=
                 ⟨.ScriptCredential plc, some (.StakingHash (.PubKeyCredential owner))⟩
             , txOutValue := adaPlusTwoTn inAda cs tn0 tn1 qIn0 qIn1
             , txOutDatum := .NoOutputDatum
             , txOutReferenceScript := none }⟩
          , ⟨⟨ByteString.mk "", 1⟩,
             { txOutAddress := ⟨.PubKeyCredential ext, none⟩
             , txOutValue := adaPlusTwoTn in2Ada cs tn0 tn1 qX0 qX1
             , txOutDatum := .NoOutputDatum
             , txOutReferenceScript := none }⟩ ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ { txOutAddress := ⟨.ScriptCredential plc, none⟩
            , txOutValue := adaPlusTwoTn outAda cs tn0 tn1 qOut0 qOut1
            , txOutDatum := .NoOutputDatum
            , txOutReferenceScript := none }
          , { txOutAddress := ⟨.PubKeyCredential dest, none⟩
            , txOutValue := adaPlusTwoTn escAda cs tn0 tn1 qE0 qE1
            , txOutDatum := .NoOutputDatum
            , txOutReferenceScript := none } ]
      , txInfoFee := fee
      , txInfoMint := []
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), p1ShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1ShapedTwoInputs
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
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ShapedTwoCtx cs tn0 tn1 plc owner inAda qIn0 qIn1 ext in2Ada qX0 qX1
        outAda qOut0 qOut1 dest escAda qE0 qE1 pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee)

end WSC
