-- ✅ RE-PROVED AT PR #112 (task N5, wsc-poc main 2306678). Current. See WSC/IMPACT-PR112.md §N5.
/-
WSC/Shaped/SeizeShaped.lean — SHAPED prep of the production clawback validator
`programmableSeize` (task Z6).

Mechanism (i) (WSC/Shaped/Shape.lean): the shape is baked into the `#prep_uplc`
inputs function. Same flat and same application order as WSC/Prep/Seize.lean
(`programmableSeize` + `WSC.seizeInputs`); the only difference from
`appliedSeize` is that the context argument is a shape instead of a universally
quantified `ScriptContext`, and the budget is raised from 600 — where the E2
vacuity probe PROVED that no accepting context exists — to 3800, which is above
this shape's two measured accepting step counts (3004 and 3328) and above the
cheapest accepting seize golden (2,570).

════════════════════════════════════════════════════════════════════════════
SHAPE S1 — "one mini-ledger seize with a wallet input and a second
base-or-not output".
════════════════════════════════════════════════════════════════════════════
Two design findings, recorded because both are places a lazier shape would have
handed over the postcondition (cf. WSC/SHAPING-RESULTS.md §3):

* **A one-input/one-output shape is USELESS for conjunct 2.** With exactly one
  input and one output the ledger balance rule (`isBalanced`, a conjunct of
  `validRewardingContext`) already forces `out = in + mint` for every non-ada
  asset, so "the seized delta stays at the base credential" would be implied by
  the HYPOTHESIS, not by the bytecode. SHAPE S1 therefore carries a SECOND
  output whose payment credential is a FREE script hash `escH`: when
  `escH ≠ plc` it is the escape route the property is about, and balance alone
  then permits `outAtBase < inAtBase`; when `escH = plc` it is the residual
  seized-tokens output that the real accepting seize goldens carry. Both
  assignments are in the class.
* **…and then a second INPUT is forced.** With one input, two outputs and the
  per-pair value clause (which pins ada and every non-seized policy of the
  continuing output to the input's, ProgrammableLogicBase.hs:1466 →
  `pvalueEqualsDeltaCurrencySymbol`), no ledger-balanced ESCAPING assignment
  exists at all, so the interesting half of the class would be empty. A wallet
  input that pays the fee and funds the second output is what makes it
  non-empty — and it is what every real seize transaction looks like.

FIXED (the published scope — quote this with any theorem stated against this
prep):
* purpose REWARDING, own credential = `ScriptCredential w0`;
* exactly 2 inputs: index 0 the candidate mini-ledger input (SCRIPT payment
  credential + a staking credential), index 1 a wallet input at a PUBKEY
  address — so input 1 is NOT at the base credential at any leaf assignment
  (`payCred`'s `Data` tags differ), i.e. this shape has exactly ONE candidate
  mini-ledger input;
* exactly 2 reference inputs: index 0 the protocol-params node, index 1 the
  directory node the redeemer points at; both at SCRIPT addresses, both with
  INLINE datums;
* exactly 2 outputs: index 0 the continuing output, index 1 an output at a FREE
  script payment credential (base or not, see above);
* every value is ada plus exactly ONE other policy carrying exactly ONE token
  name (`Shape.adaPlusOne`) — the canonical `validTxOutValue` form. **This is
  where conjunct 2's canonicity comes from for free: a one-entry token map
  cannot have duplicate names and is trivially sorted, so the two
  machine-checked counterexamples that block conjunct 2 on the source model
  (`WSC/Props/P2_Seize.lean` §5, obligation B1) cannot be instantiated here.**
* mint field: exactly ONE policy `mCS` carrying exactly ONE token name `mTn`
  with a symbolic, unsigned quantity `mQ` — so the seize-time mint of the seized
  policy (`tokensForCS key txInfoMint`, :1318-1319) is REAL at this shape and
  conjunct 2's `WSC.mintOf` term is load-bearing. `mCS` is a DIFFERENT variable
  from `key`, so whether the mint touches the seized policy at all is decided by
  the solver, and the sign of `mQ` is free, so both a mint and a burn are in the
  class;
* withdrawal map: exactly 2 entries, both SCRIPT credentials;
* exactly 1 redeemer-map entry, for the own `Rewarding` purpose;
* empty certificate / signatory / datum / vote / proposal lists;
* redeemer = `SeizeAct 1 [] 0 0 0 1`: the four index fields the validator reads
  are CONCRETE (`directoryNodeIdx = 1`, `outputsStartIdx = 0`,
  `seizeParamsRefIdx = 0`, `issuerWdrlIdx = 1`). These are self-validating
  hints — each is re-checked by the branch it selects (`phasCSH` on the params
  UTxO :832, the datum decodes at :1311-1317, the withdrawal-credential
  equality at :1327-1328) — and they are exactly the fields the shaping
  doctrine permits to fix. Fields 1 and 3 (`inputIdxs`, `lengthInputIdxs`) are
  not read by the current validator (:1299-1304);
* the four `TxOutRef`s are `⟨"",0⟩`, `⟨"",1⟩` (inputs) and `⟨"",2⟩`, `⟨"",3⟩`
  (reference inputs); transaction id `""`; validity interval the finite closed
  `[0,1]`. None of these is read by this validator.

FIXED BY AN UPSTREAM TOOL LIMITATION, not by choice — see DEFECT D4 below:
* input 0 and output 0 share ONE payment-credential variable `mlH`, so
  "input 0 is at the base credential" and "output 0 is at the base credential"
  are the SAME condition `mlH = plc` (still decided by the solver against the
  independent variable `plc`, but the shape cannot exhibit a pair whose payment
  credentials DIFFER);
* input 0 and output 0 share ONE non-ada policy variable `mlCS` and ONE token
  name variable `mlTn` (their quantities stay independent);
* both carry `txOutReferenceScript := none`, so `pairPreserved`'s
  reference-script clause is true by construction at this shape.

WHY THOSE THREE, PRECISELY — **DEFECT D4** (new, measured this session): the
`#prep_uplc` residual builder mis-types the else-branch of `Blaster.dite'`
whenever the branch condition is a COMPOUND `Bool` it cannot normalize to a
`Prop` equality. `Blaster/Optimize/Rewriting/OptimizePropNot.lean:53` rewrites
the binder type `¬ (true = e)` to `false = e` while the `dite'` head keeps
`true = e`, and the Lean kernel then rejects the residual with
`(kernel) application type mismatch`. Every `Data` equality the seize validator
performs on a structure with TWO OR MORE free scalar leaves produces exactly
such a condition, and there are three of them on this path:

1. `inp.txOutAddress == o.txOutAddress` (:1460-1461) — two leaves, payment
   credential and staking credential;
2. `programmableInputRest == programmableOutputRest` (:1462-1463) — the
   two-element `Data` list `[datum, refScript]`;
3. `inputRest == outputRest` inside `goOuter` (:1795) — the currency entries
   after the seized one, reached when the seized policy is ada.

Reducing each to ONE free leaf pair makes the prep succeed in ~1 s. The full
ladder of measured variants is in WSC/status-fragments/z6-p2shaped.md. **The
three resulting by-construction equalities are honest scope loss and are listed
above rather than hidden.** Note what is NOT lost: the STAKING credential of the
pair stays two independent variables (`inStk` vs `oStk`), and that is the
mini-ledger's ownership field — the clause a seizure would have to break in
order to hand tokens to a different holder.

SYMBOLIC — in particular:
* `plc`, the mini-ledger base credential published by the params datum, is a
  DIFFERENT variable from `mlH`, so "the pair sits at the mini-ledger" is
  earned, and from `escH`, so "the second output is inside the mini-ledger" is
  earned;
* `inStk` / `oStk`, the two staking credentials — DIFFERENT variables, so
  `pairPreserved`'s full-address clause has real content: the shape contains
  assignments in which the continuing output pays a DIFFERENT holder;
* `dIn` / `dOut`, the two inline datum payloads — DIFFERENT variables;
* `key`, the seized policy (position 0 of the directory node's datum), is a
  DIFFERENT variable from `mlCS`, `i1CS` and `o1CS`. Nothing forces the pair to
  hold the seized policy, and nothing forbids the second output from holding it;
* `nCS`, the directory node's first non-ada policy, is a DIFFERENT variable from
  `dirCS`, the directory policy published by the params datum, so :1329's
  `phasCSH` gate must be cleared by the accept path; likewise `pCS` ≠ `ppCS`
  for :832;
* `ilsH`, the node datum's issuer-logic credential, is a DIFFERENT variable from
  `w1`, the withdrawal entry `issuerWdrlIdx = 1` selects (:1327-1328);
* every ada amount, token quantity, withdrawal amount, and the fee.
-/
import WSC.Prep.Seize
import WSC.Shaped.Shape
import WSC.Redeemer
import Blaster

set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol ScriptContext ScriptHash
                          StakingCredential TokenName TxInInfo TxOutRef TxInfo
                          Withdrawals rewardingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open WSC.Shape

/-- SHAPE S1's redeemer, `SeizeAct 1 [] 0 0 0 1`, spelled out as the literal
`Data` the validator sees.  Written literally (rather than as
`IsData.toData (PLGRedeemer.SeizeAct …)`) so that the shape's `Data` skeleton is
closed by `rfl`, which the projection-audit lemmas in
WSC/Props/Shaped/P2Shaped.lean need; `seizeShapedRedeemer_eq` below is the AUDIT
that it really is what WSC/Redeemer.lean's mirror produces. -/
def seizeShapedRedeemer : Data :=
  Data.Constr 1 [Data.I 1, Data.List [], Data.I 0, Data.I 0, Data.I 0, Data.I 1]

/-- AUDIT: the literal above is exactly what WSC/Redeemer.lean's audited
`IsData PLGRedeemer` mirror encodes `SeizeAct 1 [] 0 0 0 1` to
(ProgrammableLogicBase.hs:1055-1063 for the field order, :1066-1068 for
`SeizeAct = 1`). -/
theorem seizeShapedRedeemer_eq :
    seizeShapedRedeemer = IsData.toData (PLGRedeemer.SeizeAct 1 [] 0 0 0 1) := by
  native_decide

/-- SHAPE S1's protocol-params reference input (reference index 0). Position 0 of
its datum publishes the directory policy `dirCS`, position 1 the mini-ledger base
credential `ScriptCredential plc` (ProtocolParams.hs:44-68). -/
def seizeShapedParamsIn
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

/-- SHAPE S1's directory node (reference index 1) — the input the redeemer's
`directoryNodeIdx = 1` points at. Position 0 of its datum (`key`) is the SEIZED
POLICY; position 3 (`issuerLogicScript`) is what condition 3 compares against the
withdrawal map (:1323-1328). -/
def seizeShapedNode
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

/-- SHAPE S1's candidate mini-ledger input (input index 0). Its payment
credential `mlH` is free and is compared by the validator against the params
datum's `plc` (:1446-1447); its staking credential `inStk` is a separate free
variable. -/
def seizeShapedIn0
    (mlH inStk : ByteString) (i0Ada : Integer) (mlCS mlTn : ByteString) (i0Qty : Integer)
    (dIn : ByteString) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential mlH, some (.StakingHash (.PubKeyCredential inStk))⟩
   , txOutValue := adaPlusOne i0Ada mlCS mlTn i0Qty
   , txOutDatum := .OutputDatum (Data.B dIn)
   , txOutReferenceScript := none }⟩

/-- SHAPE S1's wallet input (input index 1) — pays the fee and funds output 1.
At a PUBKEY address, so `payCred`'s `Data` tag differs from the base credential's
at every leaf assignment and the validator skips it (:1475). -/
def seizeShapedIn1
    (wallet : ByteString) (i1Ada : Integer) (i1CS i1Tn : ByteString) (i1Qty : Integer)
    : TxInInfo :=
  ⟨⟨ByteString.mk "", 1⟩,
   { txOutAddress := ⟨.PubKeyCredential wallet, none⟩
   , txOutValue := adaPlusOne i1Ada i1CS i1Tn i1Qty
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- SHAPE S1's continuing output (output index 0) — the one the validator pairs
input 0 with (:1450). Shares `mlH`, `mlCS`, `mlTn` with input 0 (DEFECT D4 in the
module header); its staking credential `oStk`, datum payload `dOut`, lovelace
`o0Ada` and quantity `o0Qty` are independent free variables. -/
def seizeShapedOut0
    (mlH oStk : ByteString) (o0Ada : Integer) (mlCS mlTn : ByteString) (o0Qty : Integer)
    (dOut : ByteString) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential mlH, some (.StakingHash (.PubKeyCredential oStk))⟩
  , txOutValue := adaPlusOne o0Ada mlCS mlTn o0Qty
  , txOutDatum := .OutputDatum (Data.B dOut)
  , txOutReferenceScript := none }

/-- SHAPE S1's second output (output index 1), at a FREE script payment
credential `escH`:

* `escH ≠ plc` — the **escape route**: an output outside the mini-ledger. An
  assignment in which the seized policy leaves through it is ledger-legal
  (`validRewardingContext` holds) and inside this shape class; conjunct 2 is
  exactly the claim that the bytecode rejects it, and
  `P2ShapedWitness.exec_rejects_escaping_seize` exhibits one such context and
  shows the real CEK rejecting it.
* `escH = plc` — the **residual seized-tokens output** that both accepting seize
  goldens carry (`residualBaseTokens`, :1510-1521). -/
def seizeShapedOut1
    (escH : ByteString) (o1Ada : Integer) (o1CS o1Tn : ByteString) (o1Qty : Integer) : TxOut :=
  { txOutAddress := ⟨.ScriptCredential escH, none⟩
  , txOutValue := adaPlusOne o1Ada o1CS o1Tn o1Qty
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- SHAPE S1's withdrawal map: entry 0 is the seize script's own (rewarding)
credential, entry 1 is what `issuerWdrlIdx = 1` selects. -/
def seizeShapedWdrl (w0 w1 : ScriptHash) (a0 a1 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1)]

/-- **SHAPE S1.** See the module header for the full FIXED / SYMBOLIC split. -/
def seizeShapedCtx
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
      , txInfoRedeemers := [(.Rewarding (.ScriptCredential w0), seizeShapedRedeemer)]
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := seizeShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- Parameter evidence unchanged from WSC/Prep/Seize.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1290-1291). -/
def seizeShapedInputs
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
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (seizeShapedCtx mlH inStk i0Ada mlCS mlTn i0Qty dIn
        wallet i1Ada i1CS i1Tn i1Qty
        oStk o0Ada o0Qty dOut
        escH o1Ada o1CS o1Tn o1Qty mCS mTn mQ
        pHash pCS pTn pAda pQty dirCS plc glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 fee)

/- SHAPE S1's prep at CEK budget **3800**. Measured step counts of the shape's
three concrete instances (`WSC/Shaped/Probe/S1K.lean`, real CEK, no prep and no
solver involved):

| instance | what it is | K |
|---|---|---|
| `ctxAccept`   | accepting; the pair absorbs the +2 mint and keeps all seized tokens; output 1 outside the mini-ledger | **3004** |
| `ctxResidual` | accepting; 5 seized tokens plus the +2 mint land in output 1, which IS at the base credential — the real goldens' shape | **3328** |
| `ctxStolen`   | ledger-legal, tokens stay at the base payment credential but the continuing output's STAKING credential is changed | REJECTED at 3800 **and at 20000** |
| `ctxEscape`   | ledger-legal ESCAPE of the seized tokens past the mini-ledger | REJECTED at 3800 **and at 20000** |

Both rejections are genuine, not budget exhaustion — that is what the 20000-step
row is for. 3800 is above BOTH accepting instances, which matters: at 3000 the
residual-output run — the one every real seize transaction performs — would fall
outside the theorem. For comparison the cheapest accepting seize GOLDEN is 2,570
and the more complex one 4,647 (`WSC/goldens/K-MEASUREMENTS.md` §3).

Contrast `WSC/Prep/Seize.lean`, which preps at 600 where the E2 vacuity probe
PROVED no accepting context exists, and the SYMBOLIC prep of this same validator,
which did not finish in 77 min at budget 2,000 nor in 62 min at 9,000
(K-MEASUREMENTS §5.1/§5.2). The shaped prep at 3800 takes ~2 s. -/
#prep_uplc appliedSeizeShaped3800 programmableSeize seizeShapedInputs 3800

end WSC
