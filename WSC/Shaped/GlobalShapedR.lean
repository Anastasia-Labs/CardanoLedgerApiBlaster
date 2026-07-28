-- ✅ RE-BASED on wsc-poc main @ 2306678 (PR #112) by task N4: redeemer widened to 5 fields, prep re-run green. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Shaped/GlobalShapedR.lean — **the NODE-REALIZABLE re-cut of the global
(transfer) validator's shapes** (task C1).

════════════════════════════════════════════════════════════════════════════
WHY THIS MODULE EXISTS
════════════════════════════════════════════════════════════════════════════
`WSC/Props/Shaped/ShapeRealizability.lean` proves that every shape in this
library is EMPTY as a class of ledger transactions: each bakes a ONE-entry
`txInfoRedeemers` map while also baking script witnesses (a two-entry all-script
withdrawal map, and for SHAPE T1 a script-credential input) that the Conway
UTXOW rule `MissingRedeemers` requires to have redeemer entries of their own.
For SHAPE T1 the emptiness is UNCONDITIONAL (`t1_class_is_empty`); for G1/G6 it
holds under the `RedeemerCoverageAllPlutus` hypothesis (`g1_class_is_empty_under_coverage`).

The shapes here are the SAME transactions with a redeemer map that COVERS every
script witness the transaction actually needs, so their classes are inhabited by
transactions a node would accept. Nothing else about the shapes changes: every
amount, policy, credential and hash that was symbolic before is still symbolic,
and the two design properties that make the theorems non-trivial are preserved
verbatim (P1: a non-base input and a non-base output; P6: two outputs with free
credential hashes).

════════════════════════════════════════════════════════════════════════════
WHAT "COVERS EVERY SCRIPT WITNESS" MEANS, RULE BY RULE
════════════════════════════════════════════════════════════════════════════
Conway UTXOW's `scriptsNeeded` collects, for one transaction:
* the payment-credential script of every SPENT input  → a `Spending` redeemer
  keyed by that input's `TxOutRef`;
* the policy of every entry of the mint field          → a `Minting` redeemer;
* the credential of every SCRIPT-credential withdrawal → a `Rewarding` redeemer;
and `MissingRedeemers` rejects the transaction if any needed script has no
entry. Reference inputs are NOT spent and need no witness; PUBKEY inputs and
PUBKEY withdrawals need a VKey witness, not a redeemer; outputs at script
addresses need nothing.

The redeemer map must additionally be strictly ASCENDING in CLAB's
`ltScriptPurpose` (`CardanoLedgerApi/V3/Contexts.lean`, audit row M):
`Spending < Minting < Certifying < Rewarding < Voting < Proposing`, and
`Rewarding` entries compare by `ltCredential`, under which
`ScriptCredential < PubKeyCredential` (audit row L). Every map below is written
in that order, and the only side condition it needs on the symbolic leaves is
`w0 < w1` — which `validWithdrawals` already forces on the withdrawal map.

════════════════════════════════════════════════════════════════════════════
THE TWO LEVERS, AND WHICH ONE EACH SHAPE USES
════════════════════════════════════════════════════════════════════════════
**(i) PUBKEY withdrawal entries wherever the validator does not need a script
witness there.** What the global validator actually dereferences out of the
withdrawal map (`ProgrammableLogicBase.hs`, worktree `new-session-3c417d`):

* `:1201` `cachedTransferScript0 <- plet $ pfstBuiltin # (phead # withdrawalEntries)`
  — the credential of withdrawal entry **0**, forced unconditionally on the
  `PTransferAct` path. So the map must be non-empty, and entry 0 is the
  validator's OWN rewarding credential (`w0`), which is a script credential
  because that is what makes the validator run at all (`validScriptInfo`'s
  rewarding clause, audit row E).
* `:913-915` on a cache MISS the positive-proof branch requires
  `directoryNodeDatumFTransferLogicScript #== (pfstBuiltin # (phead #
  (pdropList # wdrlIdx # withdrawalEntries)))` — the entry named by the
  redeemer's `transferWdrlIdxs` must equal the node datum's
  `transferLogicScript`, which is a `ScriptCredential`. So **that** entry must
  be a script credential and needs its own `Rewarding` redeemer. This is live
  only when the redeemer HAS a transfer proof, i.e. for SHAPE T1R/T2R/T6R.
* `:437-439` `pisScriptInvokedEntries # scriptCredData # withdrawalEntries` —
  used only for an input whose STAKING credential is a script; none of these
  shapes has one (they use `StakingHash (PubKeyCredential owner)` plus a
  signatory, or a pubkey input).

SHAPES G1R / G6R have `transferProofs = transferWdrlIdxs = []`, so nothing but
entry 0 is ever read: their withdrawal map is cut down to the ONE script entry
the ledger itself requires, which makes their skeleton no larger than before
(3 map entries in total, exactly as the old 2-withdrawal/1-redeemer cut).

**(ii) Symbolic redeemer VALUES.** The entries the validator does not read carry
`Data.I r` with `r` a free Integer, so the map's LENGTH and PURPOSE TAGS are
frozen (that is what `#prep_uplc` needs) while the payloads stay symbolic. This
is sound as ledger data: the redeemer of a script other than the running one is
unconstrained by `validScriptInfo` (which checks the running script's entry
only, `CardanoLedgerApi/V3/Contexts.lean:1036`).

════════════════════════════════════════════════════════════════════════════
THE SIX RE-CUT SHAPES
════════════════════════════════════════════════════════════════════════════
| shape | old cut | new cut | needed-script coverage |
|---|---|---|---|
| **G1R** (P5) | 2 script wdrl, 1 redeemer | **1 script wdrl, 2 redeemers** | mint `cs` ⟶ `Minting cs`; wdrl `w0` ⟶ `Rewarding w0`; input is PUBKEY |
| **G6R** (P6) | 2 script wdrl, 1 redeemer | **1 script wdrl, 2 redeemers** | as G1R |
| **T1R** (P1 base) | 2 script wdrl, 1 redeemer | **2 script wdrl, 3 redeemers** | input 0 at `ScriptCredential plc` ⟶ `Spending ⟨"",0⟩`; wdrl `w0`,`w1` ⟶ two `Rewarding`; no mint |
| **T2R** (P1 mint) | 2 script wdrl, 1 redeemer | **2 script wdrl, 4 redeemers** | T1R plus mint `cs` ⟶ `Minting cs` |
| **T6R** (P1 output aggregation) | 2 script wdrl, 1 redeemer | **2 script wdrl, 3 redeemers** | as T1R |
| **T7R** (P1 aggregation + mint) | 2 script wdrl, 1 redeemer | **2 script wdrl, 4 redeemers** | as T2R |

The T1R/T2R sizes are exactly the measured sizes of the real accepting goldens
(`WSC/AUDIT.md` §4b: `base-spend-transfer-tx` 1 input / 2 wdrl / **3**
redeemers; the mint vectors 1 / 3 / **5**), so this is not a guess about what a
node accepts — it is the shape of transactions the off-chain builder emits.

WHAT THIS MODULE DOES NOT CLAIM. A redeemer-covered transaction still has to
have every OTHER script accept (the base spending validator on input 0 of T1R,
the per-policy transfer-logic script at withdrawal entry 1, the issuance policy
of a `Minting` entry). Those are separate validators and separate properties;
`RedeemerCoverageAllPlutus` is the rule the emptiness proofs used, and it is the rule
these shapes satisfy. See `WSC/Props/Shaped/GlobalRealizability.lean` for the
realizability theorems and for exactly what they do and do not assert.
-/
import WSC.Shaped.GlobalShaped
import WSC.Shaped.GlobalMemberShaped
import WSC.Shaped.GlobalShapedP1
import WSC.Shaped.GlobalShapedP1Out
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

/-! ## §0 The shared building blocks of a covered redeemer map -/

/-- The ONE-entry withdrawal map of SHAPES G1R / G6R: the validator's own
rewarding credential, which `:1201` reads and which `validScriptInfo`'s
rewarding clause requires to be a script credential and to be present. -/
def globalRWdrl (w0 : ScriptHash) (a0 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0)]

/-- The redeemer map of SHAPES G1R / G6R: a `Minting` entry for the minted
policy (needed script: the issuance policy) and the running script's own
`Rewarding` entry. Ascending: `Minting < Rewarding` for ALL leaf values. -/
def globalRRedeemers (cs : CurrencySymbol) (w0 : ScriptHash) (rMint : Integer)
    (own : Data) : RedeemerMap :=
  [ (.Minting cs, Data.I rMint)
  , (.Rewarding (.ScriptCredential w0), own) ]

/-- The redeemer map of SHAPES T1R / T6R (no mint): a `Spending` entry for the
mini-ledger input at `⟨"",0⟩`, then the two `Rewarding` entries covering the
two script withdrawals. Ascending iff `w0 < w1`, which `validWithdrawals`
forces. -/
def p1RRedeemers (w0 w1 : ScriptHash) (rBase rTls : Integer) (own : Data) : RedeemerMap :=
  [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I rBase)
  , (.Rewarding (.ScriptCredential w0), own)
  , (.Rewarding (.ScriptCredential w1), Data.I rTls) ]

/-- The redeemer map of SHAPE T2R: `p1RRedeemers` plus the `Minting` entry the
nonzero mint field needs. Ascending: `Spending < Minting < Rewarding w0 <
Rewarding w1` (the last step iff `w0 < w1`). -/
def p1RMintRedeemers (cs : CurrencySymbol) (w0 w1 : ScriptHash)
    (rBase rMint rTls : Integer) (own : Data) : RedeemerMap :=
  [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I rBase)
  , (.Minting cs, Data.I rMint)
  , (.Rewarding (.ScriptCredential w0), own)
  , (.Rewarding (.ScriptCredential w1), Data.I rTls) ]

/-! ## §1 SHAPE G1R — the re-cut of SHAPE G1 (P5's shape)

SHAPE G1 verbatim (WSC/Shaped/GlobalShaped.lean's header is the published FIXED
/ SYMBOLIC split and still applies word for word to the reference inputs, the
input, the output, the mint and the redeemer) with exactly two changes:

* withdrawal map: **1** entry, `(.ScriptCredential w0, a0)` — the second entry
  was never dereferenced, because `transferWdrlIdxs = []`;
* redeemer map: **2** entries, `[(Minting cs, I rMint), (Rewarding w0, red)]`.

`w1`/`a1` are gone from the parameter list and `rMint` is added. -/
def globalRShapedCtx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer)
    : ScriptContext :=
  let resolved : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential owner, none⟩
    , txOutValue := adaOnly inAda
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  let produced : TxOut :=
    { txOutAddress := ⟨.PubKeyCredential dest, none⟩
    , txOutValue := adaPlusOne outAda cs tn qOut
    , txOutDatum := .NoOutputDatum
    , txOutReferenceScript := none }
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨⟨ByteString.mk "", 0⟩, resolved⟩]
      , txInfoReferenceInputs :=
          [ globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , globalShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs := [produced]
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := globalRWdrl w0 a0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := globalRRedeemers cs w0 rMint globalShapedRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := globalShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

/-- Parameter evidence unchanged from WSC/Prep/Global1600.lean: 1 parameter
(`protocolParamsCS`), then the context (ProgrammableLogicBase.hs:1176-1177). -/
def globalRShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (dest : ByteString) (outAda qOut : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (globalRShapedCtx cs tn q owner inAda dest outAda qOut pHash pCS pTn pAda pQty
        dirCS plc glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 a0 rMint fee)

/-! ## §2 SHAPE G6R — the re-cut of SHAPE G6 (P6's shape)

SHAPE G6 verbatim (WSC/Shaped/GlobalMemberShaped.lean's header, including the
"WHY TWO OUTPUTS" anti-tautology stanza, applies unchanged) with the same two
changes as G1R. The output list is literally `memberShapedOutputs`, so P6's
postcondition is stated about the same object as before. -/
def memberRShapedCtx
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := [memberShapedInput owner inAda]
      , txInfoReferenceInputs :=
          [ globalShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc ]
      , txInfoOutputs := memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := globalRWdrl w0 a0
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := globalRRedeemers cs w0 rMint memberShapedRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := memberShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def memberRShapedInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 : ByteString) (a0 rMint : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (memberRShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 a0 rMint fee)

/-! ## §3 SHAPE T1R — the re-cut of SHAPE T1 (P1's base shape)

SHAPE T1 verbatim (WSC/Shaped/GlobalShapedP1.lean's header, including the "WHY
THE MINIMAL P1 SHAPE IS NOT 1 INPUT, 1 OUTPUT" stanza — the external input and
the escape output are both still here) with exactly one change: the redeemer map
grows from 1 to **3** entries so that the `ScriptCredential plc` input and BOTH
script withdrawals are covered. The withdrawal map stays two-script, because
`transferWdrlIdxs = [1]` makes entry 1 the transfer-logic script the node datum
names (`:913-915`) — a pubkey entry there would make the shape's own accepting
branch unreachable. -/
def p1RShapedCtx
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
    (rBase rTls : Integer)
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
      , txInfoRedeemers := p1RRedeemers w0 w1 rBase rTls p1ShapedRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1RShapedInputs
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
    (rBase rTls : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1RShapedCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

/-! ## §4 SHAPE T2R — the re-cut of SHAPE T2 (P1's mint shape)

SHAPE T2 verbatim with a **4**-entry redeemer map: the T1R three plus the
`Minting cs` entry the nonzero mint field needs. `validMintValue` (LR-CTX audit
row K) forces every mint quantity ≠ 0, so the `Minting` entry is a genuinely
needed script at every point of the class — there is no `q = 0` corner where it
would be an EXTRA redeemer. -/
def p1RShapedMintCtx
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
    (rBase rMint rTls : Integer)
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
      , txInfoRedeemers := p1RMintRedeemers cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemerMint
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1RShapedMintInputs
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
    (rBase rMint rTls : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1RShapedMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rMint rTls fee)

/-! ## §5 SHAPE T6R — the re-cut of SHAPE T6 (P1's output-aggregation shape)

SHAPE T6 (WSC/Shaped/GlobalShapedP1Out.lean) verbatim — TWO mini-ledger outputs
with independent free quantities, so `outAtBase` is a genuine SUM and PATH A's
accumulate-scan with its early exit has to add them up — with T1R's 3-entry
redeemer map. -/
def p1ROutCtx
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
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
          [ p1ShapedBaseIn plc owner inAda cs tn qIn
          , p1ShapedExtIn ext in2Ada cs tn qIn2 ]
      , txInfoReferenceInputs :=
          [ p1ShapedParamsIn pHash pCS pTn pAda pQty dirCS plc glc slc
          , p1ShapedNode nHash nCS nTn nAda nQty key next tlsH ilsH gsCS ]
      , txInfoOutputs :=
          [ p1ShapedBaseOut plc outAda0 cs tn qOut0
          , p1ShapedBaseOut plc outAda1 cs tn qOut1
          , p1ShapedEscOut dest escAda cs tn qEsc ]
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

def p1ROutInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
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
      (p1ROutCtx cs tn plc owner inAda qIn ext in2Ada qIn2 outAda0 qOut0 outAda1 qOut1
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 a0 a1 rBase rTls fee)

/-! ## §6 SHAPE T7R — the re-cut of SHAPE T7 (P1's aggregation + mint shape)

SHAPE T7 (`p1ShapedOutMintCtx`) verbatim — two mini-ledger outputs with
independent free quantities AND a nonzero symbolic mint of unconstrained sign,
the strongest single P1 statement — with T2R's 4-entry redeemer map. -/
def p1ROutMintCtx
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rMint rTls : Integer)
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
          [ p1ShapedBaseOut plc outAda0 cs tn qOut0
          , p1ShapedBaseOut plc outAda1 cs tn qOut1
          , p1ShapedEscOut dest escAda cs tn qEsc ]
      , txInfoFee := fee
      , txInfoMint := mintOne cs tn q
      , txInfoTxCerts := []
      , txInfoWdrl := p1ShapedWdrl w0 w1 a0 a1
      , txInfoValidRange := range 0 1
      , txInfoSignatories := [owner]
      , txInfoRedeemers := p1RMintRedeemers cs w0 w1 rBase rMint rTls p1ShapedRedeemerMint
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1ShapedRedeemerMint
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1ROutMintInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (plc owner : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda0 qOut0 outAda1 qOut1 : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (rBase rMint rTls : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1ROutMintCtx cs tn q plc owner inAda qIn ext in2Ada qIn2
        outAda0 qOut0 outAda1 qOut1 dest escAda qEsc pHash pCS pTn pAda pQty
        dirCS glc slc nHash nCS nTn nAda nQty key next tlsH ilsH gsCS
        w0 w1 a0 a1 rBase rMint rTls fee)

/-! ## §7 SHAPE T8R — **NEW at PR #112**: a SCRIPT-OWNED mini-ledger input

════════════════════════════════════════════════════════════════════════════
WHY THIS SHAPE EXISTS
════════════════════════════════════════════════════════════════════════════
PR #112 replaced the owner-witness SCAN with an INDEXED lookup. Old code
(`pisScriptInvokedEntries`, ProgrammableLogicBase.hs:282-294) searched the whole
withdrawal map for the owner credential of every script-owned mini-ledger input.
New code (`:386-393`) reads the redeemer's `ownerWdrlIdxs` cursor and checks ONE
position:

    ownerCredData #== pforgetData
      (pfstBuiltin # (phead # (pdropList # pfromData (phead # idxs) # withdrawalEntries)))

**Every other shape in this library misses that code entirely.** SHAPES G1R/G6R
have no input at the mini-ledger credential at all, and SHAPES T1R/T2R/T6R/T7R
have one whose staking credential is `StakingHash (PubKeyCredential owner)`, which
takes the PUBKEY arm at `:370-376` and never touches `withdrawalEntries`. The four
regenerated transfer goldens are in the same position — N2 recorded exactly this
gap ("no golden has a non-empty `ownerWdrlIdxs`"). So without SHAPE T8R the single
most security-relevant line PR #112 added would be covered by nothing: no golden,
no shape, no theorem.

SHAPE T8R = SHAPE T1R with the mini-ledger input's OWNER changed from a pubkey to
a script, which is the whole point:

* `p1ShapedBaseInS`'s staking credential is `StakingHash (ScriptCredential sOwn)`
  with `sOwn` a FREE variable, so the tag test at `:371` sees tag 1 and the
  SCRIPT arm at `:386-393` runs;
* `txInfoSignatories` is `[]` — there is no signature to fall back on, so the
  index check is the ONLY thing standing between the attacker and the input's
  value. If it could be bypassed, this shape is where it would show;
* the redeemer's `ownerWdrlIdxs = [2]` and the withdrawal map has THREE script
  entries `w0 < w1 < w2`. `sOwn` and `w2` are DIFFERENT free variables, so
  `sOwn = w2` is not baked in — the validator has to force it. Had the shape
  written the input's owner as `ScriptCredential w2`, the check would have been
  true by construction and the shape would prove nothing.

Withdrawal roles, all three genuinely needed:
* entry 0 = `w0`, the running script's own rewarding credential, read
  unconditionally at `:1205` (`cachedTransferScript0`) and required to be a script
  credential by `validScriptInfo`'s rewarding clause;
* entry 1 = `w1`, named by `transferWdrlIdxs = [1]` and checked against the node
  datum's `transferLogicScript` at `:913-915`;
* entry 2 = `w2`, named by the NEW `ownerWdrlIdxs = [2]` and checked against the
  input's owner credential at `:386-393`.

Redeemer coverage (the C1 discipline, unchanged): 4 entries — `Spending ⟨"",0⟩`
for the script-credential input, then `Rewarding w0`, `Rewarding w1`,
`Rewarding w2`. Ascending in `ltScriptPurpose` iff `w0 < w1 < w2`, which
`validWithdrawals` forces on the withdrawal map.

P1's two design properties are preserved verbatim: the external pubkey input and
the pubkey ESCAPE output are both still present, so `isBalanced` alone still gives
only `qIn + qIn2 = qOut + qEsc` and the containment inequality must be earned.
-/

/-- SHAPE T8R's redeemer: `TransferAct [1] [1] [2] [] 0`. The third field is the
NEW `ownerWdrlIdxs` and here it is NON-EMPTY — this is the only redeemer in the
library that drives ProgrammableLogicBase.hs:386-393. -/
def p1SOwnRedeemer : Data :=
  IsData.toData (PLGRedeemer.TransferAct [1] [1] [2] [] 0)

/-- AUDIT: SHAPE T8R's redeemer `Data`, spelled out. Contrast
`p1ShapedRedeemer_eq`, whose third element is `Data.List []`. -/
theorem p1SOwnRedeemer_eq :
    p1SOwnRedeemer =
      Data.Constr 0 [Data.List [Data.I 1], Data.List [Data.I 1], Data.List [Data.I 2],
                     Data.List [], Data.I 0] := by
  native_decide

/-- SHAPE T8R's mini-ledger input: at the base credential `plc`, owner-witnessed
by a SCRIPT staking credential `sOwn` rather than by a signature. -/
def p1ShapedBaseInS (plc sOwn : ByteString) (inAda : Integer)
    (cs tn : ByteString) (qIn : Integer) : TxInInfo :=
  ⟨⟨ByteString.mk "", 0⟩,
   { txOutAddress := ⟨.ScriptCredential plc, some (.StakingHash (.ScriptCredential sOwn))⟩
   , txOutValue := adaPlusOne inAda cs tn qIn
   , txOutDatum := .NoOutputDatum
   , txOutReferenceScript := none }⟩

/-- SHAPE T8R's THREE-entry all-script withdrawal map. Ascending iff
`w0 < w1 < w2`, which `validWithdrawals` forces. -/
def p1SOwnWdrl (w0 w1 w2 : ScriptHash) (a0 a1 a2 : Integer) : Withdrawals :=
  [(.ScriptCredential w0, a0), (.ScriptCredential w1, a1), (.ScriptCredential w2, a2)]

/-- SHAPE T8R's redeemer map: one `Spending` for the script-credential input plus
one `Rewarding` per script withdrawal. -/
def p1SOwnRedeemers (w0 w1 w2 : ScriptHash) (rBase rTls rOwn : Integer)
    (own : Data) : RedeemerMap :=
  [ (.Spending ⟨ByteString.mk "", 0⟩, Data.I rBase)
  , (.Rewarding (.ScriptCredential w0), own)
  , (.Rewarding (.ScriptCredential w1), Data.I rTls)
  , (.Rewarding (.ScriptCredential w2), Data.I rOwn) ]

def p1SOwnCtx
    (cs tn : ByteString)
    (plc sOwn : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 w2 : ByteString) (a0 a1 a2 : Integer)
    (rBase rTls rOwn : Integer)
    (fee : Integer)
    : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs :=
          [ p1ShapedBaseInS plc sOwn inAda cs tn qIn
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
      , txInfoWdrl := p1SOwnWdrl w0 w1 w2 a0 a1 a2
      , txInfoValidRange := range 0 1
      , txInfoSignatories := []
      , txInfoRedeemers := p1SOwnRedeemers w0 w1 w2 rBase rTls rOwn p1SOwnRedeemer
      , txInfoData := []
      , txInfoId := ByteString.mk ""
      , txInfoVotes := []
      , txInfoProposalProcedures := []
      , txInfoCurrentTreasuryAmount := Data.I 1
      , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := p1SOwnRedeemer
  , scriptContextScriptInfo := .RewardingScript (.ScriptCredential w0) }

def p1SOwnInputs
    (protocolParamsCS : CurrencySymbol)
    (cs tn : ByteString)
    (plc sOwn : ByteString) (inAda qIn : Integer)
    (ext : ByteString) (in2Ada qIn2 : Integer)
    (outAda qOut : Integer)
    (dest : ByteString) (escAda qEsc : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS glc slc : ByteString)
    (nHash nCS nTn : ByteString) (nAda nQty : Integer)
    (key next tlsH ilsH gsCS : ByteString)
    (w0 w1 w2 : ByteString) (a0 a1 a2 : Integer)
    (rBase rTls rOwn : Integer)
    (fee : Integer)
    : List Term :=
  toTerm protocolParamsCS ::
    rewardingInputs
      (p1SOwnCtx cs tn plc sOwn inAda qIn ext in2Ada qIn2 outAda qOut
        dest escAda qEsc pHash pCS pTn pAda pQty dirCS glc slc
        nHash nCS nTn nAda nQty key next tlsH ilsH gsCS w0 w1 w2 a0 a1 a2
        rBase rTls rOwn fee)

end WSC
