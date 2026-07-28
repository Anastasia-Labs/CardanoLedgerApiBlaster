-- ⛔ REFUTED AT PR #112: `seizeModel_faithful` is FALSE at main 2306678 — machine-checked counterexample in WSC/Model/SeizeModelRefuted.lean. The 13/13 differential test still passes but no golden covers the change. Results bridged by that axiom are INVALID for production.
/-
WSC/Model/SeizeModel.lean — the SOURCE MODEL of `mkProgrammableSeize`
(ARCHITECTURE.md's pre-planned **B3** route, §"Justification for hybrid").

WHY THIS FILE EXISTS.  P2 (seize) is measured UNREACHABLE at UPLC level:
the cheapest accepting seize run costs **2,570 CEK steps**
(`WSC/goldens/K-MEASUREMENTS.md` §3), a symbolic `#prep_uplc` at budget 2,000
did not finish in 77 min and at 9,000 not in 62 min (§5.1/§5.2), and the two
vacuity probes that DID complete (budgets 600 and 1,000) returned `Valid` for
"no accepting context exists" — i.e. every P2 theorem statable today at UPLC is
provably vacuous.  Independently, task Y1 established that the wall is Z3
SEARCH rather than prep: at or above the minimal-accepting step count every
bytecode obligation is `Undetermined` even with 3,300 s of solver time.  So the
only route to a NON-VACUOUS P2 today is to model the validator at SOURCE level
and carry ONE explicit compilation-fidelity bridge (`seizeModel_faithful`,
bottom of this file).

WHAT IS MODELLED.  `mkProgrammableSeize`, transcribed clause-by-clause from
  /home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d/
      src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs
(read 2026-07-25; **line numbers below were read off that file**, not copied
from older docs).  The entry point is `:1290-1331`; the mini-ledger walk is
`processThirdPartyTransfer` `:1492-1545` with its per-pair helper
`pcheckCorrespondingThirdPartyTransferInputsAndOutputs` `:1429-1475`; the value
algebra is `pvalueEqualsDeltaCurrencySymbol` `:1677-1830` together with
`ptokenPairsUnionFast` `:149-183`, `ptokensForCurrencySymbol` `:1345-1364`,
`ptokenPairsContain` `:1381-1411`, `pnegateTokens` `:1634-1643`.  Out-of-module
helpers: `pparamsAtRefIdx` `:824-838`, `phasCSH` `:754-757`,
`pisRewardingScript` (plutarch-onchain-lib `Plutarch/Core/Integrity.hs:69-70`),
`pvalidateConditions` / `pand'List` (`Plutarch/Core/ValidationLogic.hs:164-168`,
`Plutarch/Core/Utils.hs:276-280`), `pdropList` (the PV11 `dropList` builtin —
**clamps a negative count to 0**, documented at `Issuance.hs:126-130`).

TRANSCRIPTION RULES OBEYED (SPIKE-FINDINGS layer F: blaster cannot digest
stdlib `List.all/any/find?`):
1. every walk is a pattern-match recursion — no `List.all`, `List.any`,
   `List.find?`, `List.foldr`;
2. every `perror` path of the validator is a `none` of the model, and every
   clause carries the source line it mirrors;
3. **NOTHING IS DECODED THAT THE VALIDATOR DOES NOT DECODE.**  This is the
   subtlest fidelity requirement and it forced three deliberate deviations from
   `WSC/Redeemer.lean`'s strict mirrors, each documented at its definition:
   `seizeFieldsOf` (positional raw field access, constructor fall-through),
   `paramsDirCSAndProgCred` (only fields 0 and 1 of the params datum are read,
   and field 1 is **never decoded** — it stays `Data` and is compared as
   `Data`), and `nodeKeyAndIssuer` (only fields 0 and 3 of the node datum, and
   field 3 stays `Data`).  Using the strict mirrors instead would have made the
   model STRICTER than the bytecode and the faithfulness axiom FALSE.

STRICTNESS ARGUMENT S1 (why a strict `Option` model can mirror a lazy UPLC
term).  The model is strict: any modelled error anywhere makes the verdict
`none`.  UPLC is call-by-value in the CEK machine for builtin application and
`plet`, but `pif` branches are delayed.  The four top-level conditions are
combined by `pand'List`, which folds with `pand'`, the **strict** conjunction
(`ValidationLogic.hs:162-168` — "Strictly evaluates a list of boolean
expressions"), so all four are forced regardless of earlier verdicts; and on an
ACCEPTING run `ptokenPairsContain` traverses its whole `requiredTokens` spine
and compares every quantity, which forces the entire delta accumulator and
hence every `ptokenPairsUnionFast` / `psubtractTokens` / `pnegateTokens` cell
that fed it.  Therefore on the accept side "bytecode accepts ⟹ nothing was
forced into an error ⟹ the model does not return `none`".  Where laziness could
still differ (a value computed but never compared) the model errs on the strict
side, which is why the differential test on the goldens
(`WSC/Model/SeizeDiff.lean`) — including the REJECTING golden — is mandatory
rather than decorative.

WHAT IS *NOT* IN THIS FILE.  No property, no postcondition, no ground-truth
vocabulary: those live in `WSC/Spec.lean` and `WSC/Props/P2_Seize.lean`.  This
file is only "what the validator computes".
-/
import CardanoLedgerApi.V3
import WSC.Redeemer
import WSC.Spec
import WSC.Prep.Seize

namespace WSC.SeizeModel

open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3 (Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo TxInInfo TxOut)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## 0. Representation

`CardanoLedgerApi.V1.Value.Value = List (Data × Data)` (V1/Value.lean:24), i.e.
exactly Plutarch's `pto (pto value) : PBuiltinList (PBuiltinPair (PAsData
PCurrencySymbol) (PAsData (PMap PTokenName PInteger)))`: an association list of
`(Data.B cs, Data.Map tokens)`.  `Tokens` below is the inner token-name map,
i.e. Plutarch's `PBuiltinList (PBuiltinPair (PAsData PTokenName) (PAsData
PInteger))` — the type every seize-path helper is written over. -/
abbrev Tokens := List (Data × Data)

/-- `pdropList` — the PV11 `dropList` builtin.  A NEGATIVE count is clamped to
zero by the builtin (stated at `Issuance.hs:126-130`, which is precisely why
`Issuance.hs` wraps it in `pcheckedDrop`).  The seize validator uses
`pdropList` RAW at `:1309`, `:1310` and `:1328` — there is no negative-index
guard on the seize path, so the model must clamp, not reject. -/
def dropL {α : Type} (n : Integer) (xs : List α) : List α :=
  if n < 0 then xs else xs.drop n.toNat

/-- `phead` — errors on the empty list. -/
def headM {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

/-! ## 1. Token-map algebra -/

/-- `pnegateTokens` — ProgrammableLogicBase.hs:1634-1643.

`pcons # (ppairDataBuiltin # tokenName # pdata (0 - pfromData tokenAmount))`:
the token NAME is passed through as raw `Data` (never `pfromData`'d, so its
shape is unconstrained), the AMOUNT is forced by `pfromData` and therefore must
be a `Data.I`.  `pcons` is a builtin, hence strict in the recursive tail. -/
def negateTokens : Tokens → Option Tokens
  | [] => some []                                            -- :1642 pnil
  | (k, Data.I q) :: rest =>                                 -- :1638-1640
      match negateTokens rest with
      | some r => some ((k, Data.I (0 - q)) :: r)
      | none => none
  | _ :: _ => none                                           -- :1640 pfromData on non-I ⇒ perror

/-- `ptokenPairsUnionFast` — ProgrammableLogicBase.hs:149-183.

Sorted merge by token name with addition on equal names.  Fidelity details:
* the outer `pelimList` is on `tokensA` with nil-case `tokensB` (:182-183); the
  inner `pelimList` is on `tokensB` with nil-case `tokensA` (:180-181);
* names are compared as BYTES (`pasByteStr # pforgetData tokenNameA`, :166-167),
  so both keys must be `Data.B` on every visited cell;
* quantities are `pfromData`'d **only** in the equal-name branch (:170-171); the
  `<` / `>` branches cons the original pair through untouched (:177-178), so the
  model must NOT require `Data.I` there. -/
def tokensUnion : Tokens → Tokens → Option Tokens
  | [], b => some b                                          -- :182-183
  | (ka, va) :: as, [] => some ((ka, va) :: as)              -- :180-181
  | (ka, va) :: as, (kb, vb) :: bs =>
      match ka, kb with
      | Data.B na, Data.B nb =>
          if na == nb then                                   -- :168
            match va, vb with
            | Data.I x, Data.I y =>                          -- :169-174
                match tokensUnion as bs with
                | some r => some ((Data.B na, Data.I (x + y)) :: r)
                | none => none
            | _, _ => none                                   -- :170-171 pfromData ⇒ perror
          else if na < nb then                               -- :176-177
            match tokensUnion as ((kb, vb) :: bs) with
            | some r => some ((ka, va) :: r)
            | none => none
          else                                               -- :178
            match tokensUnion ((ka, va) :: as) bs with
            | some r => some ((kb, vb) :: r)
            | none => none
      | _, _ => none                                         -- :166-167 pasByteStr ⇒ perror
  termination_by a b => a.length + b.length

/-- `ptokensForCurrencySymbol` — ProgrammableLogicBase.hs:1345-1364.

Extract one policy's token map out of a CS-sorted value, early-exiting once the
sorted list passes the target (:1360).  `pfromData (pfstBuiltin # mintCsPair)`
forces the key to be `Data.B` (:1356); `pto (pfromData (psndBuiltin #
mintCsPair))` forces the matched value to be a `Data.Map` (:1359).  Absent
policy ⇒ exactly `pnil` (:1360, :1362). -/
def tokensForCS (target : CurrencySymbol) : Value → Option Tokens
  | [] => some []                                            -- :1362
  | (k, v) :: rest =>
      match k with
      | Data.B cs =>
          if cs == target then                               -- :1357-1358
            match v with
            | Data.Map toks => some toks                     -- :1359
            | _ => none                                      -- :1359 pto/pfromData ⇒ perror
          else if target < cs then some []                   -- :1360 (sorted early exit)
          else tokensForCS target rest                       -- :1360
      | _ => none                                            -- :1356 pfromData ⇒ perror

/-- `ptokenPairsContain` — ProgrammableLogicBase.hs:1381-1411.
"`actualTokens` covers the signed quantities required by `requiredTokens`."

Fidelity details:
* `requiredQty` is forced on EVERY path (:1393) so the required value must be
  `Data.I`; `requiredTokenName` is forced only where compared, so in the
  actual-exhausted case (:1407) the required KEY is never inspected — the model
  must not inspect it either;
* symmetrically `actualQty` is forced only inside the equal-name branch
  (:1400), so the `<` branch (:1403) must not require `Data.I` on the actual
  side;
* a negative/zero requirement is satisfied by nothing (:1404, :1407). -/
def tokensContain : Tokens → Tokens → Option Bool
  | _, [] => some true                                       -- :1410
  | actual, (kr, vr) :: rrest =>
      match vr with
      | Data.I rq =>
          match actual with
          | [] =>                                            -- :1407
              if 0 ≥ rq then tokensContain [] rrest else some false
          | (ka, va) :: arest =>
              match ka, kr with
              | Data.B na, Data.B nr =>
                  if na == nr then                           -- :1399
                    match va with
                    | Data.I aq =>                           -- :1400
                        if aq ≥ rq then tokensContain arest rrest else some false
                    | _ => none                              -- :1397 pfromData ⇒ perror
                  else if na < nr then                       -- :1402-1403
                    tokensContain arest ((kr, vr) :: rrest)
                  else                                       -- :1404
                    if 0 ≥ rq then tokensContain ((ka, va) :: arest) rrest
                    else some false
              | _, _ => none                                 -- :1392/:1396 pfromData ⇒ perror
      | _ => none                                            -- :1393 pfromData ⇒ perror
  termination_by a r => a.length + r.length

/-- `psubtractTokens` — ProgrammableLogicBase.hs:1689-1745 (local to
`pvalueEqualsDeltaCurrencySymbol`).  Signed per-token-name difference
`input − output`, omitting zeroes (:1714-1715).

Fidelity details:
* both names are forced by the `#<=` comparison at :1707, so both keys must be
  `Data.B` on every visited cell;
* the equal-name test at :1710 is on the raw `Data` (`inputTokenName #==
  outputTokenName`); with both keys `Data.B` that is exactly byte equality, so
  the model tests `ni == no`;
* the output-exhausted case **re-emits the current input pair** (:1740) — this
  is the "item-1 accounting fix" the entry-point docstring at :1287-1288 calls
  out (returning `inputRest` alone silently dropped a token and let a seize move
  it out of the base address undetected);
* quantities are forced per branch only: both on equal names (:1712), the input
  one on `input < output` (:1722), the output one on `output < input` (:1729). -/
def subtractTokens : Tokens → Tokens → Option Tokens
  | [], outs => negateTokens outs                            -- :1744
  | (ki, vi) :: irest, [] => some ((ki, vi) :: irest)        -- :1740
  | (ki, vi) :: irest, (ko, vo) :: orest =>
      match ki, ko with
      | Data.B ni, Data.B no =>
          if ni ≤ no then                                    -- :1707
            if ni == no then                                 -- :1710
              match vi, vo with
              | Data.I qi, Data.I qo =>
                  let diff := qi - qo                        -- :1712
                  if diff == 0 then subtractTokens irest orest        -- :1714-1715
                  else
                    match subtractTokens irest orest with
                    | some r => some ((Data.B ni, Data.I diff) :: r)  -- :1716-1719
                    | none => none
              | _, _ => none                                 -- :1712 pfromData ⇒ perror
            else                                             -- :1721-1726 (input-only token)
              match vi with
              | Data.I qi =>
                  match subtractTokens irest ((ko, vo) :: orest) with
                  | some r => some ((Data.B ni, Data.I qi) :: r)
                  | none => none
              | _ => none
          else                                               -- :1728-1732 (output-only token)
            match vo with
            | Data.I qo =>
                match subtractTokens ((ki, vi) :: irest) orest with
                | some r => some ((Data.B no, Data.I (0 - qo)) :: r)
                | none => none
            | _ => none
      | _, _ => none                                         -- :1707 pfromData ⇒ perror
  termination_by i o => i.length + o.length

/-! ## 2. `pvalueEqualsDeltaCurrencySymbol` (:1677-1830) -/

/-- `pcurrencyListHasCS` — ProgrammableLogicBase.hs:1664-1675.  Non-contamination
gate (Aiken Finding 12, :1824-1830): does the CS-sorted currency list hold the
target policy?  Early-exits once the list passes the target (:1672). -/
def currencyListHasCS (target : CurrencySymbol) : Value → Option Bool
  | [] => some false                                         -- :1674
  | (k, _) :: rest =>
      match k with
      | Data.B cs =>
          if cs == target then some true                     -- :1672
          else if target < cs then some false                -- :1672
          else currencyListHasCS target rest                 -- :1672
      | _ => none                                            -- :1671 pfromData ⇒ perror

/-- `remainingProgCSDelta` — ProgrammableLogicBase.hs:1754-1771.  The leftover
currency entries when one side of the value comparison is exhausted: a sorted
value holds each policy at most once, so the leftover is either empty or the
single seized-policy entry; ANYTHING else is value moved outside the seized
policy and `perror`s (:1767 for a second leftover entry, :1768 for a leftover
entry that is not the seized policy).  `neg = true` is the call site at :1822
(`emit = pnegateTokens`, output side); `neg = false` is :1819 (`emit = id`,
input side). -/
def remainingProgCSDelta (neg : Bool) (progCS : CurrencySymbol) : Value → Option Tokens
  | [] => some []                                            -- :1770
  | (k, v) :: rest =>
      match k with
      | Data.B cs =>
          if cs == progCS then                               -- :1764
            match rest with
            | _ :: _ => none                                 -- :1767 second leftover ⇒ perror
            | [] =>
                match v with
                | Data.Map toks => if neg then negateTokens toks else some toks  -- :1767 emit
                | _ => none                                  -- :1767 pfromData ⇒ perror
          else none                                          -- :1768 perror
      | _ => none                                            -- :1764 pfromData ⇒ perror

/-- `goOuter` — ProgrammableLogicBase.hs:1784-1823.  Lock-step walk of the two
CS-sorted currency lists.

Fidelity details, branch for branch:
* `:1791` equal currency symbols (bytes);
  * `:1793` and it IS the seized policy: the REMAINING currency lists must be
    `Data`-equal (`pmapData # … #== pmapData # …`, :1795 — `Data.Map` is
    injective, so that is list equality), then the whole result is
    `psubtractTokens` on the two token maps (:1796) — note it **replaces** the
    accumulator rather than unioning into it, and does **not** recurse; that is
    sound because a sorted value holds the policy at most once, and it is
    mirrored here verbatim;
  * `:1799` and it is NOT the seized policy: the raw token maps must be
    `Data`-equal (`psndBuiltin # … #== psndBuiltin # …`, i.e. no decode at all),
    then recurse on both tails carrying the accumulator; else `perror`;
* `:1806` input CS < output CS: the input-only policy MUST be the seized one
  (`:1808`, else `perror` at :1810), contributing `psubtractTokens ti pnil`
  unioned with the rest of the walk (:1809);
* `:1812-1815` output CS < input CS: symmetric, contributing
  `pnegateTokens to` (:1814), `perror` at :1815 otherwise;
* `:1819` output list exhausted / `:1822` input list exhausted: the leftover is
  handled by `remainingProgCSDelta` **on the full list** (the head entry
  included — the Plutarch code passes `inputValuePairs` / `outputValuePairs`,
  not the destructured tails), unioned with the accumulator.

NOTE (vestigial accumulator, recorded not "fixed"): `diffAccumulator` is `pnil`
at the only entry point (:1829) and no branch ever unions into it, so it is
always `pnil` in practice.  It is kept in the model because it is in the
validator. -/
def valueDeltaGo (progCS : CurrencySymbol) : Value → Value → Tokens → Option Tokens
  | [], outs, acc =>                                         -- :1822
      match remainingProgCSDelta true progCS outs with
      | some d => tokensUnion d acc
      | none => none
  | (ki, vi) :: irest, [], acc =>                            -- :1819
      match remainingProgCSDelta false progCS ((ki, vi) :: irest) with
      | some d => tokensUnion d acc
      | none => none
  | (ki, vi) :: irest, (ko, vo) :: orest, acc =>
      match ki, ko with
      | Data.B ci, Data.B co =>
          if ci == co then                                   -- :1791
            if ci == progCS then                             -- :1793
              if irest == orest then                         -- :1795
                match vi, vo with
                | Data.Map ti, Data.Map to => subtractTokens ti to   -- :1796
                | _, _ => none
              else none                                      -- :1797 perror
            else
              if vi == vo then valueDeltaGo progCS irest orest acc   -- :1799
              else none                                      -- :1799 perror
          else if ci < co then                               -- :1806
            if ci == progCS then                             -- :1808
              match vi with
              | Data.Map ti =>
                  match subtractTokens ti [] with            -- :1809
                  | some d =>
                      match valueDeltaGo progCS irest ((ko, vo) :: orest) acc with
                      | some r => tokensUnion d r
                      | none => none
                  | none => none
              | _ => none
            else none                                        -- :1810 perror
          else
            if co == progCS then                             -- :1813
              match vo with
              | Data.Map to =>
                  match negateTokens to with                 -- :1814
                  | some d =>
                      match valueDeltaGo progCS ((ki, vi) :: irest) orest acc with
                      | some r => tokensUnion d r
                      | none => none
                  | none => none
              | _ => none
            else none                                        -- :1815 perror
      | _, _ => none                                         -- :1787/:1791 pfromData ⇒ perror
  termination_by i o _ => i.length + o.length

/-- `pvalueEqualsDeltaCurrencySymbol` — ProgrammableLogicBase.hs:1683-1830.
The non-contamination gate first (:1827-1830: the paired INPUT must actually
hold the seized policy), then the lock-step walk from an empty accumulator
(:1829). -/
def valueDelta (progCS : CurrencySymbol) (inV outV : Value) : Option Tokens :=
  match currencyListHasCS progCS inV with
  | some true => valueDeltaGo progCS inV outV []             -- :1829
  | some false => none                                       -- :1830 ptraceInfoError
  | none => none

/-! ## 3. `processThirdPartyTransfer` (:1492-1545)

CREDENTIAL COMPARISONS ARE `Data` COMPARISONS.  Both credential tests on this
path compare *encodings*, never decoded values:

* `:1445-1447` — `inputCredentialData #== pforgetData (pdata progLogicCred)`,
  where `inputCredentialData` is reached by raw `pasConstr`/`phead` field
  access on the input `TxOut` (`:1443-1445`) and `progLogicCred` came out of the
  params datum through `punsafeCoerce` (`:1305-1308`), i.e. is un-validated
  `Data`;
* `:1516` — `paddressCredential programmableOutputAddress #== progLogicCred`;
  `PCredential`'s `PEq` is derived through `PIsData`, so this too is `Data`
  equality.

The model therefore carries the base credential as a `Data` (`baseData`) and
compares `IsData.toData (payCred o)` against it.  Decoding `baseData` into a
`Credential` first would make the model STRICTER than the bytecode (a
malformed params field would abort the model, while the bytecode would simply
never match it, classify every input as non-base, and can then still accept) —
that divergence would falsify `seizeModel_faithful`.  `WSC/Props/P2_Seize.lean`
closes the gap on the property side with the hypothesis
`IsData.toData base = baseData`. -/

/-- `go2` — ProgrammableLogicBase.hs:1510-1521.  Accumulate the seized policy's
token map over the RESIDUAL outputs (those left after pairing) that sit at the
base credential.  `pmatch (pfromData programmableOutput)` (:1514) is a full
`TxOut` field access; non-base outputs are skipped (:1518). -/
def residualBaseTokens (progCS : CurrencySymbol) (baseData : Data) :
    List TxOut → Option Tokens
  | [] => some []                                            -- :1520
  | o :: rest =>
      if IsData.toData (WSC.payCred o) == baseData then      -- :1516
        match tokensForCS progCS o.txOutValue, residualBaseTokens progCS baseData rest with
        | some t, some r => tokensUnion t r                   -- :1517
        | _, _ => none
      else residualBaseTokens progCS baseData rest            -- :1518

/-- `go` (:1528-1541) together with
`pcheckCorrespondingThirdPartyTransferInputsAndOutputs` (:1438-1475): walk
EVERY transaction input, pair each base-credential input with the next
continuing output, and accumulate the seized-policy delta.  Returns the residual
outputs and the final accumulator — exactly the two arguments `go`'s nil case
hands to `checkBalanceInvariant` (:1542).

Fidelity details:
* `:1450` `plet (… (phead # programmableOutputs))` is evaluated BEFORE the
  address/datum checks and `plet` is strict, so an exhausted output list is an
  immediate `perror` — hence `| [] => none` rather than "skip";
* `:1460-1461` full-address equality (staking credential included) and
  `:1462-1463` `programmableInputRest #== programmableOutputRest`, which is the
  `Data` list `[value?, datum, refScript]` MINUS the value: `inputTxOutFieldsRest`
  is `tail` of the field list (so it starts at the value, :1451-1452) and
  `programmableInputRest` is `tail` of THAT (:1456-1457), i.e. `[datum,
  refScript]`.  So datum and reference script are compared, the value is not;
* `:1469` any failure of that conjunction is `perror`, not `False`;
* `:1475` a non-base input is skipped WITHOUT consuming an output. -/
def seizeWalk (progCS : CurrencySymbol) (baseData : Data) :
    List TxInInfo → List TxOut → Tokens → Option (List TxOut × Tokens)
  | [], outs, acc => some (outs, acc)                        -- :1542 (nil case of `go`)
  | i :: rest, outs, acc =>
      let inp := i.txInInfoResolved
      if IsData.toData (WSC.payCred inp) == baseData then    -- :1446-1447
        match outs with
        | [] => none                                         -- :1450 phead of pnil ⇒ perror
        | o :: os =>
            if inp.txOutAddress == o.txOutAddress &&         -- :1460-1461
               inp.txOutDatum == o.txOutDatum &&             -- :1462-1463
               inp.txOutReferenceScript == o.txOutReferenceScript then
              match valueDelta progCS inp.txOutValue o.txOutValue with   -- :1466
              | some d =>
                  match tokensUnion d acc with               -- :1467
                  | some acc' => seizeWalk progCS baseData rest os acc'
                  | none => none
              | none => none
            else none                                        -- :1469 perror
      else seizeWalk progCS baseData rest outs acc            -- :1475

/-- `processThirdPartyTransfer` — ProgrammableLogicBase.hs:1499-1545, including
`checkBalanceInvariant` (:1502-1508).  Note :1508: a FAILED containment check is
`perror`, not `False`, so it is `none` here. -/
def processThirdPartyTransfer (progCS : CurrencySymbol) (baseData : Data)
    (inputs : List TxInInfo) (progOutputs : List TxOut) (minted : Tokens) : Option Bool :=
  match seizeWalk progCS baseData inputs progOutputs [] with  -- :1545
  | none => none
  | some (residual, acc) =>
      match tokensUnion acc minted with                       -- :1542
      | none => none
      | some required =>
          match residualBaseTokens progCS baseData residual with  -- :1504
          | none => none
          | some actual =>
              match tokensContain actual required with        -- :1506
              | some true => some true                        -- :1507
              | some false => none                            -- :1508 perror
              | none => none

/-! ## 4. Redeemer / datum access — RAW, exactly as the validator does it -/

/-- The four `SeizeAct` fields the seize validator actually reads
(`:1304`): `pdirectoryNodeIdx` (position 0), `poutputsStartIdx` (2),
`pseizeParamsRefIdx` (4), `pissuerWdrlIdx` (5).  Positions 1 (`pinputIdxs`) and
3 (`plengthInputIdxs`) are deliberately NOT read any more — see the comment at
`:1299-1303`. -/
structure SeizeFields where
  dirIdx : Integer
  outStart : Integer
  paramsIdx : Integer
  issuerIdx : Integer
deriving Repr, DecidableEq

/-- Redeemer access, mirroring `:1294` + `:1297-1304`.

`red = pfromData $ punsafeCoerce @(PAsData PProgrammableLogicGlobalRedeemer)
(pto pscriptContext'redeemer)` (:1294) — an UNCHECKED coercion — and
`PProgrammableLogicGlobalRedeemer` gets `PlutusType` via `DeriveAsDataStruct`
(:1158).  Consequences, all mirrored here and NONE of them shared with
`WSC/Redeemer.lean`'s strict `IsData PLGRedeemer`:

* `pasConstr` on a non-`Constr` redeemer errors ⇒ `none`;
* constructor index 0 is `PTransferAct`, which the seize validator rejects
  outright (`:1298 ptraceInfoError "seize validator invoked with TransferAct"`)
  ⇒ `none`;
* **constructor fall-through:** the generated dispatch tests index 0 and takes
  the LAST constructor as its fallback, so ANY index ≠ 0 — not just 1 — is
  treated as `PSeizeAct`.  This is the same decode gap recorded for the minting
  policy in `WSC/Props/P4_Minting.lean`'s header; here it cannot be dodged
  (the seize validator must read the redeemer's indices), so it is modelled;
* fields are reached by a raw `phead`/`ptail` chain: a field list of length ≥ 6
  is required, extra fields are ignored, and only the four fields actually read
  need to be `Data.I`.  Positions 1 and 3 may be arbitrary `Data`. -/
def seizeFieldsOf : Data → Option SeizeFields
  | Data.Constr 0 _ => none                                  -- :1298
  | Data.Constr _ (f0 :: _ :: f2 :: _ :: f4 :: f5 :: _) =>   -- :1304 raw positional access
      match f0, f2, f4, f5 with
      | Data.I d, Data.I o, Data.I p, Data.I w => some ⟨d, o, p, w⟩
      | _, _, _, _ => none                                   -- pfromData on a non-I index ⇒ perror
  | _ => none                                                -- short field list / pasConstr ⇒ perror

/-- `phasCSH` — ProgrammableLogicBase.hs:754-757.  **NOT** a membership test:
it reads the FIRST NON-ADA entry only (`phead # (ptail # value')`) and compares
its currency symbol.  A value with fewer than two entries makes `ptail`/`phead`
error.  (The docstring at :735-753 is explicit that a `False` here must never be
read as "policy absent everywhere".) -/
def hasCSH (cs : CurrencySymbol) : Value → Option Bool
  | _ :: (Data.B cs', _) :: _ => some (cs' == cs)            -- :756-757
  | _ => none                                                -- :756 phead/ptail ⇒ perror

/-- The two params-datum fields the seize validator reads (`:1305`):
`pdirectoryNodeCS` (position 0) and `pprogLogicCred` (position 1).

`pparamsAtRefIdx` (:824-838) reaches the datum through `punsafeCoerce
@(PAsData PProgrammableLogicGlobalParams)`; `PProgrammableLogicGlobalParams`
derives `PlutusType` via `DeriveAsDataRec`, i.e. the datum is a `Data.List`
(ProtocolParams.hs:84-96, mirrored in WSC/Redeemer.lean:296-311) and fields are
raw positional accesses.  So:

* only positions 0 and 1 need exist — positions 2 (`globalLogicCred`) and 3
  (`seizeLogicCred`) are never read on the seize path and need not be
  well-formed, and a longer list is accepted;
* position 0 is forced by `pfromData pdirectoryNodeCS` at :1329 ⇒ `Data.B`;
* **position 1 is never decoded.**  `progLogicCred <- plet $ pfromData
  pprogLogicCred` (:1308) is, for a `DeriveAsDataStruct` type, the identity on
  the underlying `Data`; the only use is `pforgetData (pdata progLogicCred)`
  (:1447) and the `PEq` at :1516 — both `Data` comparisons.  The model
  therefore keeps it as `Data`. -/
def paramsDirCSAndProgCred : Data → Option (CurrencySymbol × Data)
  | Data.List (Data.B dcs :: r_plc :: _) => some (dcs, r_plc)
  | _ => none

/-- `pparamsAtRefIdx` — ProgrammableLogicBase.hs:824-838, called at :1307.
Reference input at the redeemer-supplied index (via raw `pdropList`, so a
negative index is CLAMPED, not rejected — contrast `Issuance.hs`'s
`pcheckedDrop`), authenticated by `phasCSH` (:832), then the inline datum is
read raw (:833-835); a missing/non-inline datum errors (:836) and a failed
authentication errors (:838). -/
def paramsAtRefIdx (ppCS : CurrencySymbol) (refs : List TxInInfo) (idx : Integer) :
    Option (CurrencySymbol × Data) :=
  match headM (dropL idx refs) with
  | none => none                                             -- :826 phead ⇒ perror
  | some i =>
      match hasCSH ppCS i.txInInfoResolved.txOutValue with
      | some true =>
          match i.txInInfoResolved.txOutDatum with
          | .OutputDatum d => paramsDirCSAndProgCred d       -- :833-835
          | _ => none                                        -- :836 ptraceInfoError
      | _ => none                                            -- :838 ptraceInfoError

/-- The two directory-node-datum fields the seize validator reads (`:1313-1316`):
`pkey` (position 0) and `pissuerLogicScript` (position 3).

`PDirectorySetNode` is reached through `punsafeCoerce @(PAsData
PDirectorySetNode) (pto seizeDat')` (:1317) and derives `PlutusType` via
`DeriveAsDataRec`, so the datum is a `Data.List` of five fields
(PTokenDirectory.hs:167-174, mirrored in WSC/Redeemer.lean:258-273) accessed
positionally.  Only positions 0 and 3 are read here, so positions 1, 2, 4 need
not be well-formed and a longer list is accepted.  Position 0 is forced by
`pfromData directoryNodeDatumFKey` at :1319 ⇒ `Data.B`; position 3 is compared
as raw `Data` against a withdrawal key at :1327-1328 and is therefore NOT
decoded. -/
def nodeKeyAndIssuer : CardanoLedgerApi.V2.OutputDatum → Option (CurrencySymbol × Data)
  | .OutputDatum (Data.List (Data.B key :: _ :: _ :: issuer :: _)) => some (key, issuer)
  | _ => none                                                -- :1312 pmatch POutputDatum ⇒ perror

/-- Condition 3 — ProgrammableLogicBase.hs:1323-1328.  The node datum's
`issuerLogicScript` field, as raw `Data`, must equal the credential key of the
withdrawal entry at the redeemer-supplied `pissuerWdrlIdx` (raw `pdropList`,
negative clamped; `phead` of an exhausted list errors).  In CLAB
`txInfoWdrl : List (Credential × Integer)` (V3/Governance.lean:409) and the
`Data` of the key is `IsData.toData cred`. -/
def issuerInvoked (issuerData : Data) (idx : Integer)
    (wdrl : List (Credential × Integer)) : Option Bool :=
  match headM (dropL idx wdrl) with
  | none => none                                             -- :1328 phead ⇒ perror
  | some e => some (IsData.toData e.1 == issuerData)         -- :1327-1328

/-- Condition 1 — `pisRewardingScript (pdata pscriptContext'scriptInfo)` at
:1321.  Definition: `(pfstBuiltin # (pasConstr # pforgetData term)) #== 2`
(plutarch-onchain-lib `Plutarch/Core/Integrity.hs:69-70`) — the `ScriptInfo`
constructor index only, fields ignored.  CLAB's `ScriptInfo` uses the Plutus
constructor order (`MintingScript = 0`, `SpendingScript = 1`,
`RewardingScript = 2`, …; V3/Contexts.lean:161-168). -/
def isRewardingScript (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .RewardingScript _ => true
  | _ => false

/-! ## 5. The validator -/

/-- **The model of `mkProgrammableSeize`** — ProgrammableLogicBase.hs:1290-1331,
in source order.  `none` = `perror`; `some b` = the value of `pand'List
conditions`, which `pvalidateConditions` turns into `()` when `true` and
`perror` when `false` (`ValidationLogic.hs:164-168`).

Because `pand'List` folds with the STRICT `pand'` (`Utils.hs:276-280`), all four
conditions are evaluated on every run; the `do`-block's short-circuiting on
`none` is therefore verdict-equivalent (any modelled error, in any condition,
makes the run unsuccessful either way). -/
def seizeRun (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : Option Bool :=
  let tx := ctx.scriptContextTxInfo
  match seizeFieldsOf ctx.scriptContextRedeemer with          -- :1294, :1297-1304
  | none => none
  | some f =>
      match paramsAtRefIdx protocolParamsCS tx.txInfoReferenceInputs f.paramsIdx with
      | none => none                                         -- :1305-1307
      | some (dirCS, baseData) =>                            -- :1308 progLogicCred
          let remainingOutputs := dropL f.outStart tx.txInfoOutputs             -- :1309
          match headM (dropL f.dirIdx tx.txInfoReferenceInputs) with            -- :1310
          | none => none
          | some dirNode =>
              match nodeKeyAndIssuer dirNode.txInInfoResolved.txOutDatum with   -- :1311-1317
              | none => none
              | some (seizedCS, issuerData) =>
                  match tokensForCS seizedCS tx.txInfoMint with                 -- :1318-1319
                  | none => none
                  | some minted =>
                      match processThirdPartyTransfer seizedCS baseData
                              tx.txInfoInputs remainingOutputs minted with      -- :1322
                      | none => none
                      | some c2 =>
                          match issuerInvoked issuerData f.issuerIdx tx.txInfoWdrl with
                          | none => none                                        -- :1326-1328
                          | some c3 =>
                              match hasCSH dirCS dirNode.txInInfoResolved.txOutValue with
                              | none => none                                    -- :1329
                              | some c4 =>
                                  some (isRewardingScript ctx && c2 && c3 && c4) -- :1320-1331

/-- The model's VERDICT: the seize validator succeeds iff `pvalidateConditions`
returns `()`, i.e. iff no `perror` was reached and the conjunction is `true`. -/
def seizeModel (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  seizeRun protocolParamsCS ctx == some true

/-! ## 6. Derived projections used by P2's statement

These are NOT part of the model's verdict; they name the two quantities P2
quantifies over, computed the same way the validator computes them, so that
`WSC/Props/P2_Seize.lean` can talk about "the seized policy" and "the paired
outputs" without re-deriving them. -/

/-- The seized policy: the `key` of the directory node at the redeemer's
`pdirectoryNodeIdx` (:1310-1319).  This is ARCHITECTURE.md §3-P2's
`seizedPolicyOf`.  It reads only ledger fields — a redeemer-supplied index used
solely to INDEX a reference input, and a `Data` field of that input's datum. -/
def seizedPolicyOf (ctx : ScriptContext) : Option CurrencySymbol :=
  match seizeFieldsOf ctx.scriptContextRedeemer with
  | none => none
  | some f =>
      match headM (dropL f.dirIdx ctx.scriptContextTxInfo.txInfoReferenceInputs) with
      | none => none
      | some i =>
          match nodeKeyAndIssuer i.txInInfoResolved.txOutDatum with
          | none => none
          | some (key, _) => some key

/-- The base (mini-ledger) payment credential the validator actually uses: field
1 of the authenticated protocol-params datum, as raw `Data` (:1305-1308).  See
the `Data`-comparison note in §3 for why this is NOT decoded. -/
def progLogicCredDataOf (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) :
    Option Data :=
  match seizeFieldsOf ctx.scriptContextRedeemer with
  | none => none
  | some f =>
      match paramsAtRefIdx protocolParamsCS ctx.scriptContextTxInfo.txInfoReferenceInputs
              f.paramsIdx with
      | none => none
      | some (_, baseData) => some baseData

/-- The paired-output cursor: `txInfoOutputs` from the redeemer's
`poutputsStartIdx` onward (:1309), with `pdropList`'s negative-clamping. -/
def pairedOutputsOf (ctx : ScriptContext) : Option (List TxOut) :=
  match seizeFieldsOf ctx.scriptContextRedeemer with
  | none => none
  | some f => some (dropL f.outStart ctx.scriptContextTxInfo.txInfoOutputs)

/-! ## 7. THE TRUST DELTA — the one unproven bridge

Everything else in the WSC library is either machine-checked against the real
compiled bytecode or an axiom in `WSC/Honest.lean`'s audited ledger/deployment
set.  This axiom is neither, and it is deliberately NOT in `Honest.lean`: it is
a different KIND of assumption (a compilation-fidelity claim about a hand
transcription), and mixing it into the honest-deployment set would hide that. -/

/-- The real bytecode's run of `programmableSeize` on `(protocolParamsCS, ctx)`,
metered at `n` CEK steps.  `programmableSeize` is the imported production flat
(`WSC/flats/programmableSeize.flat`, sha256 in `WSC/flats/PROVENANCE.md`) and
`seizeInputs` is its audited parameter/context application order — both from
`WSC/Prep/Seize.lean`.  This is the same machine `WSC/Prep/Seize.lean`'s
`appliedSeize.exec` uses, with the step count left free. -/
def seizeExecAt (n : Nat) (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) :
    PlutusCore.UPLC.CekMachine.State :=
  PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableSeize.script
    (WSC.seizeInputs protocolParamsCS ctx) n

/-- **The bytecode accepts, UNBOUNDEDLY** — there is some step count at which the
production `programmableSeize` bytecode halts successfully on this context.

WHY THIS AND NOT `appliedSeize.prop`.  The obvious phrasing of the faithfulness
axiom, `seizeModel params ctx = true ↔ isSuccessful (appliedSeize.prop params
ctx)`, would be **FALSE**, and measurably so: `WSC/Prep/Seize.lean` preps at
budget 600, and the E2 vacuity probe PROVED that no context is accepted within
600 steps (`WSC/STATUS.md` P2 row), while `seizeModel` is satisfiable.  Writing
that axiom would therefore have imported a contradiction.  Quantifying the step
count instead states exactly the intended claim — agreement with the script the
node runs, whose only budget is the transaction's ExUnits — and, as a bonus,
makes P2-via-the-model the ONLY property in this library that is not
budget-bounded (contrast ADDENDUM E1 and every other row of `WSC/STATUS.md`). -/
def seizeAcceptsUnbounded (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : Prop :=
  ∃ n, isSuccessful (seizeExecAt n protocolParamsCS ctx)

/-- **THE ONE UNPROVEN BRIDGE: `seizeModel` computes what the compiled
`programmableSeize` bytecode computes.**

Read `WSC/STATUS.md`'s P2 row with this axiom in hand: P2 is proven *about the
model*, and only this axiom turns that into a statement about the deployed
script.

**Evidence FOR it.**
1. *Line-by-line transcription.*  Every clause of every definition above cites
   the `ProgrammableLogicBase.hs` line it mirrors (file read 2026-07-25 at the
   wsc-poc worktree `new-session-3c417d`), including all fourteen `perror`
   paths (`:1298`, `:1450`, `:1469`, `:1508`, `:1767`, `:1768`, `:1797`,
   `:1799`, `:1810`, `:1815`, `:1830`, `:836`, `:838`, `:1312`) and the four
   raw-`Data` decode gaps that a naive use of `WSC/Redeemer.lean`'s strict
   mirrors would have got WRONG (constructor fall-through in `seizeFieldsOf`;
   partial params datum in `paramsDirCSAndProgCred`; partial node datum in
   `nodeKeyAndIssuer`; `Data`-level credential comparison in `seizeWalk` /
   `residualBaseTokens`).
2. *Differential agreement on the golden suite.*  `WSC/Model/SeizeDiff.lean`
   runs `seizeModel` against the recorded verdicts of the production bytecode
   (executed at PV11 by `PlutusLedgerApi.V3.evaluateScriptCounting`, and
   independently reproduced to the ExBudget unit by PlutusCoreBlaster's CEK —
   `WSC/goldens/MANIFEST.md`) on **all three seize goldens: 2 accepting and 1
   rejecting**, plus the 10 non-seize goldens as off-purpose controls.  Every
   comparison is closed by `native_decide`.  The rejecting golden
   (`seize-1-input-missing-residual-output-REJECT`) is the load-bearing one: a
   model that accepted everything would still pass the two accepting goldens.
3. *Strictness argument S1* (file header): on an accepting run every value the
   model forces is forced by the bytecode too, so the strict-`Option` model
   cannot manufacture an error the bytecode did not have.

**What would discharge it.**  A `by blaster` theorem `seizeModel params ctx =
true ↔ isSuccessful (appliedSeize.prop params ctx)` over the real prepped
bytecode.  That is blocked TODAY, and the block is measured, not assumed:
`#prep_uplc` at budget 2,000 did not finish in 77 min and at 9,000 not in
62 min, the cheapest accepting seize run needs 2,570 CEK steps, and the two
budgets whose prep DID complete (600, 1,000) have vacuity probes returning
`Valid` for "no accepting context exists"
(`WSC/goldens/K-MEASUREMENTS.md` §5.1/§5.2, `WSC/STATUS.md` P2 row).  Task Y1
further showed the binding constraint is Z3 SEARCH over a fully symbolic `Data`
`ScriptContext`, not prep: at or above the minimal accepting step count, every
bytecode obligation stayed `Undetermined` with 3,300 s of solver time.  The
shaped-context route (fixed list spines + concrete redeemer indices, security
fields left symbolic) is the identified next lever.

**The risk, plainly.**  This axiom is a hand transcription of ~340 lines of
Plutarch into Lean.  If the transcription is wrong in a way the three seize
goldens do not exercise, P2 is wrong.  Concretely un-exercised by the goldens:
the constructor fall-through path (no golden uses an out-of-range redeemer
tag), the negative-index clamping of `pdropList` (no golden uses a negative
index), the `remainingProgCSDelta` `perror` branches (:1767/:1768), and the
laziness/strictness boundary of S1.  A transcription error in `perror`
POLARITY — modelling a `perror` as `false`, or vice versa — would be
invisible on accepting goldens; that is why every `perror` above is separately
line-cited, and why the rejecting golden is in the differential suite.

────────────────────────────────────────────────────────────────────────────
APPENDED (task Z6, 2026-07-25) — WHAT THE SHAPED UPLC PROOF DOES AND DOES NOT
DO FOR THIS AXIOM.
────────────────────────────────────────────────────────────────────────────
`WSC/Props/Shaped/P2Shaped.lean` now proves BOTH conjuncts of P2 **against the
real compiled `programmableSeize` bytecode**, with no reference to this model and
no use of this axiom (`#print axioms` there lists only `propext, sorryAx,
Classical.choice, Quot.sound` — `sorryAx` being `blaster`'s `admit`).  The proof
is bounded twice: CEK budget 3800 and the transaction shape SHAPE S1
(`WSC/Shaped/SeizeShaped.lean`).

**It does NOT discharge this axiom.**  The axiom is unbounded in BOTH dimensions
that the shaped theorem bounds: it quantifies over every `ScriptContext` and over
every step count.  A shaped, budgeted theorem cannot imply it, and there is no
shape-coverage argument in this library that would let it (that gap is recorded
as limit 1 of WSC/SHAPING-RESULTS.md §7).  So P2-via-this-model remains the only
UNBOUNDED P2 statement, and it still rests entirely on this axiom.

**What it DOES do — it narrows the residual risk, in four specific ways.**
1. *The `#prep_uplc` justification quoted above ("what would discharge it") is
   now obsolete as a description of the tooling limit.*  Shaping makes the prep
   cost essentially budget-independent: the shaped prep at budget 3800 takes
   ~3 s, against "did not finish in 77 min at 2,000".  What remains blocking is
   only the SHAPE-FREE part of the obligation, not prep.
2. *Two of the four risks this docstring names as "un-exercised by the goldens"
   are now exercised by machine-checked runs of the real bytecode.*  Concretely,
   `WSC/Props/Shaped/P2Shaped.lean`'s four concrete instances add, beyond the
   three goldens, an accepting run with a NON-ZERO seize-time mint of the seized
   policy, an accepting run whose residual base output over-covers the delta, a
   ledger-legal ESCAPE attempt (rejected at 3800 and at 20000 steps), and a
   ledger-legal attempt to re-point the continuing output at a DIFFERENT staking
   credential (also rejected at both budgets).  The last two probe exactly the
   `perror` POLARITY of `checkBalanceInvariant` (:1508) and of the per-pair
   conjunction (:1469) that this docstring flags as the invisible-error risk.
3. *The two conclusions agree.*  On SHAPE S1 the bytecode satisfies the SAME two
   predicates (`WSC.seizeStructurePreserved`,
   `WSC.P2.sumOutAtBase ≥ sumInAtBase + WSC.mintOf`) that the model route derives
   from `seizeModel`.  A transcription error that changed P2's meaning would have
   to be invisible on all three goldens AND consistent with the bytecode's
   behaviour on the whole SHAPE S1 class, which is a strictly stronger demand
   than before.
4. *Conjunct 2 is no longer unproven anywhere.*  §5 of
   `WSC/Props/P2_Seize.lean` records `P2b_seized_delta_contained` as NOT proven,
   because bridge lemma B1 is false without ledger canonicity.  At SHAPE S1 that
   canonicity is structural (one token name per policy), so conjunct 2 is a
   theorem about the bytecode on that class.  The general, shape-free conjunct 2
   is still open, and obligations B1/B2 there are still the way to get it.

Nothing above changes the STRENGTH of any statement that cites this axiom; it
changes only how much independent evidence stands behind it.  A reviewer quoting
`P2a_bytecode` should now also read `WSC/Props/Shaped/P2Shaped.lean`'s SCOPE
block, and should note the two routes trade different trust: this axiom is a hand
transcription, the shaped route trusts the solver, `admit`, and the shape. -/
axiom seizeModel_faithful :
    ∀ (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext),
      seizeModel protocolParamsCS ctx = true ↔ seizeAcceptsUnbounded protocolParamsCS ctx

end WSC.SeizeModel
