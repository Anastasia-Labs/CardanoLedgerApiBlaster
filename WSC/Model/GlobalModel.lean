/-
WSC/Model/GlobalModel.lean — SOURCE MODEL of the `TransferAct` path of
`mkProgrammableLogicGlobal` (task Z4, ARCHITECTURE.md §2 route B3).

WHY THIS FILE EXISTS.  P1 (containment) and P6 (Member self-penalization) live
on the global transfer validator, whose accepting runs cost 3,262 / 3,726 CEK
steps (`WSC/goldens/K-MEASUREMENTS.md` §3).  Symbolic `#prep_uplc` at 3,300
never completes and Z3 is Undetermined already at the affordable budget 1,600
(`WSC/STATUS.md` §1, `WSC/Props/P5_NonMember.lean`).  So P1/P6 are proved here
against a HAND-TRANSCRIBED model of the validator, bridged to the bytecode by
ONE explicit axiom (`WSC/Props/P1_Transfer.lean`, `globalModel_faithful`).

FIDELITY DISCIPLINE (what makes this a model of the REAL validator, not an
invented abstraction):

1. Every clause below cites the Plutarch line it transcribes.  Source of truth:
   `/home/gumbo/iohk/wsc-poc/.claude/worktrees/new-session-3c417d/src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs`
   read on 2026-07-25 (line numbers in older WSC docs drift by ~2; the numbers
   here are what that file actually contains).
2. `perror` is modelled by `Option.none`, and it PROPAGATES: the validator's
   `plet`s are strict (a `plet` compiles to an applied lambda, and the CEK
   machine is strict in applications), so an error anywhere in the value
   computation is an error of the whole script.  A `false` verdict and an error
   both mean "the transaction is rejected" (`pvalidateConditions` errors on
   `false`), so the top-level model collapses both to `false` — but the
   intermediate `Option`s are what keep the ERROR-not-SKIP behaviour of
   `pvalueFromCred` (ARCHITECTURE.md §3-P1 lemma L1.3) faithful.
3. Pattern-match recursions only — no `List.all/any/find?/foldl`.  This is the
   blaster-friendly discipline of `WSC/SPIKE-FINDINGS.md` layer F, and it is
   also what makes the `native_decide` differential test cheap.
4. The five CIP-153 builtin operations the validator calls
   (`punValueData`, `punionValue`, `pvalueContains`, `pvalueData`,
   `pinsertCoin`) are NOT re-invented here: they are PlutusCoreBlaster's
   denotations from `PlutusCore/Value/Basic.lean` (branch `cip153-value-builtins`
   @ 9f9ca8c), i.e. the very functions the CEK machine runs when it executes the
   real bytecode, and the P1 proof reasons about them through the 51 PROVED
   lemmas of `PlutusCore/Value/Algebra.lean`.  That is why this model bottoms
   out in real builtin semantics.

KNOWN MODELLING DEVIATIONS (all listed, none hidden; every one is also
re-checked empirically by the 4/4 golden differential test in
`WSC/Model/GlobalGoldens.lean`):

* **D-M1 (redeemer fall-through).**  The validator obtains its redeemer by
  `punsafeCoerce` (:1180) and `pmatch`es it (:1183); a `Data` that is neither a
  `Constr 0`- nor a `Constr 1`-shaped `ProgrammableLogicGlobalRedeemer` has
  UNSPECIFIED behaviour there, while the model rejects it (`decodeRedeemer =
  none → false`).  Direction: the model may reject where the bytecode does
  something undefined; it never accepts more.
* **D-M2 (datum decoding is field-wise, not type-wise).**  The validator
  `punsafeCoerce`s the directory-node datum (:887, :1004) and the params datum
  (:835) and then only reads the fields it needs.  The model therefore uses
  LOOSE field extractors (`dirNodeFields`, `paramsFields`) that require only the
  positions actually read, NOT the full 5-field / 4-field mirror decode of
  `WSC/Redeemer.lean`.  The single exception is the params `progLogicCred`
  (position 1), which the model decodes to a `Credential` because the theorems'
  ground-truth vocabulary (`payCred`) is credential-typed; the accept path
  compares it against real ledger addresses, which are always well-formed
  credential encodings, so this costs nothing on the accept path.
* **D-M3 (`ptxSignedByPkh`).**  Comes from an external Plutarch library not
  vendored in the wsc-poc worktree; modelled as membership of the pkh in
  `txInfoSignatories`, its documented meaning.  It only ever guards a
  CONTRIBUTION to the expected value, so a discrepancy could only make the
  model's expected value smaller — the P1 conclusion is monotone in the wrong
  direction for that to hide an escape, which is why L1.3 (error-not-skip) is
  stated and proved.
* **D-M4 (`Data`-level vs decoded comparisons).**  The validator compares raw
  `Data` for credentials (`paymentCredData #== credData`, :426, :637, :665) and
  for the transfer-logic script (:912-915).  The model compares decoded
  `Credential`s where the CLAB type gives them (inputs/outputs) and raw `Data`
  where the validator's own value is raw (the cached transfer script).  Sound
  because CLAB's `IsData Credential` encoding is injective
  (`CardanoLedgerApi/V1/Credential.lean:110-135`).
-/
import CardanoLedgerApi.V3
import WSC.Redeemer
import WSC.Spec
import PlutusCore.Value.Algebra

namespace WSC.Model

open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol TokenName Value MintValue
                          ScriptContext ScriptInfo ScriptHash StakingCredential
                          TxInInfo TxInfo PubKeyHash Withdrawals)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## 0. Representation

The validator's internal accumulators are all raw sorted currency-pair lists

    `PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (PMap 'Sorted PTokenName PInteger)))`

which is EXACTLY CLAB's `Value = List (Data × Data)`
(`CardanoLedgerApi/V1/Value.lean:23`), with `fst = Data.B cs` and
`snd = Data.Map tokenPairs`.  No conversion layer is needed, and the ground-truth
lookup `CardanoLedgerApi.V2.valueOf` applies to model values directly. -/

/-- A raw currency-pair list (= CLAB `Value`; see the note above). -/
abbrev CsPairs := Value

/-- `phead` on a builtin list: `perror` on `[]`
(the CEK `headList` denotation, PlutusCoreBlaster
`PlutusCore/UPLC/BuiltinFunctions/List.lean`). -/
def headOpt {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

/-- `ptail` on a builtin list: `perror` on `[]`. -/
def tailOpt {α : Type} : List α → Option (List α)
  | [] => none
  | _ :: xs => some xs

/-- `pdropList # idx # l`.  PlutusCoreBlaster's `dropList` denotation is
`xs.drop n.toNat` (`PlutusCore/UPLC/BuiltinFunctions/List.lean:102-110`), so a
NEGATIVE index drops nothing (Lean `Int.toNat` of a negative is `0`) rather than
erroring — the error, when the index is out of range, comes from the `phead`
that always follows. -/
def dropIdx {α : Type} (idx : Integer) (l : List α) : List α := l.drop idx.toNat

/-- `phead # (pdropList # idx # l)` — the indexed lookup idiom used at :830,
:880 and :998. -/
def atIdx {α : Type} (idx : Integer) (l : List α) : Option α :=
  headOpt (dropIdx idx l)

/-! ## 1. `phasCSH` (:754-757)

`pfromData (pfstBuiltin # (phead # (ptail # value'))) #== directoryNodeCS`:
the FIRST NON-ADA policy of the value must be `directoryNodeCS`.  Both the
`ptail` (value with no entries) and the `phead` (value with only the ada entry)
`perror`, and `pfromData` to `PCurrencySymbol` errors on a non-bytestring key —
hence three `none` cases. -/
def hasCSH (cs : CurrencySymbol) : Value → Option Bool
  | [] => none                              -- ptail # pnil
  | _ :: rest =>
      match rest with
      | [] => none                          -- phead # pnil
      | (Data.B cs', _) :: _ => some (cs' == cs)
      | _ => none                           -- pfromData on a non-B key

/-! ## 2. `pisScriptInvokedEntries` (:364-376)

The loop `phead`s the entry list, compares, then `phead`s the TAIL and compares
again before recursing on that tail.  Consequence (fidelity-critical, and the
reason this is not a `Bool`): when the credential is ABSENT the loop runs off the
end of the withdrawal list and `perror`s — it never returns `false`.  The
callers rely on that: a missing script witness must fail validation, not silently
omit the input's value (:389, :440). -/
def scriptInvokedEntries (cred : Credential) : Withdrawals → Option Bool
  | [] => none
  | (c, _) :: rest =>
      if c == cred then some true
      else
        match rest with
        | [] => none
        | (cA, _) :: _ =>
            if cA == cred then some true
            else scriptInvokedEntries cred rest

/-- The one-step formulation of the same walk. -/
def scriptInvokedSimple (cred : Credential) : Withdrawals → Option Bool
  | [] => none
  | (c, _) :: rest => if c == cred then some true else scriptInvokedSimple cred rest

/-- The validator's two-entries-per-iteration unrolling is BEHAVIOURALLY
IDENTICAL to the one-step walk: the second comparison only short-circuits an
iteration that the recursion would have performed anyway, and both formulations
run off the end of the list into `perror`.  (Proved, so the unrolling is not a
place a transcription mistake can hide.) -/
theorem scriptInvokedEntries_eq_simple (cred : Credential) :
    ∀ w : Withdrawals, scriptInvokedEntries cred w = scriptInvokedSimple cred w := by
  intro w
  induction w with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨c, _⟩ := hd
      by_cases h : (c == cred) = true
      · simp [scriptInvokedEntries, scriptInvokedSimple, h]
      · cases tl with
        | nil => simp [scriptInvokedEntries, scriptInvokedSimple, h]
        | cons hd' tl' =>
            obtain ⟨cA, _⟩ := hd'
            by_cases h' : (cA == cred) = true
            · simp [scriptInvokedEntries, scriptInvokedSimple, h, h']
            · simp only [scriptInvokedEntries, scriptInvokedSimple, h, h',
                         Bool.false_eq_true, if_false] at *
              exact ih

/-- `ptxSignedByPkh` (:432; external Plutarch library — deviation D-M3):
membership of the key hash in `txInfoSignatories`. -/
def signedByPkh (pkh : PubKeyHash) : List PubKeyHash → Bool
  | [] => false
  | s :: rest => s == pkh || signedByPkh pkh rest

/-! ## 3. `pvalueFromCred`'s shared per-input gate (`withContributing`, :413-443)

Raw-field access: the resolved output's fields 0/1 are its address and value
(:421-422); the address's fields 0/1 are its payment credential and its
`PMaybeData PStakingCredential` staking credential (:423-424).  Then

* payment credential ≠ `cred` → SKIP the input (:443);
* payment credential = `cred` → the OWNER WITNESS is mandatory:
  * `PStakingHash (PPubKeyCredential pkh)` → signer required, else `perror` (:434);
  * `PStakingHash (PScriptCredential h)` → withdrawal entry required, else
    `perror` (:440);
  * anything else (`PStakingPtr`, and `PNothing` because `pjustData` `phead`s the
    `Nothing` constructor's empty field list — :70-72) → `perror` (:441).

This ERROR-not-SKIP behaviour is exactly lemma L1.3 of ARCHITECTURE.md §3-P1:
every input at the base credential is counted, or the transaction dies. -/
inductive Gate where
  /-- The input contributes; carries its raw value. -/
  | contributes (v : Value)
  /-- The input is not at the base credential; it is skipped. -/
  | skip
  /-- `perror`. -/
  | err
deriving Repr, DecidableEq

def gateInput (base : Credential) (sigs : List PubKeyHash) (wdrl : Withdrawals)
    (i : TxInInfo) : Gate :=
  let o := i.txInInfoResolved
  if WSC.payCred o == base then
    match o.txOutAddress.addressStakingCredential with
    | some (.StakingHash (.PubKeyCredential pkh)) =>
        if signedByPkh pkh sigs then .contributes o.txOutValue else .err
    | some (.StakingHash (.ScriptCredential h)) =>
        (match scriptInvokedEntries (.ScriptCredential h) wdrl with
         | some true => .contributes o.txOutValue
         | _ => .err)
    | _ => .err
  else .skip

/-! ## 4. `pvalueFromCred` — the three-phase hybrid accumulation (:392-484)

Phase 1 `goFind` (:474-483): no contributing input seen yet; `pnil` on exhaustion.
Phase 2 `goRest` (:460-472): exactly one contributing input seen, its RAW value
`Data` held; on exhaustion the result is `ptail # (pasMap # firstVd)` — the
ada entry dropped by position, the pre-PV11 cheap path.
Phase 3 `goBuiltin` (:446-458): two or more contributing inputs; the accumulator
is a CIP-153 builtin `Value` merged with `punionValue`, and on exhaustion it is
bridged back to raw pairs by `pasMap # (pvalueData # (pinsertCoin # "" # "" # 0 # acc))`
— `insertCoin` with amount 0 DELETES, which is how the ada entry is removed
(`PlutusCore/Value/Basic.lean:131-139`). -/

/-- `punValueData # vd` where `vd` is a raw value's `Data` (`Data.Map …`). -/
def unVD (v : Value) : Option PlutusCore.Value.ValueRep :=
  PlutusCore.Value.unValueData (Data.Map v)

/-- Phase 3 (:446-458). -/
def goBuiltin (base : Credential) (sigs : List PubKeyHash) (wdrl : Withdrawals)
    (acc : PlutusCore.Value.ValueRep) : List TxInInfo → Option CsPairs
  | [] =>
      match PlutusCore.Value.insertCoin (ByteString.mk "") (ByteString.mk "") 0 acc with
      | none => none
      | some acc' =>
          match PlutusCore.Value.valueData acc' with
          | Data.Map ps => some ps
          | _ => none
  | i :: xs =>
      match gateInput base sigs wdrl i with
      | .err => none
      | .skip => goBuiltin base sigs wdrl acc xs
      | .contributes vd =>
          match unVD vd with
          | none => none
          | some v =>
              match PlutusCore.Value.unionValue acc v with
              | none => none
              | some acc' => goBuiltin base sigs wdrl acc' xs

/-- Phase 2 (:460-472). -/
def goRest (base : Credential) (sigs : List PubKeyHash) (wdrl : Withdrawals)
    (firstVd : Value) : List TxInInfo → Option CsPairs
  | [] => tailOpt firstVd
  | i :: xs =>
      match gateInput base sigs wdrl i with
      | .err => none
      | .skip => goRest base sigs wdrl firstVd xs
      | .contributes vd =>
          match unVD firstVd, unVD vd with
          | some v₁, some v₂ =>
              match PlutusCore.Value.unionValue v₁ v₂ with
              | none => none
              | some acc => goBuiltin base sigs wdrl acc xs
          | _, _ => none

/-- Phase 1 (:474-483). -/
def goFind (base : Credential) (sigs : List PubKeyHash) (wdrl : Withdrawals) :
    List TxInInfo → Option CsPairs
  | [] => some []
  | i :: xs =>
      match gateInput base sigs wdrl i with
      | .err => none
      | .skip => goFind base sigs wdrl xs
      | .contributes vd => goRest base sigs wdrl vd xs

/-- `pvalueFromCred cred sigs withdrawalEntries inputs` (:406, `goFind # inputs`
at :484). -/
def valueFromCred (base : Credential) (sigs : List PubKeyHash) (wdrl : Withdrawals)
    (inputs : List TxInInfo) : Option CsPairs :=
  goFind base sigs wdrl inputs

/-! ## 5. Datum field extractors (deviation D-M2)

`PDirectorySetNode` is `DeriveAsDataRec`, i.e. a raw `Data.List` of five fields
(`PTokenDirectory.hs:176-186`, mirrored in `WSC/Redeemer.lean:250-256`); the
validator `punsafeCoerce`s the datum and reads only positions 0 (`key`),
1 (`next`) and — in the transfer walk — 2 (`transferLogicScript`, kept RAW because
it is only ever compared with `#==`). -/
def dirNodeFields : Data → Option (CurrencySymbol × CurrencySymbol × Data)
  | Data.List (Data.B k :: Data.B n :: tls :: _) => some (k, n, tls)
  | _ => none

/-- The directory node the walks address by reference-input index: `phead #
(pdropList # idx # refInputs)` (:880, :998), whose resolved output must carry an
inline datum (`POutputDatum` — :881, :999; any other datum constructor is a
`pmatch` failure = `perror`). Returns the node's VALUE (for `phasCSH`) and its
three read fields. -/
def dirNodeAt (idx : Integer) (refs : List TxInInfo) :
    Option (Value × CurrencySymbol × CurrencySymbol × Data) :=
  match atIdx idx refs with
  | none => none
  | some i =>
      match i.txInInfoResolved.txOutDatum with
      | .OutputDatum d =>
          match dirNodeFields d with
          | some (k, n, tls) => some (i.txInInfoResolved.txOutValue, k, n, tls)
          | none => none
      | _ => none

/-- The two params-datum positions the transfer path reads: `directoryNodeCS`
(0) and `progLogicCred` (1) — `ProtocolParams.hs:44-68`, mirror
`WSC/Redeemer.lean:289-294`.  `progLogicCred` is decoded to a `Credential`
(see D-M2). -/
def paramsFields : Data → Option (CurrencySymbol × Credential)
  | Data.List (Data.B dcs :: plcD :: _) =>
      match (IsData.fromData plcD : Option Credential) with
      | some plc => some (dcs, plc)
      | none => none
  | _ => none

/-- `pparamsAtRefIdx` (:824-838): reference input at the redeemer's index,
authenticated by `phasCSH` on the protocol-params policy (:832), inline datum
required (:833-836), otherwise `perror` (:838). -/
def paramsAtRefIdx (ppCS : CurrencySymbol) (refs : List TxInInfo) (idx : Integer) :
    Option (CurrencySymbol × Credential) :=
  match atIdx idx refs with
  | none => none
  | some i =>
      match hasCSH ppCS i.txInInfoResolved.txOutValue with
      | some true =>
          (match i.txInInfoResolved.txOutDatum with
           | .OutputDatum d => paramsFields d
           | _ => none)
      | _ => none

/-! ## 6. `pcheckTransferLogicAndGetProgrammableValue` (:859-942)

The LOCKSTEP per-policy walk.  For each currency-symbol entry of the aggregated
mini-ledger input value, in ascending order, one directory-node proof index is
consumed (`phead # proofs`, :880 — running out of proofs `perror`s) and one
withdrawal index cursor is advanced (`ptail # wdrlIdxs`, :902/:923 — running out
`perror`s, in BOTH branches, even the negative one which never reads it):

* `nodeKey < currCS` → NEGATIVE proof (:891-908): the node must COVER
  (`currCS < nodeNext`, :895) and be directory-authentic (`phasCSH`, :896).  The
  entry is DROPPED from the accumulator — this is the only way a policy escapes
  the containment requirement, and is exactly what P5 is about.
* otherwise → POSITIVE proof (:909-929): the node's `transferLogicScript` must
  equal the cached one or the credential of the withdrawal entry at
  `wdrlIdxs[0]` (:911-915), the node must be keyed EXACTLY `currCS` (:916), and
  be directory-authentic (:917).  The entry is CONSED onto the accumulator
  (:925) and the cache is updated to this node's script (:926).

`pand'List` is STRICT in its elements, so a later conjunct's `perror` is reached
even when an earlier conjunct is already `false` — modelled by evaluating all
conjuncts in the `Option` monad.  On exhaustion the cons-built (DESCENDING)
accumulator is restored to canonical order by `preverseCurrencyPairs` (:935,
:315-327). -/
def transferWalk (dirCS : CurrencySymbol) (refs : List TxInInfo) (wdrl : Withdrawals) :
    List Integer → List Integer → CsPairs → CsPairs → Data → Option CsPairs
  | _, _, [], acc, _ => some acc.reverse
  | proofs, wdrlIdxs, (csD, tnsD) :: csPairs, acc, cached =>
      match csD with
      | Data.B currCS =>
          match headOpt proofs, tailOpt proofs, tailOpt wdrlIdxs with
          | some pIdx, some proofs', some wdrlIdxs' =>
              match dirNodeAt pIdx refs with
              | none => none
              | some (nodeVal, nodeKey, nodeNext, tls) =>
                  match hasCSH dirCS nodeVal with
                  | none => none
                  | some authentic =>
                      if nodeKey < currCS then
                        if decide (currCS < nodeNext) && authentic then
                          transferWalk dirCS refs wdrl proofs' wdrlIdxs' csPairs acc cached
                        else none
                      else
                        -- transfer-logic script: cached, or the withdrawal entry
                        -- named by `wdrlIdxs[0]` (:911-915).  `#||` is lazy, so
                        -- the index lookup only happens on a cache miss.
                        let tlsOk : Option Bool :=
                          if tls == cached then some true
                          else
                            match headOpt wdrlIdxs with
                            | none => none
                            | some wIdx =>
                                match atIdx wIdx wdrl with
                                | none => none
                                | some (c, _) => some (tls == IsData.toData c)
                        match tlsOk with
                        | none => none
                        | some ok =>
                            if ok && (nodeKey == currCS) && authentic then
                              transferWalk dirCS refs wdrl proofs' wdrlIdxs' csPairs
                                ((csD, tnsD) :: acc) tls
                            else none
          | _, _, _ => none
      | _ => none        -- pfromData to PCurrencySymbol on a non-B key

/-! ## 7. `pcheckMintLogicAndGetProgrammableValue` (:976-1026)

The same lockstep discipline over the tx MINT entries, with the §11.3
simplification: a `Member` proof (:993-994) counts its entry and touches NO node
— no index, no datum decode, no authentication, no transfer-logic invocation.
That is precisely the P6 claim: claiming Member can only ADD the claimant's
ledger-truth mint delta to what must remain at the base.  A `NonMember` proof
(:996-1016) must exhibit a `phasCSH`-authenticated node STRICTLY covering the
symbol (`nodeKey < currCS < nodeNext`) and its entry is dropped.

No-omission is enforced from both sides: a mint entry without a proof errors
(:1018), a leftover proof after the last mint entry errors (:1024). -/
def mintWalk (dirCS : CurrencySymbol) (refs : List TxInInfo) :
    List MintProof → CsPairs → CsPairs → Option CsPairs
  | proofs, [], acc =>
      match proofs with
      | [] => some acc.reverse
      | _ :: _ => none                      -- "extra mint proof" (:1024)
  | proofs, (csD, tnsD) :: mintCsPairs, acc =>
      match proofs with
      | [] => none                          -- "mint proof missing" (:1018)
      | p :: proofsRest =>
          match csD with
          | Data.B currCS =>
              match p with
              | .Member =>
                  mintWalk dirCS refs proofsRest mintCsPairs ((csD, tnsD) :: acc)
              | .NonMember nodeIdx =>
                  match dirNodeAt nodeIdx refs with
                  | none => none
                  | some (nodeVal, nodeKey, nodeNext, _) =>
                      match hasCSH dirCS nodeVal with
                      | none => none
                      | some authentic =>
                          if decide (nodeKey < currCS) && decide (currCS < nodeNext)
                             && authentic then
                            mintWalk dirCS refs proofsRest mintCsPairs acc
                          else none
          | _ => none

/-! ## 8. `pcurrencyPairsUnionFast` (:200-241) and `ptokenPairsUnionFast` (:149-184)

Sorted linear merges with asset-wise addition.  `pasByteStr` errors on a
non-bytestring key and `pfromData` on a non-integer quantity, hence the `none`
cases.  NOTE (load-bearing for P6/L1.6): the merge KEEPS zero and negative sums —
the filter below is what removes them, and that is why the filter has to be
proved not to lower the requirement on any positive asset. -/
def tokenPairsUnion : List (Data × Data) → List (Data × Data) →
    Option (List (Data × Data))
  | [], ys => some ys
  | x :: xs, [] => some (x :: xs)
  | (Data.B t₁, q₁) :: xs, (Data.B t₂, q₂) :: ys =>
      if t₁ == t₂ then
        match q₁, q₂ with
        | Data.I a, Data.I b =>
            (fun r => (Data.B t₁, Data.I (a + b)) :: r) <$> tokenPairsUnion xs ys
        | _, _ => none
      else if t₁ < t₂ then
        (fun r => (Data.B t₁, q₁) :: r) <$> tokenPairsUnion xs ((Data.B t₂, q₂) :: ys)
      else
        (fun r => (Data.B t₂, q₂) :: r) <$> tokenPairsUnion ((Data.B t₁, q₁) :: xs) ys
  | _, _ => none

def csPairsUnion : CsPairs → CsPairs → Option CsPairs
  | [], ys => some ys
  | x :: xs, [] => some (x :: xs)
  | (Data.B c₁, m₁) :: xs, (Data.B c₂, m₂) :: ys =>
      if c₁ == c₂ then
        match m₁, m₂ with
        | Data.Map i₁, Data.Map i₂ =>
            match tokenPairsUnion i₁ i₂, csPairsUnion xs ys with
            | some inner, some rest => some ((Data.B c₁, Data.Map inner) :: rest)
            | _, _ => none
        | _, _ => none
      else if c₁ < c₂ then
        (fun r => (Data.B c₁, m₁) :: r) <$> csPairsUnion xs ((Data.B c₂, m₂) :: ys)
      else
        (fun r => (Data.B c₂, m₂) :: r) <$> csPairsUnion ((Data.B c₁, m₁) :: xs) ys
  | _, _ => none

/-! ## 9. `pfilterPositiveCurrencyPairs` (:257-298)

Drops every quantity `≤ 0` and then every policy whose token map became empty.
The comment at :1230-1234 is normative: a non-positive entry requires nothing to
remain at the mini-ledger outputs, and the filter is what makes the `'Positive`
coercion at :1235 genuinely true. -/
def filterPosTokens : List (Data × Data) → Option (List (Data × Data))
  | [] => some []
  | (t, Data.I q) :: rest =>
      match filterPosTokens rest with
      | none => none
      | some r => some (if q ≤ 0 then r else (t, Data.I q) :: r)
  | _ => none

def filterPosCsPairs : CsPairs → Option CsPairs
  | [] => some []
  | (c, Data.Map tns) :: rest =>
      match filterPosTokens tns, filterPosCsPairs rest with
      | some [], some r => some r
      | some ts, some r => some ((c, Data.Map ts) :: r)
      | _, _ => none
  | _ => none

/-! ## 10. `poutputsContainExpectedValueAtCred` (:563-699) — THREE dispatch paths

ARCHITECTURE.md Tier 3.1 is binding here: each path must INDEPENDENTLY imply the
aggregate per-asset containment, because the source comment at :560 asserting
their equivalence is not a theorem.

* **Path A — single-asset accumulate-scan** (:604-618, dispatched at :679-695
  when the expected value is exactly one currency symbol with exactly one token
  name).  Scans outputs, accumulating that one asset's quantity at base outputs
  only, and EXITS EARLY once the required quantity is reached.
* **Path B — wholesale `Data` equality** (:648-674): the first base output whose
  ada-stripped value map is byte-identical to the expected map decides `True`.
* **Path C — builtin `valueContains`** (:619-647): accumulate every base output's
  value with `punionValue` (ada NOT stripped — irrelevant to a lower bound) and
  decide with one `pvalueContains`. -/

/-- `passetQtyInValue`'s inner token walk (:571-586): a SORTED early-exit lookup
(`tn #< tokenName ⟹ 0`), not a linear scan. -/
def assetQtyInner (tn : TokenName) : List (Data × Data) → Option Integer
  | [] => some 0
  | (Data.B t, Data.I q) :: rest =>
      if t == tn then some q else if tn < t then some 0 else assetQtyInner tn rest
  | _ => none

/-- `passetQtyInValue` (:570-603), outer walk over the currency pairs of the
WHOLE value (ada entry included; for a non-ada `cs` the sorted early exit walks
past it). -/
def assetQtyInValue (cs : CurrencySymbol) (tn : TokenName) : Value → Option Integer
  | [] => some 0
  | (Data.B c, Data.Map tns) :: rest =>
      if c == cs then assetQtyInner tn tns
      else if cs < c then some 0
      else assetQtyInValue cs tn rest
  | _ => none

/-- **Path A** — `hasAtLeastAssetInProgOutputs` (:604-618).  The `currentQty #>=
requiredQty` guard is tested BEFORE the list is destructured (:605-607) and again
as the nil result (:616). -/
def hasAtLeastAsset (base : Credential) (req : Integer) (cs : CurrencySymbol)
    (tn : TokenName) (cur : Integer) : List TxOut → Option Bool
  | [] => some (decide (req ≤ cur))
  | o :: rest =>
      if decide (req ≤ cur) then some true
      else if WSC.payCred o == base then
        match assetQtyInValue cs tn o.txOutValue with
        | none => none
        | some q => hasAtLeastAsset base req cs tn (cur + q) rest
      else hasAtLeastAsset base req cs tn cur rest

/-- `accumulateOutputsAtCred` (:628-643): builtin-`Value` accumulation of every
base output's value. -/
def accumOutputsAtCred (base : Credential) (acc : PlutusCore.Value.ValueRep) :
    List TxOut → Option PlutusCore.Value.ValueRep
  | [] => some acc
  | o :: rest =>
      if WSC.payCred o == base then
        match unVD o.txOutValue with
        | none => none
        | some v =>
            match PlutusCore.Value.unionValue acc v with
            | none => none
            | some acc' => accumOutputsAtCred base acc' rest
      else accumOutputsAtCred base acc rest

/-- **Path C** — `checkByBuiltinContains` (:644-647).  The initial accumulator is
`punValueData # (pmapData # pnil)`, i.e. the decode of the empty value map. -/
def checkByBuiltinContains (base : Credential) (outs : List TxOut) (expected : CsPairs) :
    Option Bool :=
  match unVD ([] : Value) with
  | none => none
  | some z =>
      match accumOutputsAtCred base z outs, unVD expected with
      | some outV, some expV => PlutusCore.Value.valueContains outV expV
      | _, _ => none

/-- **Path B, then C** — `checkWholesaleThenBuiltin` (:657-674).  `allOuts` is the
closed-over full output list the builtin fallback re-scans (:646); the walked
list is the remaining suffix. -/
def checkWholesaleThenBuiltin (base : Credential) (allOuts : List TxOut)
    (expected : CsPairs) : List TxOut → Option Bool
  | [] => checkByBuiltinContains base allOuts expected
  | o :: rest =>
      if WSC.payCred o == base then
        match o.txOutValue with
        | [] => none                        -- ptail # (pasMap # …) on an empty value
        | _ :: nonAda =>
            if nonAda == expected then some true
            else checkByBuiltinContains base allOuts expected
      else checkWholesaleThenBuiltin base allOuts expected rest

/-- The dispatch (:676-699).  An EMPTY expected value is `True` (:698) — nothing
has to remain. -/
def outputsContainExpectedValueAtCred (base : Credential) (outs : List TxOut)
    (expected : CsPairs) : Option Bool :=
  match expected with
  | [] => some true
  | (csD, tnsD) :: rest =>
      match tnsD with
      | Data.Map tnPairs =>
          match rest, tnPairs with
          | [], [(tnD, qD)] =>
              match csD, tnD, qD with
              | Data.B cs, Data.B tn, Data.I q => hasAtLeastAsset base q cs tn 0 outs
              | _, _, _ => none
          | _, _ => checkWholesaleThenBuiltin base outs expected outs
      | _ => none                           -- pfromData to PMap on a non-Map inner

/-! ## 11. The validator itself — `mkProgrammableLogicGlobal`, TransferAct (:1176-1274) -/

/-- The redeemer decode (:1180, :1183).  See deviation D-M1. -/
def decodeRedeemer (r : Data) : Option PLGRedeemer := IsData.fromData r

/-- The `expectedProgrammableOutputValue` computation (:1219-1251).

FIDELITY NOTE (load-bearing).  The mint walk is called INSIDE the `pif`'s false
branch (:1244), so when `txInfoMint` is EMPTY the walk never runs and the
"extra mint proof" check (:1024) is NOT performed — a `TransferAct` carrying mint
proofs for a mint-free transaction is accepted.  Harmless (the expected value is
then just the transfer value) but it is a real behaviour of the bytecode and the
model reproduces it. -/
def expectedValue (dirCS : CurrencySymbol) (refs : List TxInInfo)
    (mintProofs : List MintProof) (mint : MintValue) (transferVal : CsPairs) :
    Option CsPairs :=
  match mint with
  | [] => some transferVal
  | _ :: _ =>
      match mintWalk dirCS refs mintProofs mint [] with
      | none => none
      | some mv =>
          match csPairsUnion transferVal mv with
          | none => none
          | some u => filterPosCsPairs u

/-- The whole `TransferAct` path, in the `Option` (error-propagating) monad.
`none` = `perror`; `some false` = a validated `False`; `some true` = accept. -/
def globalModelOpt (ppCS : CurrencySymbol) (ctx : ScriptContext) : Option Bool :=
  let ti := ctx.scriptContextTxInfo
  let wdrl := ti.txInfoWdrl
  match decodeRedeemer ctx.scriptContextRedeemer with
  | some (.TransferAct proofs wdrlIdxs mintProofs paramsRefIdx) =>
      -- :1196-1199 — reference inputs + params, resolved by redeemer index.
      match paramsAtRefIdx ppCS ti.txInfoReferenceInputs paramsRefIdx with
      | none => none
      | some (dirCS, progLogicCred) =>
          -- :1201 — the cached transfer script starts as the credential of the
          -- FIRST withdrawal entry; `phead` errors on an empty withdrawal map.
          match headOpt wdrl with
          | none => none
          | some (cached0, _) =>
              -- :1202-1208
              match valueFromCred progLogicCred ti.txInfoSignatories wdrl ti.txInfoInputs with
              | none => none
              | some total =>
                  -- :1209-1218
                  match transferWalk dirCS ti.txInfoReferenceInputs wdrl proofs wdrlIdxs
                          total [] (IsData.toData cached0) with
                  | none => none
                  | some total' =>
                      -- :1219-1251
                      match expectedValue dirCS ti.txInfoReferenceInputs mintProofs
                              ti.txInfoMint total' with
                      | none => none
                      | some expected =>
                          -- :1253-1260 — `pisRewardingScript` ∧ containment.
                          match ctx.scriptContextScriptInfo with
                          | .RewardingScript _ =>
                              outputsContainExpectedValueAtCred progLogicCred
                                ti.txInfoOutputs expected
                          | _ => some false
  | some (.SeizeAct ..) => some false       -- :1273-1274, `ptraceInfoError`
  | none => some false                      -- D-M1

/-- **THE MODEL.**  `true` iff the transcribed `TransferAct` path of
`mkProgrammableLogicGlobal` accepts: both `perror` and a validated `False` are
rejections (`pvalidateConditions` errors on a false condition). -/
def globalModel (ppCS : CurrencySymbol) (ctx : ScriptContext) : Bool :=
  match globalModelOpt ppCS ctx with
  | some b => b
  | none => false

end WSC.Model
