/-
WSC/Props/P3_Base.lean — P3, the KEYSTONE property (arch §3-P3, unit U1),
**RE-BASED ON wsc-poc `main` @ 2306678 (PR #112) BY TASK N3**.

Plain English, unchanged in meaning: you cannot spend a mini-ledger UTxO unless
the global (transfer) or seize validator runs in the same transaction — which
forces the containment checks (P1 or P2) on every exit from the mini-ledger.

╔══════════════════════════════════════════════════════════════════════════╗
║ READ THIS FIRST: WHAT THIS MODULE IS, AFTER #112                         ║
╠══════════════════════════════════════════════════════════════════════════╣
║ **P3 itself is NO LONGER PROVED HERE.** It has moved to                   ║
║ `WSC/Props/Shaped/P3ShapedR.lean` (SHAPES B1RG / B1RS) and                ║
║ `WSC/Props/P3_BaseRun.lean` (the same, on the ledger-side run term).      ║
║                                                                          ║
║ What survives in THIS module is the UNSHAPED substrate that P3 used to    ║
║ live on: the prep at budget 600, two concrete accepting bootstrap         ║
║ contexts with K pinned two-sided, and — §MEASUREMENT below — the record   ║
║ of exactly why the unshaped route no longer closes. The measurement is    ║
║ the deliverable here, not a theorem.                                      ║
╚══════════════════════════════════════════════════════════════════════════╝

════════════════════════════════════════════════════════════════════════════
§MEASUREMENT — the unshaped route, and why it is gone
════════════════════════════════════════════════════════════════════════════
PRE-#112 the base validator ignored its redeemer and SCANNED `txInfoWdrl` with
a `pfix` loop (`ProgrammableLogicBase.hs:722-730` at `f918ec6`). `blaster`
closed the unshaped P3 goal — over a FULLY SYMBOLIC `ScriptContext` — in
seconds. That made P3 the ONE property in this campaign needing no coverage
argument at all (`WSC/Coverage.lean` §7).

POST-#112 the validator reads a constructor tag and an `Integer` INDEX out of
its redeemer and does `pdropList <symbolic index>` into the withdrawal map
(`:712-733`). MEASURED on this flat, this inputs function (`WSC.baseInputs`),
this budget (600) and this machine, each goal in its OWN module so the Z3 cap
is per goal:

| goal, UNSHAPED at `appliedBase.prop`, budget 600 | Z3 cap | verdict | wall |
|---|---|---|---|
| P3 (`validSpendingContext → accept → cred ∈ wdrl ∨ cred ∈ wdrl`) | 600 s | **`⚠️ Undetermined`** | 602 s |
| negative control (`¬post → reject`) | 600 s | **`⚠️ Undetermined`** | 602 s |
| **vacuity probe** (`∀ ctx, ¬ accept`) | 600 s | **`⚠️ Undetermined`** | 602 s |
| P3, UNCAPPED — the form this module shipped pre-#112 | ∞ | no verdict, killed | > 60 min |

ESCALATIONS RUN, and none of them recovers the unshaped route:

| escalation | Z3 cap | verdict |
|---|---|---|
| P3 + vacuity probe at a bigger cap | 2400 s | **`⚠️ Undetermined`** (2404 s / 2403 s wall) |
| P3 + vacuity probe at the MINIMAL shape — ONLY the redeemer's `Data` skeleton frozen (`Constr tag [I red]`, `red` symbolic), every other context field fully symbolic | 900 s | **`⚠️ Undetermined`** |
| P3 + vacuity probe at a SMALLER prep budget (250; K = 194, so 250 still admits the accepting witnesses) | 900 s | **`⚠️ Undetermined`** |

All of them, verbatim and re-runnable, are in `WSC/Props/P3Unshaped.lean.disabled`.

**WHAT THAT LOCALIZES.** Freezing the redeemer alone changes nothing. Freezing
the redeemer AND the withdrawal map — SHAPES B1RG / B1RS, two entries — closes
every goal in under 2 seconds. Lowering the budget changes nothing. So the
blocker is specifically the symbolic withdrawal LIST under
`pdropList <symbolic index>`; it is not the redeemer, and it is not the budget.

THE SHARP POINT: even the VACUITY PROBE is Undetermined, although accepting
contexts demonstrably exist — `P3Witness.exec_accepts` / `exec_accepts_S` below halt
accepting at K = 194 by `native_decide` on the real CEK machine with no solver
involved. So the property did not become false and the budget did not become
vacuous; a symbolic index into a symbolic list is simply a search Z3 does not
finish. The pre-#112 scan was bounded by the CEK budget and unrolled; the
post-#112 `dropList` is not.

THE HONEST CONSEQUENCE, stated once and not softened: **P3 has lost its
special status.** It is now a shaped property like P1, P2, P4, P5 and P6, with
the same two-dimensional scope (CEK budget × shape) and the same obligation to
carry a realizability argument. `WSC/Coverage.lean`'s
`p3_lives_over_a_covering_class` and the sentence it exists to support are
retired, not re-pointed.

════════════════════════════════════════════════════════════════════════════
SCOPE (ADDENDUM E1, binding)
════════════════════════════════════════════════════════════════════════════
`#prep_uplc … 600` bakes a concrete CEK step budget into `appliedBase.prop`;
budget exhaustion evaluates to `Error`. Everything below is therefore about
invocations whose validator run halts within 600 CEK steps. The budget is
NON-VACUOUS on the post-#112 bytecode: the two bootstrap witnesses in §WITNESS
halt accepting at 194 steps, pinned two-sided.

PRECONDITION AUDIT (arch §4.1, may-assume / must-not-assume) — for the record,
since the shaped successors inherit it: the only ledger hypothesis anywhere in
the P3 family is CLAB's `validSpendingContext` (spending purpose, sorted /
canonical fields, balanced tx). It constrains the withdrawal map ONLY to be
credential-sorted (`validWithdrawals`); it assumes NOTHING about WHICH
credentials appear there, so the postcondition is not smuggled in.
**The redeemer's CONTENT is never assumed** — after #112 that is the load-bearing
half of the audit, because the redeemer is now the attacker's channel. An
attacker naming a wrong index, an out-of-range index, a negative index or the
wrong arm must remain expressible, and it does: the shaped successors quantify
over the index leaf and cover both constructor tags.

Source fidelity (validator side, commentary only; line numbers at 2306678):
* `mkProgrammableLogicBase :: PAsData PCredential :--> PAsData PCredential
  :--> PScriptContext :--> PUnit` — ProgrammableLogicBase.hs:711
  (parameter evidence in `WSC/Prep/Base.lean`).
* The accept path is now: `ctxFields ← unConstrData ctx`; `witness ←
  unConstrData (head (tail ctxFields))` (= the redeemer); `wdrls = pasMap (head
  (dropList 6 (snd (unConstrData (head ctxFields)))))` (= `TxInfo` field 6);
  `claimed = if fst witness == 0 then globalCred else seizeCred`;
  `witnessed = fst (head (dropList (asInt (head (snd witness))) wdrls))`;
  accept iff `witnessed == claimed` — `:712-733`. Note `claimed` is selected by
  a `pif`, NOT an exhaustive match, so **any tag ≠ 0 takes the seize arm**.
-/
import WSC.Prep.Base
import WSC.Redeemer
import Blaster

namespace WSC

open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptInfo ScriptPurpose
                          TxInInfo TxOutRef TxInfo Withdrawals validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false

/-! ════════════════════════════════════════════════════════════════════════
## §WITNESS — the unshaped bootstrap contexts, re-cut for the new redeemer
════════════════════════════════════════════════════════════════════════

Two hand-constructed, fully concrete accepting contexts — one per arm of the
new `BaseSpendRedeemer`. Each has one input spent from a script address, an
ada-only canonical value, and a ONE-entry withdrawal map holding exactly the
credential its own arm claims (the withdraw-zero pattern). CLEARLY LABELLED
BOOTSTRAP: they certify non-vacuity and the accept polarity end to end
(concrete `Data`, real CEK) but are NOT off-chain-produced golden vectors —
for that see `WSC/Goldens/Witnesses.lean`.

**WHAT #112 BROKE HERE, and it is worth naming.** The pre-#112 bootstrap
context carried `scriptContextRedeemer := Data.I 0`, because the old validator
never looked at it. Against the new bytecode that context is REJECTING, not
accepting: `pasConstr` on a `Data.I` errors. A pre-#112 context literal is
therefore not merely "still fine"; it silently flips polarity. Every context
literal in this library had to be re-checked for that, and the two here were
re-cut to `Data.Constr 0 [Data.I 0]` / `Data.Constr 1 [Data.I 1]`.

The seize arm (`ctxS`) is new. It exists because **no golden vector exercises
`SpendViaSeize`** — task N2 §5 records that gap explicitly, tag 1 being pinned
only negatively there — so without `ctxS` the library would have no positive
evidence at all about that arm. -/

namespace P3Witness

open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

/-- The global (transfer) rewarding credential parameter. -/
def globalCred : Credential := .ScriptCredential (ByteString.mk "GLOBAL")
/-- The standalone seize rewarding credential parameter. -/
def seizeCred  : Credential := .ScriptCredential (ByteString.mk "SEIZE")

def outRef : TxOutRef := ⟨ByteString.mk "", 0⟩

/-- Ada-only canonical value (lovelace-first, positive): 100 lovelace. -/
def value : CardanoLedgerApi.V1.Value.Value :=
  [(Data.B (ByteString.mk ""), Data.Map [(Data.B (ByteString.mk ""), Data.I 100)])]

/-- The spent mini-ledger UTxO (script payment credential, no datum). -/
def resolved : TxOut :=
  { txOutAddress := ⟨.ScriptCredential (ByteString.mk "BASE"), none⟩
  , txOutValue := value
  , txOutDatum := .NoOutputDatum
  , txOutReferenceScript := none }

/-- Validity interval [0, 1], both bounds finite and closed. -/
def range : Data :=
  Data.Constr 0 [ Data.Constr 0 [Data.Constr 1 [Data.I 0], Data.Constr 1 []]
                , Data.Constr 0 [Data.Constr 1 [Data.I 1], Data.Constr 1 []] ]

/-- `SpendViaGlobal 0` on the wire — `Constr 0 [I 0]`. Pinned against the
mirror by `redeemers_match_mirror`. -/
def rdmrG : Data := Data.Constr 0 [Data.I 0]
/-- `SpendViaSeize 0` on the wire — `Constr 1 [I 0]`. -/
def rdmrS : Data := Data.Constr 1 [Data.I 0]

/-- Concrete accepting spending context, parameterised by its redeemer and its
withdrawal map: spends `resolved`, burns the whole 100 lovelace as fee
(balanced: 100 + 0 = 0 + 100). -/
def mkCtx (rdmr : Data) (wdrl : Withdrawals) : ScriptContext :=
  { scriptContextTxInfo :=
    { txInfoInputs := [⟨outRef, resolved⟩]
    , txInfoReferenceInputs := []
    , txInfoOutputs := []
    , txInfoFee := 100
    , txInfoMint := []
    , txInfoTxCerts := []
    , txInfoWdrl := wdrl
    , txInfoValidRange := range
    , txInfoSignatories := []
    , txInfoRedeemers := [(.Spending outRef, rdmr)]
    , txInfoData := []
    , txInfoId := ByteString.mk ""
    , txInfoVotes := []
    , txInfoProposalProcedures := []
    , txInfoCurrentTreasuryAmount := Data.I 1
    , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := rdmr
  , scriptContextScriptInfo := .SpendingScript outRef none }

/-- BOOTSTRAP witness, GLOBAL arm: withdrawal map `[(globalCred, 0)]`, redeemer
`SpendViaGlobal 0` — index 0 names the entry whose credential IS `globalCred`. -/
def ctx : ScriptContext := mkCtx rdmrG [(globalCred, 0)]

/-- BOOTSTRAP witness, SEIZE arm: withdrawal map `[(seizeCred, 0)]`, redeemer
`SpendViaSeize 0`. -/
def ctxS : ScriptContext := mkCtx rdmrS [(seizeCred, 0)]

/-- The two bootstrap redeemers are exactly what `WSC/Redeemer.lean`'s mirror
of `BaseSpendRedeemer` encodes — so the witnesses are not carrying a private
guess at the new wire form. -/
theorem redeemers_match_mirror :
    rdmrG = CardanoLedgerApi.IsData.Class.IsData.toData
              (BaseSpendRedeemer.SpendViaGlobal 0)
  ∧ rdmrS = CardanoLedgerApi.IsData.Class.IsData.toData
              (BaseSpendRedeemer.SpendViaSeize 0) :=
  ⟨rfl, rfl⟩

/-- The metered run of the REAL imported bytecode, global arm. -/
def runG (K : Nat) := cekExecuteProgram programmableLogicBase.script
  (baseInputs globalCred seizeCred ctx) K
/-- The metered run of the REAL imported bytecode, seize arm. -/
def runS (K : Nat) := cekExecuteProgram programmableLogicBase.script
  (baseInputs globalCred seizeCred ctxS) K

/-- Bool reflection of `isSuccessful` (a `Prop`), for `native_decide`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The GLOBAL-arm witness satisfies the ledger-normalization precondition.
NAME KEPT from the pre-#112 module: `WSC/Composition.lean:1185` names it. -/
theorem ctx_valid : validSpendingContext ctx = true := by native_decide

/-- The SEIZE-arm witness satisfies it too. -/
theorem ctxS_valid : validSpendingContext ctxS = true := by native_decide

/-- The global-arm witness satisfies P3's postcondition through the FIRST
disjunct. -/
theorem ctx_post :
    credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl = true := by
  native_decide

/-- …and the seize-arm witness through the SECOND, so both disjuncts of P3's
conclusion are reachable and the disjunction is not degenerate. -/
theorem ctxS_post :
    credentialInWithdrawals seizeCred ctxS.scriptContextTxInfo.txInfoWdrl = true := by
  native_decide

/-- **K = 194, PINNED TWO-SIDED, both arms.** Halts at 194, budget-errors at
193, stable at 10× (1940). Pre-#112 the same bootstrap cost **208**; the
regenerated golden `base-spend-transfer-tx` also moved 208 → 194
(`WSC/goldens/K-MEASUREMENTS.md` §3, task N2), so the two agree to the step. -/
theorem K_two_sided :
    isHaltB (runG 194) = true ∧ isHaltB (runG 193) = false ∧ isHaltB (runG 1940) = true
  ∧ isHaltB (runS 194) = true ∧ isHaltB (runS 193) = false ∧ isHaltB (runS 1940) = true := by
  native_decide

/-- BOOTSTRAP WITNESS (executable CEK), global arm: the real compiled post-#112
bytecode ACCEPTS the concrete context at budget 600. NAME KEPT from the pre-#112
module: `WSC/Composition.lean:1186` names it. -/
theorem exec_accepts : isSuccessful (appliedBase.exec globalCred seizeCred ctx) :=
  isHaltB_sound _ (by native_decide)

/-- BOOTSTRAP WITNESS (executable CEK), seize arm. -/
theorem exec_accepts_S : isSuccessful (appliedBase.exec globalCred seizeCred ctxS) :=
  isHaltB_sound _ (by native_decide)

/-- **THE POLARITY FLIP #112 INTRODUCED, MADE INTO A THEOREM.** The PRE-#112
bootstrap context — byte-identical to `ctx` except that its redeemer is the old
PlutusTx `()`-era `Data.I 0` — is REJECTED by the post-#112 bytecode. This is
the negative control for the re-cut above: it shows the two witnesses accept
*because of* their new redeemers and not by accident, and it is the reason
every pre-#112 context literal in the library had to be re-checked rather than
assumed still good. -/
theorem old_redeemer_now_rejects :
    isHaltB (cekExecuteProgram programmableLogicBase.script
      (baseInputs globalCred seizeCred (mkCtx (Data.I 0) [(globalCred, 0)])) 600) = false := by
  native_decide

/-- …and it is not merely a budget artifact: it still fails at 10× the budget. -/
theorem old_redeemer_now_rejects_at_10x :
    isHaltB (cekExecuteProgram programmableLogicBase.script
      (baseInputs globalCred seizeCred (mkCtx (Data.I 0) [(globalCred, 0)])) 6000) = false := by
  native_decide

/-- **THE WRONG-INDEX ATTACK IS REJECTED.** Same context, same arm, but the
redeemer names index 1 of a ONE-entry withdrawal map. `dropList 1` leaves the
empty list and `phead` errors — so a dishonest witness index invalidates only
the attacker's own transaction, exactly as the in-source rationale claims
(`ProgrammableLogicBase.hs:685-699`). Not a proof for all shapes — that is
`P3ShapedR`'s job — but a concrete instance of it. -/
theorem out_of_range_index_rejects :
    isHaltB (cekExecuteProgram programmableLogicBase.script
      (baseInputs globalCred seizeCred
        (mkCtx (Data.Constr 0 [Data.I 1]) [(globalCred, 0)])) 6000) = false := by
  native_decide

/-- **THE WRONG-ARM ATTACK IS REJECTED.** Same one-entry map holding
`globalCred`, but the redeemer claims `SpendViaSeize 0`, so `claimed` is
`seizeCred` and the equality fails. -/
theorem wrong_arm_rejects :
    isHaltB (cekExecuteProgram programmableLogicBase.script
      (baseInputs globalCred seizeCred
        (mkCtx (Data.Constr 1 [Data.I 0]) [(globalCred, 0)])) 6000) = false := by
  native_decide

/-- **THE THREE ATTACK WITNESSES ARE LEDGER-LEGAL — checked, not assumed**
(task R3, the counterexample-witness sweep).

A rejection demonstration is only evidence about an ATTACK if the context it
rejects is one a node would actually build; a rejection of a transaction the
ledger would refuse anyway shows nothing about the validator.  The three
theorems above vary `ctx` in its REDEEMER only, and no `[LEDGER-RULE]` predicate
constrains a redeemer's payload, so all three inherit `ctx_valid`'s legality —
but "so it should" is exactly the reasoning that produced the P2b canonicity
error (`WSC/Props/P2_Seize.lean` §4b, `WSC/AUDIT.md` §5.2, §5.6), so it is
computed here instead. -/
theorem attack_witnesses_are_ledger_legal :
    validSpendingContext (mkCtx (Data.I 0) [(globalCred, 0)]) = true
  ∧ validSpendingContext (mkCtx (Data.Constr 0 [Data.I 1]) [(globalCred, 0)]) = true
  ∧ validSpendingContext (mkCtx (Data.Constr 1 [Data.I 0]) [(globalCred, 0)]) = true := by
  native_decide

end P3Witness

/-! ## AXIOM AUDIT

Everything in §WITNESS is `native_decide` or `rfl` — no `blaster`, hence no
`sorryAx` on any of it. That is a strictly better trust status than the
pre-#112 module, whose `prop_accepts` was solver-closed. -/

#print axioms WSC.P3Witness.K_two_sided
#print axioms WSC.P3Witness.exec_accepts
#print axioms WSC.P3Witness.exec_accepts_S
#print axioms WSC.P3Witness.old_redeemer_now_rejects
#print axioms WSC.P3Witness.out_of_range_index_rejects
#print axioms WSC.P3Witness.wrong_arm_rejects

end WSC
