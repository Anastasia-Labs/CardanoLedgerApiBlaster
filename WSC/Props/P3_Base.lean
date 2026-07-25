/-
WSC/Props/P3_Base.lean — P3, the KEYSTONE property (arch §3-P3, unit U1).

Plain English: you cannot spend a mini-ledger UTxO unless the global
(transfer) or seize validator runs in the same transaction — which forces the
containment checks (P1 or P2) on every exit from the mini-ledger.

Proved against the ACTUAL compiled production bytecode
(`WSC/flats/programmableLogicBase.flat`, prepped in WSC/Prep/Base.lean at CEK
step budget 600).

SCOPE (ADDENDUM E1, binding): `#prep_uplc … 600` bakes a concrete CEK step
budget into `appliedBase.prop`; budget exhaustion evaluates to `Error`. Every
theorem below is therefore BOUNDED-TRANSACTION model checking: it constrains
exactly those invocations whose validator run halts within 600 CEK steps
(bridged to real node acceptance by `LR_BUDGET_base` in WSC/Honest.lean). The
budget is NON-VACUOUS: the probe at the bottom of this file exhibits accepting
contexts within 600 steps (and the bootstrap witness pins one concretely).

PRECONDITION AUDIT (arch §4.1, may-assume/must-not-assume): the only
hypothesis is CLAB's `validSpendingContext` = ledger normalization (spending
purpose, sorted/canonical fields, balanced tx). In particular it constrains
the withdrawal map ONLY to be credential-sorted (`validWithdrawals`) — it
assumes NOTHING about WHICH credentials appear there, so the postcondition is
not smuggled in. The redeemer is wholly unconstrained. `globalCred`/`seizeCred`
are universally quantified parameters, never concrete hashes.

Source fidelity (validator side, commentary only):
* `mkProgrammableLogicBase :: PAsData PCredential :--> PAsData PCredential
  :--> PScriptContext :--> PUnit` —
  src/programmable-tokens-onchain/lib/SmartTokens/Contracts/ProgrammableLogicBase.hs:717-729
  (parameter evidence in WSC/Prep/Base.lean).
* The accept path is a single fixpoint scan of `txInfoWdrl` comparing each
  entry's credential against the two parameters — ProgrammableLogicBase.hs:722-730
  (`(c #== globalCred) #|| (c #== seizeCred) #|| (self # rest)`).
-/
import WSC.Prep.Base
import Blaster

namespace WSC

open CardanoLedgerApi.V2 (TxOut)
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptInfo ScriptPurpose
                          TxInInfo TxOutRef TxInfo validSpendingContext
                          credentialInWithdrawals)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): the `sorry`
-- warnings on blaster-proved theorems are expected and whitelisted.
set_option warn.sorry false

/-! ## The keystone theorem -/

/-- **P3 (keystone).** *You cannot spend a mini-ledger UTxO unless the global
(transfer) or seize validator runs in the same transaction — which forces the
containment checks (P1 or P2) on every exit from the mini-ledger.*

Formally: any accepting run of the production `programmableLogicBase` spending
validator (within the 600-step bound, ADDENDUM E1) on a ledger-normalized
context implies that the `globalCred` or the `seizeCred` parameter appears in
the transaction's withdrawal map. Combined with LR6/LR-CTX ("a script-cred
withdrawal entry means that stake validator ran and succeeded"), every base
spend forces a run of the global (⟹ P1) or seize (⟹ P2) validator over the
same transaction. -/
theorem P3_base_requires_global_or_seize :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    isSuccessful (appliedBase.prop globalCred seizeCred ctx) →
      credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl := by blaster

/-! ## Polarity controls (ADDENDUM E9)

The controls below pin the accept/reject axis from both sides. NOTE (E9,
binding): they certify behavior ONLY within the 600-step bound — the negative
control is satisfied by budget-`Error` as well, so it cannot detect the bound;
the vacuity probe + concrete witness below are what rule out vacuity. -/

/-- Negative control: a context violating the postcondition (NEITHER
credential in the withdrawal map) is rejected by the bytecode. -/
theorem P3_base_negative_control :
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    ¬(credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl) →
    isUnsuccessful (appliedBase.prop globalCred seizeCred ctx) := by blaster

/-- Tightness stanza: the NEGATION of P3's postcondition under an accepting
run must be falsifiable (mirrors Tests/Scripts/MintingPolicy/Properties.lean:47-53).
Expected result: Falsified. -/
def P3_base_tightness : Prop :=
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    isSuccessful (appliedBase.prop globalCred seizeCred ctx) →
    ¬(credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl
      ∨ credentialInWithdrawals seizeCred ctx.scriptContextTxInfo.txInfoWdrl)

#blaster (gen-cex: 0) (solve-result: 1) [P3_base_tightness]

/-- MANDATORY vacuity probe (SPIKE-FINDINGS / E9): "no accepting context
within budget 600" must be FALSIFIED, i.e. accepting contexts exist within
the prep budget, so the success-implies theorems above are not vacuous.
Expected result: Falsified. (Run with `(gen-cex: 1)` to print a concrete
accepting context; suppressed here to keep build logs readable.) -/
def P3_base_vacuity_probe : Prop :=
  ∀ (globalCred seizeCred : Credential) (ctx : ScriptContext),
    validSpendingContext ctx →
    ¬ isSuccessful (appliedBase.prop globalCred seizeCred ctx)

#blaster (gen-cex: 0) (solve-result: 1) [P3_base_vacuity_probe]

/-! ## BOOTSTRAP positive witness — SUPERSEDED (E9 boundary witness)

A hand-constructed, fully concrete accepting context: one input spent from a
script address, an ada-only canonical value, and a withdrawal map containing
exactly the global credential (amount 0 — the withdraw-zero pattern). CLEARLY
LABELED BOOTSTRAP: it certifies non-vacuity and the accept polarity end-to-end
(concrete `Data`, real CEK) but is NOT an off-chain-produced golden vector.

STATUS (task Y4 / ADDENDUM E9): **superseded, retained deliberately.** The
real-suite replacement is `WSC/Goldens/Witnesses.lean`, which proves the same two
facts — `exec_accepts` and `prop_accepts` — for the off-chain-produced golden
`programmableLogicBase.base-spend-transfer-tx` (K = 208 CEK steps, inside this
module's 600-step budget), decoded from its `serialiseData` CBOR with a
byte-identical round-trip receipt. **Cite that module, not this one, as P3's
non-vacuity witness.** This bootstrap is kept because it is the minimal
accepting context (useful when debugging the accept path) and because, unlike
the golden, it also satisfies `validSpendingContext` — the goldens are
benchmark-harness-built and set `txInfoFee = 0` (see `WSC/LR-CTX-AUDIT.md`), so
only the bootstrap can be substituted into `P3_base_requires_global_or_seize`
itself. -/

namespace P3Witness

def globalCred : Credential := .ScriptCredential (ByteString.mk "GLOBAL")
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

/-- Concrete accepting spending context: spends `resolved`, burns the whole
100 lovelace as fee (balanced: 100 + 0 = 0 + 100), withdrawal map
`[(globalCred, 0)]`. -/
def ctx : ScriptContext :=
  { scriptContextTxInfo :=
    { txInfoInputs := [⟨outRef, resolved⟩]
    , txInfoReferenceInputs := []
    , txInfoOutputs := []
    , txInfoFee := 100
    , txInfoMint := []
    , txInfoTxCerts := []
    , txInfoWdrl := [(globalCred, 0)]
    , txInfoValidRange := range
    , txInfoSignatories := []
    , txInfoRedeemers := [(.Spending outRef, Data.I 0)]
    , txInfoData := []
    , txInfoId := ByteString.mk ""
    , txInfoVotes := []
    , txInfoProposalProcedures := []
    , txInfoCurrentTreasuryAmount := Data.I 1
    , txInfoTreasuryDonation := Data.I 1 }
  , scriptContextRedeemer := Data.I 0
  , scriptContextScriptInfo := .SpendingScript outRef none }

/-- Bool reflection of `isSuccessful` (a `Prop`), for `native_decide`. -/
def isHaltB : PlutusCore.UPLC.CekMachine.State → Bool
  | .Halt _ => true
  | _ => false

theorem isHaltB_sound (s : PlutusCore.UPLC.CekMachine.State) :
    isHaltB s = true → isSuccessful s := by
  intro h; cases s <;> simp [isHaltB] at h <;> trivial

/-- The witness satisfies the ledger-normalization precondition. -/
theorem ctx_valid : validSpendingContext ctx = true := by native_decide

/-- The witness satisfies P3's postcondition through its FIRST disjunct. -/
theorem ctx_post :
    credentialInWithdrawals globalCred ctx.scriptContextTxInfo.txInfoWdrl = true := by
  native_decide

/-- BOOTSTRAP WITNESS (executable CEK): the real compiled bytecode ACCEPTS the
concrete context, via the compiled `appliedBase.exec` (`cekExecuteProgram` at
budget 600) and `native_decide`. -/
theorem exec_accepts : isSuccessful (appliedBase.exec globalCred seizeCred ctx) :=
  isHaltB_sound _ (by native_decide)

/-- BOOTSTRAP WITNESS (prepped form): the SAME concrete context is accepted by
the optimized `appliedBase.prop` the P-theorems quantify over (the
`Classical`-bearing optimized term is not kernel-reducible, so this is closed
by blaster on the fully concrete goal rather than `decide`). -/
theorem prop_accepts : isSuccessful (appliedBase.prop globalCred seizeCred ctx) := by
  blaster

end P3Witness

end WSC
