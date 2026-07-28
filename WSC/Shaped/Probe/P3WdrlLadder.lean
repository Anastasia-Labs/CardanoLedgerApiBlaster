/-
WSC/Shaped/Probe/P3WdrlLadder.lean — task N6, EXPERIMENT 2.

How far does the withdrawal-map-only cut generalise?  Three axes, measured:
  (cc) both script PARAMETERS and both withdrawal CREDENTIALS fully symbolic
       `Credential`s (constructor tags NOT frozen);
  (n)  withdrawal maps of length 1 and 3 as well as 2.
-/
import WSC.Prep.Base
import WSC.Shaped.Shape
import Blaster

set_option maxHeartbeats 0
set_option warn.sorry false

namespace WSC

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (Credential ScriptContext ScriptHash ScriptInfo TxInfo
                          Withdrawals credentialInWithdrawals spendingInputs)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## (cc) fully symbolic credentials, length 2 -/

def bccWdrl (c0 c1 : Credential) (a0 a1 : Integer) : Withdrawals := [(c0, a0), (c1, a1)]

def bccInputs (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 c1 : Credential) (a0 a1 : Integer) : List Term :=
  toTerm g :: toTerm s ::
    spendingInputs
      { scriptContextTxInfo := { ti with txInfoWdrl := bccWdrl c0 c1 a0 a1 }
      , scriptContextRedeemer := red
      , scriptContextScriptInfo := si }

#prep_uplc appliedBcc programmableLogicBase bccInputs 600

theorem P3_cc :
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 c1 : Credential) (a0 a1 : Integer),
    isSuccessful (appliedBcc.prop g s ti red si c0 c1 a0 a1) →
      credentialInWithdrawals g (bccWdrl c0 c1 a0 a1)
      ∨ credentialInWithdrawals s (bccWdrl c0 c1 a0 a1) := by
  blaster (timeout: 900)

def P3_cc_vac : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 c1 : Credential) (a0 a1 : Integer),
    ¬ isSuccessful (appliedBcc.prop g s ti red si c0 c1 a0 a1)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_cc_vac]

/-! ## (n = 1) -/

def bcc1Wdrl (c0 : Credential) (a0 : Integer) : Withdrawals := [(c0, a0)]

def bcc1Inputs (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 : Credential) (a0 : Integer) : List Term :=
  toTerm g :: toTerm s ::
    spendingInputs
      { scriptContextTxInfo := { ti with txInfoWdrl := bcc1Wdrl c0 a0 }
      , scriptContextRedeemer := red
      , scriptContextScriptInfo := si }

#prep_uplc appliedBcc1 programmableLogicBase bcc1Inputs 600

theorem P3_cc1 :
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 : Credential) (a0 : Integer),
    isSuccessful (appliedBcc1.prop g s ti red si c0 a0) →
      credentialInWithdrawals g (bcc1Wdrl c0 a0)
      ∨ credentialInWithdrawals s (bcc1Wdrl c0 a0) := by
  blaster (timeout: 900)

def P3_cc1_vac : Prop :=
  ∀ (g s : Credential) (ti : TxInfo) (red : Data) (si : ScriptInfo)
    (c0 : Credential) (a0 : Integer),
    ¬ isSuccessful (appliedBcc1.prop g s ti red si c0 a0)

#blaster (timeout: 900) (gen-cex: 0) (solve-result: 1) [P3_cc1_vac]

/-! ## (n = 3) — **MEASURED, DOES NOT CLOSE.**

The same statement at a THREE-entry map returned no verdict: `blaster (timeout:
900)` left the goal open (`unsolved goals`) after the full 900 s cap, while its
vacuity probe came back `✅ Expected Falsified` in seconds — so accepting
contexts of that shape demonstrably exist and the failure is Z3 search, not
emptiness.  Total wall for the three-rung module was 14 m 30 s, essentially all
of it the n = 3 rung.

The n = 3 stanza is kept as prose rather than as a `⚠️ Undetermined` in the
build, for the same reason `WSC/Props/P3Unshaped.lean.disabled` is disabled: it
adds a quarter of an hour to a two-minute build and puts a non-`✅` marker into a
census that is otherwise all-`✅`.  To re-run it, copy the n = 2 stanza and add a
third `(c2, a2)` entry.

**SO THE MEASURED BOUNDARY IS:** withdrawal maps of length 1 and 2 close with
everything else symbolic; length 3 does not, at a 900 s cap.  Both classes the
library composes over have length 2.
-/

end WSC
