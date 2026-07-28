-- ✅ RE-PROVED against wsc-poc main @ 2306678 (PR #112) by task N4. Shapes re-cut with the 5-field TransferAct; K re-measured two-sided. See WSC/IMPACT-PR112.md APPENDIX N4.
/-
WSC/Props/Shaped/P6Shaped.lean — **P6 (the `Member` claim is self-penalizing),
PROVED at UPLC level against the real compiled transfer bytecode, over SHAPE G6**
(task V3 rung 4).

════════════════════════════════════════════════════════════════════════════
⚠ SHAPE-CLASS STATUS (task C1) — READ BEFORE COMPOSING ANYTHING FROM THIS FILE
════════════════════════════════════════════════════════════════════════════
Every theorem below is TRUE and unchanged. But SHAPE G6's class is **EMPTY as a
class of ledger transactions** under Conway UTXOW's `MissingRedeemers` rule —
two script withdrawals, one redeemer entry (`WSC.g6_class_is_empty_under_coverage`,
WSC/Props/Shaped/GlobalRealizability.lean). **Use
`WSC/Props/Shaped/P6ShapedR.lean` instead**: the same statement
(`P6R_shaped_member_adds_to_requirement`), same budget 3300, same witness
K = 2837, over the re-cut SHAPE G6R whose class is proved NON-EMPTY
(`WSC.g6R_realizable`).

════════════════════════════════════════════════════════════════════════════
P6 IN PLAIN ENGLISH
════════════════════════════════════════════════════════════════════════════
*If a policy is classified `Member` during a transfer — i.e. claimed to be a
registered programmable token — its minted amount is ADDED to the amount that must
remain inside the mini-ledger, never subtracted. Claiming `Member` can only make
the containment obligation harder, so the claim is self-penalizing and cannot be
abused.*

Two halves, and this module supplies the second:

* **"never subtracted"** was proved on the SOURCE MODEL in
  `WSC/Props/P6_Member.lean`: `mintWalk_result_sublist` (the programmable mint
  value the walk returns is an order-preserving SUBLIST of `txInfoMint`, with every
  retained entry byte-identical, so the walk has no quantity arithmetic at all and
  cannot negate, halve or otherwise flip a sign) and `mintWalk_member_retains` (a
  `Member` proof retains its entry while touching no directory node — no index, no
  datum decode, no authentication).
* **"ADDED to the amount that must remain inside the mini-ledger"** is what this
  module proves, and it proves it AGAINST THE REAL BYTECODE, in ground-truth
  vocabulary, at budget 3300 over SHAPE G6.

Together with the executable contrast in the `§ SELF-PENALIZATION, MEASURED`
section at the bottom — *the same escaping transaction is REJECTED under `Member`
and ACCEPTED under `NonMember`* — the plain-English sentence above is now backed
end to end at the bytecode level for this shape class.

════════════════════════════════════════════════════════════════════════════
GROUND-TRUTH FORM (ARCHITECTURE Tier 0.1 / D3, hard gate)
════════════════════════════════════════════════════════════════════════════
The postcondition is ARCHITECTURE §3-P6's inequality, in the SIGNED form that the
composition layer actually consumes:

    outAtBaseQty base cs tn (outputs)  ≥  inAtBaseQty base cs tn (inputs)
                                          + mintOf cs tn (txInfoMint)

Everything in it is ledger data: output/input addresses' payment credentials,
output/input `Value`s, and `txInfoMint`. Nothing refers to the validator's
`expectedProgrammableOutputValue`, its mint-walk accumulator, or any other
computed quantity.

**WHY THE SIGNED FORM, NOT `≥ mintPos`.** ARCHITECTURE §3-P6 writes
`outAtBase ≥ mintPos`. Task Z5's Stage-5 correction (a) established that the
`mintPos` form is **REFUTED for burns** — with `inSum = 5` and `mintOf = −3` the
validator's expected value is `filterPos(5 − 3) = 2 < 5` — and that the inequality
which actually holds, and which the composition consumes, is the SIGNED
`out ≥ in + mintOf`. This module states the corrected form. It is strictly the
right one here too: `pfilterPositiveCurrencyPairs`
(ProgrammableLogicBase.hs:1236-1252) drops non-positive entries, so a burn
(`q < 0`) imposes no requirement at all, and the signed inequality is exactly what
survives.

**THE SHAPE HAS NO MINI-LEDGER INPUTS, AND THAT IS PUBLISHED, NOT HIDDEN.**
`P6_shaped_noBaseInputs` below proves by `rfl` that
`inAtBaseQty (ScriptCredential plc) cs tn (SHAPE G6's inputs) = 0` for every leaf
assignment. So at this shape the signed inequality specialises to
`outAtBaseQty ≥ mintOf`, and the entire content of the theorem is the MINT side —
which is the side P6 is about. The `in` term is kept in the statement anyway so
the theorem is literally the composition's inequality and not a different one.

════════════════════════════════════════════════════════════════════════════
SCOPE — TWO BOUNDS, BOTH BINDING
════════════════════════════════════════════════════════════════════════════
**Bound 1 — CEK step budget 3300** (ADDENDUM E1), bridged to node acceptance by
`LR_BUDGET_global` (WSC/Honest.lean).

MEASURED FLOOR, and a warning for anyone reusing these shapes: the concrete SHAPE
G6 witness costs **K = 2837** steps, so the first attempt at budget **2500 was
provably VACUOUS** — its vacuity probe came back `Valid` (accept-UNSAT) and the
witness `Error`ed on budget exhaustion. The full ladder is in
`WSC/status-fragments/V3.md`. The interesting part is WHY 2837 ≫ SHAPE G1's 1541:
under a `NonMember` claim the mint entry is DROPPED, so
`expectedProgrammableOutputValue` is empty and
`poutputsContainExpectedValueAtCred`'s dispatch (ProgrammableLogicBase.hs:678-701)
short-circuits to `pconstant True` on an empty expected map. Under `Member` the
entry is RETAINED, so the containment scan actually runs. **The 1,296-step
difference IS P6's self-penalization, visible as execution cost.**

**Bound 2 — SHAPE G6**, published in full in WSC/Shaped/GlobalMemberShaped.lean's
header. In one line: one ada-only PUBKEY input (so no programmable inputs), one
reference input (the params node — a `Member` proof needs no directory node), TWO
script-address outputs each holding ada plus the minted asset with FREE credential
hashes and FREE quantities, a one-policy/one-token mint with a symbolic SIGNED
quantity, a 2-entry all-script withdrawal map, one redeemer entry, empty
cert/signatory/datum/vote/proposal lists, and the redeemer fixed to
`TransferAct [] [] [] [Member] 0` (FIVE fields since PR #112).

**Bound 2b — one token name, one policy.** The mint has exactly one `(cs, tn)`
pair. That matters more than usual here, because
`poutputsContainExpectedValueAtCred` DISPATCHES on the expected value's shape
(ProgrammableLogicBase.hs:678-701): exactly one asset takes the
`hasAtLeastAssetInProgOutputs` accumulate-scan, anything else takes the
wholesale/`pvalueContains` builtin path. **SHAPE G6 therefore exercises only the
single-asset path.** The multi-asset path is untested at UPLC by this module.

**Bound 2c — `paramsRefIdx = 0` is concrete**, a self-validating hint re-checked
by `pparamsAtRefIdx`'s `phasCSH` gate (ProgrammableLogicBase.hs:832). The
mint-proof list has no index to free (a `Member` proof carries none — that is the
point), so unlike P5 there is no G3-style index-loosening rung to attempt here.

════════════════════════════════════════════════════════════════════════════
NOT TRUE BY CONSTRUCTION
════════════════════════════════════════════════════════════════════════════
Full argument in WSC/Shaped/GlobalMemberShaped.lean's "WHY TWO OUTPUTS" stanza.
The short version: `isBalanced` forces `qq0 + qq1 = q`, i.e. the ledger guarantees
the minted tokens are SOMEWHERE among the outputs, and says nothing about WHICH.
The postcondition is about the sum over outputs at the base credential only, and
`ob0`, `ob1`, `plc` are three DIFFERENT free variables. So the theorem is not a
consequence of value conservation; the bytecode has to force enough of the split
to land at `plc`.

With a single output the ledger would have handed the postcondition over. That is
why SHAPE G6 has two, and why both quantities are free.

════════════════════════════════════════════════════════════════════════════
SOURCE FIDELITY (ProgrammableLogicBase.hs, wsc-poc worktree
`new-session-3c417d`, read 2026-07-25)
════════════════════════════════════════════════════════════════════════════
The `PTransferAct` path is :1189-1262. The chain this theorem certifies:

1. `pparamsAtRefIdx (pfromData protocolParamsCS) referenceInputs (pfromData
   paramsRefIdx)` (:1201-1203) yields `pprogLogicCred`, the base credential the
   postcondition names. SHAPE G6 pins `paramsRefIdx = 0` and reference input 0 IS
   the params node — the lesson of the SHAPE G2 falsification
   (WSC/SHAPING-RESULTS.md §6.1) is that this record must be named through the
   redeemer's own index, never through a chosen reference position.
2. `pvalueFromCred progLogicCred signatories withdrawalEntries inputs`
   (:1206-1212) — contributes nothing at this shape (the sole input is at a pubkey
   address), which is what `P6_shaped_noBaseInputs` records.
3. `pcheckMintLogicAndGetProgrammableValue` (:983-1027, invoked :1240-1245). Its
   `PMember` arm is :989-991: `self # proofsRest # mintCsPairs # (pcons #
   mintCsPair # programmableMintValue)` — the mint entry is CONSED VERBATIM onto
   the accumulator, no node, no datum, no arithmetic. That single line is P6.
4. the merge `pfilterPositiveCurrencyPairs #$ pcurrencyPairsUnionFast # …`
   (:1232-1246), which is why the inequality is signed and why burns impose
   nothing.
5. `poutputsContainExpectedValueAtCred progLogicCred (pfromData ptxInfo'outputs)
   expectedProgrammableOutputValue` (:1256-1259, defined :563-701). At this shape
   the dispatch (:678-701) selects `hasAtLeastAssetInProgOutputs` (:601-618), which
   accumulates `passetQtyInValue` over the outputs whose
   `paddressCredential ptxOut'address #== progLogicCred` and requires the running
   total to reach the required quantity. `outAtBaseQty` below is its ground-truth
   counterpart. (Note the validator short-circuits once the total is reached and so
   may not scan every output; the ground-truth sum is over ALL base outputs, which
   is ≥ what the validator accumulated because `validTxOutValue` makes every output
   quantity strictly positive. The ground-truth statement is therefore implied, not
   assumed.)

E1 CAVEAT (binding on every theorem in this file): what is proved is a statement
about `cekExecuteProgram … 3300`. A real node budgets in ExUnits, not CEK steps;
the bridge is `LR_BUDGET_global` in WSC/Honest.lean, which this task does not
discharge.
-/
import WSC.Shaped.GlobalMemberShaped
import WSC.Props.Shaped.P6Vocab
import WSC.Spec
import Blaster

-- Blaster closes Valid goals via `admit` (SPIKE-FINDINGS): expected `sorry`s.
set_option warn.sorry false
set_option maxHeartbeats 0

namespace WSC

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptContext ScriptHash TokenName
                          TxOut TxInInfo valueOf validRewardingContext)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-! ## Ground-truth vocabulary for the containment inequality

These two belong in `WSC/Spec.lean` alongside `outAtBase` / `inAtBase` / `mintOf`;
they live here for this stage only, to avoid cross-agent edit collisions in the
shared spec module. They mention nothing but ledger data. -/

/-- AUDIT (published scope, not a hidden assumption): SHAPE G6 has NO mini-ledger
inputs, for every leaf assignment. So the signed inequality proved below
specialises to `outAtBaseQty ≥ mintOf`, and the whole content of P6 at this shape
is the MINT side. -/
theorem P6_shaped_noBaseInputs
    (plc cs tn owner : ByteString) (inAda : Integer) :
    inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda] = 0 := rfl

/-! ## The bytecode obligation — PROVED -/

/-- **P6 over SHAPE G6 — PROVED AT UPLC.**

*If the real compiled transfer validator accepts a shape-G6 transaction — in which
the redeemer classifies the minted policy `cs` as `Member` — then the quantity of
`cs.tn` sitting at outputs at the mini-ledger base credential is at least the
quantity spent from the base PLUS the signed minted amount.*

I.e. the `Member` claim ADDS the mint to the containment requirement. It cannot
subtract it: there is no leaf assignment of SHAPE G6 that the bytecode accepts and
in which the minted tokens escape the base credential.

The base credential `plc` is the one the validator itself read out of the params
datum at the redeemer's `paramsRefIdx = 0`; `ob0`, `ob1`, `qq0`, `qq1` and `q` are
all free, and the ledger's own balance rule only forces `qq0 + qq1 = q`, never
WHERE the split lands. See the module header's "NOT TRUE BY CONSTRUCTION".

MEASURED: `✅ Valid`, ≈1.8 s at budget 3300 (and provably VACUOUS at 2500 — the
witness costs K = 2837). Validator source: ProgrammableLogicBase.hs:989-991 (the
`PMember` cons) + :1256-1259 (the containment call). -/
theorem P6_shaped_member_adds_to_requirement :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
      outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q) := by blaster (timeout: 1500)

/-- **The same statement in the `mintPos`-free specialised form**, obtained from
the theorem above by rewriting the (provably zero) input term. This is the shape
that reads most directly as "the Member claim's minted amount must remain inside
the mini-ledger". -/
theorem P6_shaped_member_mint_stays_at_base
    (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer)
    (hv : validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee))
    (ha : isSuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)) :
    outAtBaseQty (Credential.ScriptCredential plc) cs tn
      (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
      ≥ mintOf cs tn (Shape.mintOne cs tn q) := by
  have h := P6_shaped_member_adds_to_requirement ppCS cs tn q owner inAda ob0 outAda0 qq0
    ob1 outAda1 qq1 pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee hv ha
  rw [P6_shaped_noBaseInputs, Int.zero_add] at h
  exact h

/-! ## Polarity controls (ADDENDUM E9) — the full four-stanza set -/

/-- Negative control (≡ the contrapositive of P6 over the shape): a shape-G6
context in which not enough of the minted asset lands at the base credential is
REJECTED by the real bytecode. MEASURED: `✅ Valid`.

NOTE (E9, binding): also satisfied by budget-`Error`, so it cannot detect the
3300-step bound by itself — and at this shape that warning has teeth, because the
bound really was too low on the first attempt (2500). The vacuity probe and the
concrete witness are what caught it. -/
theorem P6_shaped_negative_control :
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    ¬ (outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q)) →
    isUnsuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) := by blaster (timeout: 1500)

/-- Tightness stanza: the NEGATION of P6's postcondition under an accepting run
must be FALSIFIABLE. Expected and MEASURED: `Falsified`. -/
def P6_shaped_tightness : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    isSuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    ¬ (outAtBaseQty (Credential.ScriptCredential plc) cs tn
        (memberShapedOutputs cs tn ob0 outAda0 qq0 ob1 outAda1 qq1)
        ≥ inAtBaseQty (Credential.ScriptCredential plc) cs tn [memberShapedInput owner inAda]
          + mintOf cs tn (Shape.mintOne cs tn q))

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P6_shaped_tightness]

/-- **MANDATORY VACUITY PROBE AT SHAPE G6.** "No accepting shape-G6 context exists
within 3300 CEK steps" must be FALSIFIED.

Expected and MEASURED: `✅ Falsified`. **This probe earned its keep on this
shape:** at the first attempted budget of 2500 it came back `Valid`, i.e. the shape
class was genuinely accept-UNSAT and the P6 theorem was vacuous, because the
witness needs 2837 steps. Nothing else in the control set detects that. -/
def P6_shaped_vacuity_probe : Prop :=
  ∀ (ppCS : CurrencySymbol)
    (cs tn : ByteString) (q : Integer)
    (owner : ByteString) (inAda : Integer)
    (ob0 : ByteString) (outAda0 : Integer) (qq0 : Integer)
    (ob1 : ByteString) (outAda1 : Integer) (qq1 : Integer)
    (pHash pCS pTn : ByteString) (pAda pQty : Integer)
    (dirCS plc glc slc : ByteString)
    (w0 w1 : ByteString) (a0 a1 : Integer)
    (fee : Integer),
    validRewardingContext
      (memberShapedCtx cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee) →
    ¬ isSuccessful
      (appliedGlobalMemberShaped3300.prop ppCS cs tn q owner inAda ob0 outAda0 qq0 ob1 outAda1 qq1
        pHash pCS pTn pAda pQty dirCS plc glc slc w0 w1 a0 a1 fee)

#blaster (timeout: 1500) (gen-cex: 0) (solve-result: 1) [P6_shaped_vacuity_probe]

/-! ## CONCRETE accepting witness OF EXACTLY SHAPE G6 — executable, no SMT

Leaf values: the policy `MMM` mints **+7** of `MMM.TOK` and the redeemer claims
`Member`. Both outputs sit at `ScriptCredential "PROGLOGIC"` — exactly the
`progLogicCred` the params datum publishes — holding **4** and **3** of the asset,
so 4 + 3 = 7 lands inside the mini-ledger and the containment requirement is met
by a genuine SPLIT across two outputs rather than by one wholesale output. 200
lovelace in, 100 + 50 out, 50 fee. Reference input 0 is the params node, whose
value carries the script-parameter policy `PARAMS`. -/

namespace P6ShapedWitness

set_option maxRecDepth 4000000

-- `ppCS` / `base` / `cs` / `tn` / `isHaltB` / `isHaltB_sound` moved to
-- WSC/Props/Shaped/P6Vocab.lean (task N4) and are in scope from there.

def ctx : ScriptContext :=
  memberShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "PROGLOGIC") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

/-- The witness satisfies the theorem's ledger-normalization hypothesis IN FULL. -/
theorem ctx_valid : validRewardingContext ctx = true := by native_decide

/-- The witness satisfies P6's postcondition, with the numbers visible: 7 of the
minted asset at the base credential against a +7 mint and zero base inputs. -/
theorem ctx_post :
    outAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoOutputs = 7
    ∧ mintOf cs tn ctx.scriptContextTxInfo.txInfoMint = 7
    ∧ inAtBaseQty base cs tn ctx.scriptContextTxInfo.txInfoInputs = 0 := by native_decide

/-- **NON-VACUITY, EXECUTABLE.** The real compiled bytecode ACCEPTS this shape-G6
context at budget 3300, through the SHAPED applied term the theorems above
quantify over. -/
theorem exec_accepts_at_3300 :
    isSuccessful
      (appliedGlobalMemberShaped3300.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "PROGLOGIC") 100 4
        (ByteString.mk "PROGLOGIC") 50 3
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
        50) :=
  isHaltB_sound _ (by native_decide)

/-- **EXACT STEP COUNT — `K = 2837`**: halts at 2837, budget-errors at 2836
(binary search in `WSC/Shaped/Probe/G6Diag.lean`, pinned here).

**Read this next to SHAPE G1's K = 1541** (`WSC/Props/Shaped/P5Shaped.lean`
`K_is_1541`), which is the same validator on the same-sized transaction with a
`NonMember` claim instead of a `Member` one. The 1,296-step gap is the containment
scan that a `Member` claim switches ON: under `NonMember` the mint entry is dropped,
the expected value is empty and the dispatch at ProgrammableLogicBase.hs:678-701
short-circuits. P6's self-penalization is therefore visible even in the step count,
before any theorem is proved.

RE-MEASURED against the PR #112 bytecode (task N4), two-sided. It is IDENTICAL
to the re-cut sibling's value in `WSC/Props/Shaped/P6ShapedR.lean` on the same witness leaves — redeemer
coverage costs zero CEK steps, as before. -/
theorem K_is_2196 :
    isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 2196) = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
              (globalInputs1600 ppCS ctx) 2195) = false := by native_decide

/-! ### § SELF-PENALIZATION, MEASURED — the same escape, both classifications

This is the executable form of P6's plain-English sentence, and the sharpest
control in the module: it exhibits ONE ledger-legal transaction and shows that the
`Member` claim REJECTS it while the `NonMember` claim ACCEPTS it. Claiming Member
therefore costs the claimant; it cannot buy anything.

`ctxEscape` is `ctx` with output 1 moved OUTSIDE the mini-ledger (payment
credential `OUTSIDE` instead of `PROGLOGIC`), so only 4 of the 7 minted tokens
land at the base. Nothing else changes: the ledger balance, the value canonicity,
the withdrawal map and the params reference input are identical, so this is a
transaction a real attacker could submit.

`ctxEscapeNonMember` is the SAME skeleton with the mint proof replaced by
`NonMember 1` and a covering directory node added at reference input 1
(`nonMemberSiblingCtx`, WSC/Shaped/GlobalMemberShaped.lean). It is accepted. -/

/-- SHAPE G6 with 3 of the 7 minted tokens escaping to a non-base credential. -/
def ctxEscape : ScriptContext :=
  memberShapedCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "OUTSIDE") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

/-- The escaping context IS ledger-valid, and it genuinely violates P6's
postcondition: only 4 of the 7 minted tokens are at the base. -/
theorem ctxEscape_valid_and_escaping :
    validRewardingContext ctxEscape = true
    ∧ outAtBaseQty base cs tn ctxEscape.scriptContextTxInfo.txInfoOutputs = 4
    ∧ mintOf cs tn ctxEscape.scriptContextTxInfo.txInfoMint = 7 := by native_decide

/-- …and the REAL compiled bytecode REJECTS it under the `Member` claim at budget
3300. So P6 excludes a non-empty, ledger-legal set of transactions. -/
theorem exec_rejects_escape_under_member :
    isHaltB
      (appliedGlobalMemberShaped3300.exec ppCS (ByteString.mk "MMM") (ByteString.mk "TOK") 7
        (ByteString.mk "OWNER") 200
        (ByteString.mk "PROGLOGIC") 100 4
        (ByteString.mk "OUTSIDE") 50 3
        (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
        (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
        (ByteString.mk "SEIZE")
        (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
        50) = false := by native_decide

/-- The SAME escape with the mint proof changed to `NonMember 1` and a covering
directory node supplied at reference input 1. -/
def ctxEscapeNonMember : ScriptContext :=
  nonMemberSiblingCtx (ByteString.mk "MMM") (ByteString.mk "TOK") 7
    (ByteString.mk "OWNER") 200
    (ByteString.mk "PROGLOGIC") 100 4
    (ByteString.mk "OUTSIDE") 50 3
    (ByteString.mk "PANCHOR") (ByteString.mk "PARAMS") (ByteString.mk "PTOK") 100 1
    (ByteString.mk "DIRCS") (ByteString.mk "PROGLOGIC") (ByteString.mk "GLOBAL")
    (ByteString.mk "SEIZE")
    (ByteString.mk "DIRNODE") (ByteString.mk "DIRCS") (ByteString.mk "NODETOK") 100 1
    (ByteString.mk "AAA") (ByteString.mk "ZZZ") (ByteString.mk "TLS") (ByteString.mk "ILS")
    (ByteString.mk "GS")
    (ByteString.mk "GLOBAL") (ByteString.mk "ZZZZ") 0 0
    50

/-- **P6's PLAIN-ENGLISH CLAIM, MEASURED ON THE REAL BYTECODE.** The escaping
transaction that the `Member` claim REJECTS is ACCEPTED once the claim is changed
to `NonMember` (with a covering node). So a `Member` claim strictly ENLARGES what
the transaction must satisfy — it is self-penalizing, and an attacker gains
nothing by making it.

(The `NonMember` side is of course only safe because P5 forces the covering node
to be authentic and its interval to exclude `cs` — `P5_shaped_indexed`,
WSC/Props/Shaped/P5Shaped.lean — and because DirWF then makes such a node
unobtainable for a registered policy. That is P5's job, not P6's.) -/
theorem exec_accepts_same_escape_under_nonmember :
    validRewardingContext ctxEscapeNonMember = true
    ∧ isHaltB (PlutusCore.UPLC.CekMachine.cekExecuteProgram programmableLogicGlobal1600.script
                (globalInputs1600 ppCS ctxEscapeNonMember) 3300) = true := by native_decide

end P6ShapedWitness

end WSC
