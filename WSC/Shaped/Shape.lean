/-
WSC/Shaped/Shape.lean — the SHAPING vocabulary (task Z2).

WHAT SHAPING IS, PRECISELY. A *shape* is a Lean function
`σ : leaves → ScriptContext` that builds a `ScriptContext` whose entire `Data`
SKELETON is a closed term — every list length, every constructor tag, every
`Option`, every nesting depth is fixed — while every SCALAR LEAF (a
`ByteString` or an `Integer`) is a free variable. A shaped theorem quantifies
over the leaves, not over `ScriptContext`, and is stated against a prep whose
inputs function is `… :: purposeInputs (σ leaves)`, so the CEK symbolic
execution sees the concrete skeleton and only the leaves stay symbolic.

WHY (measured motivation, WSC/Props/P4_Minting.lean "SOLVER COST" and
WSC/Props/P5_NonMember.lean "OBLIGATION STATUS"): below the minimal accepting
step count the bytecode obligations are discharged in seconds *because accept is
UNSAT*; at or above it Z3 returns no verdict even with 3300 s. The cost is the
SMT search over a fully symbolic `Data` context, because every
`unConstrData`/`headList`/`chooseList` on a symbolic `Data` leaves a residual
branch. A fixed skeleton collapses all of those branches at prep time, leaving
only `equalsByteString` / `lessThanByteString` / `equalsInteger` over the leaves.

WHAT SHAPING COSTS (published as SCOPE on every shaped theorem): the theorem
covers exactly the transaction shapes σ ranges over, and nothing else. It is
honest bounded verification in the *second* dimension — the first being the CEK
step budget of ADDENDUM E1 — and a shaped theorem must therefore always be
quoted together with (a) its budget K and (b) its shape.

WHAT SHAPING MUST NOT DO. Security-relevant content stays symbolic:
credentials, script hashes, currency symbols, token names, amounts, datum
payloads. Only *self-validating hints* may be made concrete — above all the
redeemer's index fields, which the validator uses to point at a list position
and then re-checks (`pcheckedDrop`/`phead` + the per-branch conditions), so
fixing them removes no adversarial power beyond restricting the shape class.

This module holds only the Data-level constants shared by the shapes.
-/
import CardanoLedgerApi.V3

namespace WSC.Shape

open CardanoLedgerApi.V3 (Credential CurrencySymbol ScriptHash TokenName)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-- The ada policy id (`""`) — the first entry of every canonical `Value`. -/
def adaCS : CurrencySymbol := ByteString.mk ""

/-- The ada token name (`""`). -/
def adaTN : TokenName := ByteString.mk ""

/-- Canonical ada-only `Value` with a symbolic lovelace amount. Shape:
`[(B "", Map [(B "", I n)])]` — `validTxOutValue`'s canonical, lovelace-first,
strictly-positive form (CardanoLedgerApi/V1/Contexts.lean:769-784). -/
def adaOnly (n : Integer) : CardanoLedgerApi.V1.Value.Value :=
  [(Data.B adaCS, Data.Map [(Data.B adaTN, Data.I n)])]

/-- Canonical `Value` with ada plus exactly ONE other policy carrying exactly
ONE token name, all three quantities symbolic. -/
def adaPlusOne (n : Integer) (cs : CurrencySymbol) (tn : TokenName) (q : Integer)
    : CardanoLedgerApi.V1.Value.Value :=
  [ (Data.B adaCS, Data.Map [(Data.B adaTN, Data.I n)])
  , (Data.B cs, Data.Map [(Data.B tn, Data.I q)]) ]

/-- Mint field carrying exactly one policy and one token name, symbolic
quantity. Shape only: the sign of `q` is NOT fixed. -/
def mintOne (cs : CurrencySymbol) (tn : TokenName) (q : Integer)
    : CardanoLedgerApi.V3.MintValue :=
  [(Data.B cs, Data.Map [(Data.B tn, Data.I q)])]

/-- A finite, closed validity interval `[lo, hi]` with symbolic bounds
(`Data.Constr` skeleton of `PPOSIXTimeRange`; `Finite`/`Closed` tags fixed). -/
def range (lo hi : Integer) : Data :=
  Data.Constr 0 [ Data.Constr 0 [Data.Constr 1 [Data.I lo], Data.Constr 1 []]
                , Data.Constr 0 [Data.Constr 1 [Data.I hi], Data.Constr 1 []] ]

end WSC.Shape
