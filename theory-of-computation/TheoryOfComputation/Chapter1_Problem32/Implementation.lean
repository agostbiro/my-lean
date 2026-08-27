import Mathlib.Tactic.DeriveFintype
import TheoryOfComputation.Chapter1_Problem32.Specification

namespace TheoryOfComputation.Chapter1.Problem32

/-!
# Problem 1.32 — Implementation

The specification of the language `B` is in `Specification.lean`; this file
builds the DFA that recognizes `B.reverse`. The proof that it does is in
`Proof.lean`.

## Solution

We can use the theorem that if a language is regular, then its reverse is
regular as well to simplify the problem. This way, we can iterate through the
reversed string and keep track of the carries to recognize a string (the string
is in B if the carry is zero at the end).

We can construct a DFA that recognizes B^R as follows (dead states are
omitted):

              000                              010
              011                              100
              101                              111
            ┌──────┐                        ┌──────┐
            │      ↓                        │      ↓
           ╔════════╗       110            ┌──────────┐
  start ──▶║   q0   ║───────────────────▶  │    q1    │
           ║ carry 0║  ◀───────────────────│ carry 1  │
           ╚════════╝       001            └──────────┘

## Reading the formalization

The pieces below line up with the picture:

* `q0` is `DfaState.carry false` and `q1` is `DfaState.carry true` — the state is the carry
  produced by the columns read so far;
* the dead states the picture omits are the single state `DfaState.dead`;
* the edge labels are the columns `dfaStep` maps to a carry state: from `q0` it
  keeps `000`, `011`, `101` and moves to `q1` on `110`; from `q1` it keeps `010`, `100`,
  `111` and moves back to `q0` on `001`. Everything else falls into `DfaState.dead`.

The automaton consumes columns least significant bit first, so everything about it is
stated in the `valueLE` convention. Unfolding `valueBE` converts between the two
conventions, once, in `adderDFA_accepts` (in `Proof.lean`).
-/

/-- The states of the DFA for `B^R`.

`carry c` is the state drawn as `q0` (`c = false`) and `q1` (`c = true`) above.
The carry is the carry produced by the columns read so far, which is the carry
*into* the next column. `dead` is the sink the picture omits. It is entered as
soon as a column's bottom bit disagrees with the sum bit, and is never left. -/
inductive DfaState where
  /-- The columns read so far produced carry `c`. -/
  | carry (c : Bool)
  /-- A column has already contradicted the addition; the word is rejected. -/
  | dead
  deriving DecidableEq, Fintype

/-- The transition function of the DFA, which is a one-bit full adder with a sink.

The carry out is the majority of `x`, `y` and `c`. -/
def dfaStep : DfaState → Sigma3 → DfaState
  | .dead, _ => .dead
  | .carry c, (x, y, z) =>
      -- Verify that the transition is valid:
      -- `z = x + y + c`
      -- `z = x XOR y XOR c`
      if z = (x ^^ y ^^ c) then
        -- There is a carry if at least two of x, y and c are 1.
        .carry (Bool.atLeastTwo x y c)
      else
        .dead

/-- The DFA drawn above.

It reads columns least significant first, i.e. it recognizes `B.reverse` rather than `B`.
Carries flow from the low columns towards the high ones, so only in that direction is the
next state a function of the current one. `start` is `carry false` because nothing carries
into the least significant column, and `carry false` is also the only accepting state because
a carry out of the most significant column would be an overflow. -/
def adderDFA : DFA Sigma3 DfaState where
  step := dfaStep
  start := .carry false
  accept := {.carry false}

/-! Check the transitions from the figure. -/

-- `q0` keeps its state on `000`, `011` and `101`: no carry is produced.
example : dfaStep (.carry false) (false, false, false) = .carry false := by decide
example : dfaStep (.carry false) (false, true, true) = .carry false := by decide
example : dfaStep (.carry false) (true, false, true) = .carry false := by decide
-- `q0 --110--> q1`: `1 + 1` is `0` carry `1`.
example : dfaStep (.carry false) (true, true, false) = .carry true := by decide
-- `q1` keeps its state on `010`, `100` and `111`: the carry is passed on.
example : dfaStep (.carry true) (false, true, false) = .carry true := by decide
example : dfaStep (.carry true) (true, false, false) = .carry true := by decide
example : dfaStep (.carry true) (true, true, true) = .carry true := by decide
-- `q1 --001--> q0`: `0 + 0 + 1` is `1` carry `0`.
example : dfaStep (.carry true) (false, false, true) = .carry false := by decide
-- Spot checks for dead state.
example : dfaStep (.carry false) (false, false, true) = .dead := by decide
example : dfaStep .dead (false, false, false) = .dead := by decide

/-! Check the examples from the problem -/

example :
    adderDFA.evalFrom (.carry false)
      [(true, false, true), (false, false, true)] = .dead := by
  decide

example :
    adderDFA.evalFrom (.carry false)
      [(true, true, false), (true, false, false), (false, false, true)] = .carry false := by
  decide

end TheoryOfComputation.Chapter1.Problem32
