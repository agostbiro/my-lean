import Mathlib.Computability.NFA
import Mathlib.Tactic.DeriveFintype

namespace TheoryOfComputation.Chapter1.Problem32

/-!
# Problem 1.32

Let `Σ₃` be the alphabet of all 3-bit columns, i.e. `Bool × Bool × Bool`.
A string `w ∈ Σ₃*` therefore gives three rows of bits. Read each row as a
binary number, most significant bit first (all three rows have the same
length `|w|`, so no overflow is permitted). Define

    B = { w ∈ Σ₃*  | the bottom row of w is the sum of the top two rows }

For example:

⎡ 0 ⎤⎡ 1 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥⎢ 1 ⎥ ∈ B, because 011 + 001 = 100
⎣ 1 ⎦⎣ 0 ⎦⎣ 0 ⎦

But

⎡ 0 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥ ∉ B, because 01 + 00 ≠ 11
⎣ 1 ⎦⎣ 1 ⎦

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

* `Sigma3` is `Σ₃`, one column, written as the triple `(row 1 bit, row 2 bit, row 3 bit)`;
* `B` is the language above, with `valueBE` reading a row most significant bit first;
* `valueLE` reads a row the other way round, least significant bit first, which is the
  order the automaton consumes columns in. Everything about the automaton is stated in that
  convention. Unfolding `valueBE` converts between the two, once, in `carryDFA_accepts`.
* `q0` is `DfaState.carry false` and `q1` is `DfaState.carry true` — the state is the carry
  produced by the columns read so far;
* the dead states the picture omits are the single state `DfaState.dead`;
* the edge labels are the columns `dfaStep` maps to a carry state: from `q0` it
  keeps `000`, `011`, `101` and moves to `q1` on `110`; from `q1` it keeps `010`, `100`,
  `111` and moves back to `q0` on `001`. Everything else falls into `DfaState.dead`.
-/

/-- A symbol in the alphabet `Σ₃`: a column of three bits. -/
abbrev Sigma3 := Bool × Bool × Bool

/-- Little endian interpretation of a list of bools. -/
def valueLE : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * valueLE bs

/-- Big endian interpretation of a list of bools: reading a list most significant bit first
is reading its reverse least significant bit first.

This definition is the insight the whole solution rests on, stated once: the `B` side of the
problem is most significant bit first (fixed by the problem statement), the automaton side is
least significant bit first (fixed by the direction carries flow in), and `reverse` is what
connects them. -/
def valueBE (bs : List Bool) : Nat := valueLE bs.reverse

/-- The top row of a word: the first bit of every column. -/
def row1 (w : List Sigma3) : List Bool := w.map fun (x, _, _) => x

/-- The middle row of a word: the second bit of every column. -/
def row2 (w : List Sigma3) : List Bool := w.map fun (_, y, _) => y

/-- The bottom row of a word: the third bit of every column. -/
def row3 (w : List Sigma3) : List Bool := w.map fun (_, _, z) => z

/-- The language `B` of the problem: words whose bottom row is the sum of the top two rows.

Note that all three rows have equal length by definition (they're extracted from the same list). -/
def B : Language Sigma3 :=
  { wBE | valueBE (row3 wBE) = valueBE (row1 wBE) + valueBE (row2 wBE) }

/-- Helper to avoid unfolding manually in subsequent proofs. -/
lemma mem_B_iff (wBE : List Sigma3) :
    wBE ∈ B ↔ valueBE (row3 wBE) = valueBE (row1 wBE) + valueBE (row2 wBE) := Iff.rfl

/-! ### Rewriting rules for rows

Peeling the leading column off a word peels the leading bit off each of its rows, and reversing
a word reverses each of its rows. Both facts hold by computation, but they are needed as
rewrite rules (rather than by unfolding `row1`/`row2`/`row3`) so that the proofs below can keep
talking about `row1 columns` instead of an unfolded `List.map`. -/

/-- Peeling a column off a word peels the leading bit off its top row. -/
@[simp] lemma row1_cons (x y z : Bool) (columns : List Sigma3) :
    row1 ((x, y, z) :: columns) = x :: row1 columns := rfl

/-- Peeling a column off a word peels the leading bit off its middle row. -/
@[simp] lemma row2_cons (x y z : Bool) (columns : List Sigma3) :
    row2 ((x, y, z) :: columns) = y :: row2 columns := rfl

/-- Peeling a column off a word peels the leading bit off its bottom row. -/
@[simp] lemma row3_cons (x y z : Bool) (columns : List Sigma3) :
    row3 ((x, y, z) :: columns) = z :: row3 columns := rfl

/-- Reversing a word reverses its top row. -/
@[simp] lemma row1_reverse (w : List Sigma3) : row1 w.reverse = (row1 w).reverse := by
  simp [row1]

/-- Reversing a word reverses its middle row. -/
@[simp] lemma row2_reverse (w : List Sigma3) : row2 w.reverse = (row2 w).reverse := by
  simp [row2]

/-- Reversing a word reverses its bottom row. -/
@[simp] lemma row3_reverse (w : List Sigma3) : row3 w.reverse = (row3 w).reverse := by
  simp [row3]

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
def carryDFA : DFA Sigma3 DfaState where
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

/-- Carry step is correct arithmetically. -/
lemma dfaStep_carry_iff (x y z carryIn carryOut : Bool) :
    dfaStep (.carry carryIn) (x, y, z) = .carry carryOut ↔
      x.toNat + y.toNat + carryIn.toNat = z.toNat + 2 * carryOut.toNat := by
  cases x <;> cases y <;> cases z <;> cases carryIn <;> cases carryOut <;>
    simp [dfaStep]

/-- `dead` is a sink: once a column has contradicted the addition, no suffix recovers.

`evalFrom_carry_iff` peels the leading column, which is the run's first step, so the case
where that step dies leaves a whole run still to evaluate. This lemma evaluates it. -/
lemma evalFrom_dead (w : List Sigma3) : carryDFA.evalFrom .dead w = .dead := by
  induction w with
  | nil => rfl
  | cons column columns induction_hypothesis =>
    simpa [DFA.evalFrom, carryDFA, dfaStep] using induction_hypothesis

/-- A run over a nonempty word ends in a carry state exactly when its first
column produces an intermediate carry and the rest of the run produces the
final carry. -/
lemma evalFrom_cons_carry_iff (x y z carryIn carryOut : Bool) (w : List Sigma3) :
    carryDFA.evalFrom (.carry carryIn) ((x, y, z) :: w) = .carry carryOut ↔
      ∃ carryMid, dfaStep (.carry carryIn) (x, y, z) = .carry carryMid ∧
        carryDFA.evalFrom (.carry carryMid) w = .carry carryOut := by
  change carryDFA.evalFrom (dfaStep (.carry carryIn) (x, y, z)) w = .carry carryOut ↔ _
  cases dfaStep (.carry carryIn) (x, y, z) with
  | dead => rw [evalFrom_dead]; simp
  | carry carryMid => simp

/-- A binary addition equation splits into the equation for its low bit and
the equation for the remaining higher bits, connected by an intermediate
carry.

This iff also covers the dead-column case of the induction for free: every term other
than the low bits is even, so when the low bit has the wrong parity no `carryMid`
satisfies the right-hand side — matching the run entering `dead` on the left. -/
lemma low_bit_split (x y z carryIn : Bool) (a b d k : Nat) :
    (x.toNat + 2 * a) + (y.toNat + 2 * b) + carryIn.toNat
        = (z.toNat + 2 * d) + 2 * k ↔
      ∃ carryMid : Bool,
        x.toNat + y.toNat + carryIn.toNat = z.toNat + 2 * carryMid.toNat ∧
        a + b + carryMid.toNat = d + k := by
  cases x <;> cases y <;> cases z <;> cases carryIn <;> simp <;> omega

/-- Running the carry DFA over a little-endian word `wLE` from carry
  `carryIn` lands in state carry `carryOut` when the equation holds:
  `row1 + row2 + carryIn = row3 + carryOut · 2^|wLE|`.
-/
lemma evalFrom_carry_iff (wLE : List Sigma3) (carryIn carryOut : Bool) :
    carryDFA.evalFrom (.carry carryIn) wLE = .carry carryOut ↔
      valueLE (row1 wLE) + valueLE (row2 wLE) + carryIn.toNat
        = valueLE (row3 wLE) + carryOut.toNat * 2 ^ wLE.length := by
  induction wLE generalizing carryIn with
  | nil =>
    cases carryIn <;> cases carryOut <;>
      simp [valueLE, row1, row2, row3, DFA.evalFrom]
  | cons column columnsLE induction_hypothesis =>
    obtain ⟨x, y, z⟩ := column
    rw [evalFrom_cons_carry_iff]
    simp_rw [dfaStep_carry_iff, induction_hypothesis]
    simp only [row1_cons, row2_cons, row3_cons, valueLE, List.length_cons, pow_succ]
    -- This is `low_bit_split` with `k := carryOut.toNat * 2 ^ |columnsLE|`, but the two
    -- sides write the same number differently: the goal has `carryOut.toNat * (2 ^ n * 2)`
    -- (from `pow_succ`), the lemma has `2 * (carryOut.toNat * 2 ^ n)`. The `*`/`+`
    -- commutativity and associativity lemmas below let `simpa` match them up.
    -- `omega` can't finish instead: it doesn't handle the `∃ carryMid`.
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (low_bit_split x y z carryIn
          (valueLE (row1 columnsLE))
          (valueLE (row2 columnsLE))
          (valueLE (row3 columnsLE))
          (carryOut.toNat * 2 ^ columnsLE.length)).symm

/-- The DFA recognizes the reverse of `B` 

`B.reverse = { w | w.reverse ∈ B }` -/
theorem carryDFA_accepts : carryDFA.accepts = B.reverse := by
  -- Change the goal from "these two languages are the same" to "for an arbitrary word, the DFA accepts it iff it's in B.reverse".
  ext wLE
  -- `evalFrom_carry_iff` states that running the carry DFA over a little-endian word `wLE` from carry
  -- carryIn` lands in state carry `carryOut` when the equation holds:
  -- `row1 + row2 + carryIn = row3 + carryOut · 2^|wLE|`.
  -- Since we initialize it with `false, false`, the  invariant is "no carry in
  -- at the low end, no carry out at the high end".
  have invariant := evalFrom_carry_iff wLE false false
  -- Since they're zero, cancel the terms involving carries from the
  -- invariant's equation which becomes `row1 + row2 = row3`.
  simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at invariant
  -- Acceptance is by definition "the run from the start state ends in `carry false`".
  have mem_accepts_iff :
      wLE ∈ carryDFA.accepts ↔ carryDFA.evalFrom (.carry false) wLE = .carry false := Iff.rfl
  -- Remember, the goal is `wLE ∈ carryDFA.accepts ↔ wLE ∈ B.reverse`. We need to show that both sides are equal.
  rw [
    -- First we massage the left side.
    -- Replace `wLE ∈ carryDFA.accepts` with `carryDFA.evalFrom (.carry false) wLE = .carry false`
    mem_accepts_iff,
    -- Replace `carryDFA.evalFrom (.carry false) wLE = .carry false` with 
    -- `valueLE (row1 wLE) + valueLE (row2 wLE) = valueLE (row3 wLE)`
    invariant,

    -- Then massage the right side.
    -- `B.reverse` is defined as `{ w | w.reverse ∈ B }`. 
    -- Replace `wLE ∈ B.reverse` with `wLE.reverse ∈ B`.
    Language.mem_reverse,
    -- Following the exercise, we defined the `B` language as: 
    -- `wBE ∈ B ↔ valueBE (row3 wBE) = valueBE (row1 wBE) + valueBE (row2 wBE)`.
    -- Applying this definition lets us replace `wLE.reverse ∈ B` with
    -- `valueBE (row3 wLE.reverse) = valueBE (row1 wLE.reverse) + valueBE (row2 wLE.reverse)`
    mem_B_iff
  ]
  -- We have almost met the goal now, except the right side of the equation has `valueBE (row wLE.reverse)` instead of `valueLE (row wLE)`.
  simp only [
    -- Push the `reverse` from the word down onto its rows, giving
    -- `valueBE (row3 wLE).reverse = valueBE (row1 wLE).reverse + valueBE (row2 wLE).reverse`.
    row1_reverse,
    row2_reverse,
    row3_reverse,
    -- Unfold "most significant bit first" as "least significant bit first, backwards", giving
    -- `valueLE (row3 wLE).reverse.reverse = valueLE (row1 wLE).reverse.reverse + …`.
    valueBE,
    -- Cancel the two reversals. Both sides now read the same three rows the same way:
    -- `valueLE (row1 wLE) + valueLE (row2 wLE) = valueLE (row3 wLE) ↔
    --    valueLE (row3 wLE) = valueLE (row1 wLE) + valueLE (row2 wLE)`.
    List.reverse_reverse,
    -- All that is left is the direction of the equation: `B` puts the sum on the right, the
    -- automaton's invariant on the left. Flipping one of them leaves `X ↔ X`, which closes the goal.
    eq_comm
  ]

/-- Corollary: `B^R` is regular since `carryDFA` is a DFA with finitely many states that recognizes it. -/
theorem B_reverse_isRegular : B.reverse.IsRegular :=
  ⟨DfaState, inferInstance, carryDFA, carryDFA_accepts⟩

/-- Hence `B` itself is regular, by closure of the regular languages under reversal. -/
theorem B_isRegular : B.IsRegular :=
  Language.isRegular_reverse_iff.mp B_reverse_isRegular

/-! ### The examples from the problem statement

The matrix art above writes the three rows across the page, so each *column* of the picture
is one letter of `Σ₃`. Reading the first example column by column gives
`(0,0,1)`, `(1,0,0)`, `(1,1,0)`. -/

/-- `011 + 001 = 100`, so this word is in `B`. -/
example : [(false, false, true), (true, false, false), (true, true, false)] ∈ B := by
  rw [mem_B_iff]; decide

/-- `01 + 00 ≠ 11`, so this word is not in `B`. -/
example : [(false, false, true), (true, false, true)] ∉ B := by
  rw [mem_B_iff]; decide

end TheoryOfComputation.Chapter1.Problem32
