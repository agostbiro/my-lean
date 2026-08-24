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
  -- Proof by exhaustion over the truth table that is constructed by chaining cases where each
  -- case is true or false.
  cases x <;> cases y <;> cases z <;> cases carryIn <;> cases carryOut <;>
    -- The simp tactic does a lot of have lifting here. It uses lemmas and hypothesis to simplify
    -- the goal target for each case.
    -- Consider the goal x=true, y=true, z=false, carryIn=false, carryOut=true.
    -- Filling in the values results in:
    --   dfaStep (.carry false) (true, true, false) = .carry true
    --     ↔ true.toNat + true.toNat + false.toNat = false.toNat + 2 * true.toNat
    -- Simp first rewrites the left-hand side of the equivalence to:
    --   if false = (true ^^ true ^^ false) then .carry (Bool.atLeastTwo true true false) else .dead = .carry true
    -- Then it performs boolean evaluation:
    --   if false = false then .carry true else .dead. = .carry true
    -- Which becomes
    --   .carry true = .carry true
    -- There is some further bookkeeping to done by simp for Lean to accept the above expression as
    -- true, but we'll skip over that now and look at the right-hand side of the equivalance which
    -- is relatively simple in comparison.
    --   true.toNat + true.toNat + false.toNat = false.toNat + 2 * true.toNat
    -- results in
    --   1 + 1 + 0 = 0 + 2 * 1
    -- which after some further steps will be resolved to true.
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

/-! ### Sanity check: encoding numbers into words

`B` is a definition, so nothing in this file can prove it correct: it is the trusted
translation of the problem statement into Lean. What we can do is translate the statement a
second time, independently, and prove that the two translations agree. `encode` builds the
word for the addition `a + b = c` directly from the three numbers, and `encode_mem_B_iff`
restates membership in `B` with no lists, rows or endianness in sight:
`encode n a b c ∈ B ↔ c = a + b`. A convention error in `B` (wrong endianness, top and bottom
row confused) would make that theorem unprovable. The check leaves no word out either:
`encode_rows` shows that every word is the encoding of its own three rows, so the words the
theorem talks about are all of them, not just those `encode` happens to build.

Limitations of this check:

* It does not prove `B` correct — nothing can. `encode` is itself a trusted translation of
  the English statement; the theorem only shows the two translations agree.
* A shared misunderstanding survives it: if `B` and `encode` both misread the problem the
  same way (say, both swap what "top row" means, or both pick the wrong endianness), the
  theorem still goes through.
* It is only as strong as the independence of the two definitions; see the warning on
  `encode`.
* Swapping the two summand rows is invisible to it. `B` asks for `row3 = row1 + row2`, and
  addition commutes, so a `B` that had the two top rows the other way round would prove the
  same theorem. Only the sum row is pinned down.
* The bounds `a, b, c < 2 ^ n` restrict the theorem to numbers representable in `n` bits.
  That is not a gap: it is the problem's no-overflow rule made explicit.
-/

/-- The `n`-bit big-endian bit string of `a`. Bits from position `n` up are dropped, so this
only spells out `a` itself when `a < 2 ^ n`; both uses below carry that hypothesis. -/
def bitsBE (n a : Nat) : List Bool := (List.range n).reverse.map a.testBit

/-- The word for the addition `a + b = c`, written in `n` columns: column `i` holds bit `i`
of each number, most significant column first.

Warning: the sanity check `encode_mem_B_iff` is only meaningful while this definition stays
stylistically independent of `valueLE`. Do not rewrite it as the step-by-step inverse of
`valueLE` (peeling `% 2` and `/ 2`); that would make the check essentially tautological rather
than an independent consistency check. -/
def encode (n a b c : Nat) : List Sigma3 :=
  (List.range n).reverse.map fun i => (a.testBit i, b.testBit i, c.testBit i)

/-- Extracting the top row of an encoded word gives back the bits of `a`. -/
lemma row1_encode (n a b c : Nat) : row1 (encode n a b c) = bitsBE n a := by
  simp [row1, encode, bitsBE, List.map_map, Function.comp]

/-- Extracting the middle row of an encoded word gives back the bits of `b`. -/
lemma row2_encode (n a b c : Nat) : row2 (encode n a b c) = bitsBE n b := by
  simp [row2, encode, bitsBE, List.map_map, Function.comp]

/-- Extracting the bottom row of an encoded word gives back the bits of `c`. -/
lemma row3_encode (n a b c : Nat) : row3 (encode n a b c) = bitsBE n c := by
  simp [row3, encode, bitsBE, List.map_map, Function.comp]

/-- Reading the first `n` bits of `a` least significant first recovers `a`, provided `a`
fits in `n` bits.

This is where the two translations meet: the left-hand side reads bits the way `valueLE`
does, the right-hand side produces them the way `encode` does
(by `Nat.testBit`). -/
lemma valueLE_range_testBit {n a : Nat} (h : a < 2 ^ n) :
    valueLE ((List.range n).map a.testBit) = a := by
  induction n generalizing a with
  | zero =>
    -- `a < 2 ^ 0` forces `a = 0`, and the empty bit string reads as `0`.
    simp only [pow_zero, Nat.lt_one_iff] at h
    simp [h, valueLE]
  | succ n induction_hypothesis =>
    -- Halving strips the low bit: `a / 2` fits in `n` bits.
    have hdiv : a / 2 < 2 ^ n := by
      rw [pow_succ] at h
      omega
    -- The tail bits of `a` are the bits of `a / 2`.
    have htail : a.testBit ∘ Nat.succ = (a / 2).testBit := by
      funext i
      exact Nat.testBit_succ a i
    -- The head bit of `a` is its parity.
    have hbit : (a.testBit 0).toNat = a % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar <;> simp [Nat.testBit_zero, hpar]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, htail]
    simp only [valueLE]
    rw [induction_hypothesis hdiv, hbit]
    omega

/-- Reading an `n`-bit big-endian bit string most significant bit first recovers the number,
provided it fits in `n` bits. -/
lemma valueBE_bitsBE {n a : Nat} (h : a < 2 ^ n) : valueBE (bitsBE n a) = a := by
  rw [valueBE, bitsBE, List.map_reverse, List.reverse_reverse]
  exact valueLE_range_testBit h

/-- The sanity check: membership in `B` of an encoded word says exactly that the addition
holds, stated with plain numbers only.

The bounds are `B`'s implicit no-overflow rule made explicit: only sums representable in
`n` bits are in scope, because all three rows have the same length. -/
theorem encode_mem_B_iff {n : Nat} (a b c : Nat)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
    encode n a b c ∈ B ↔ c = a + b := by
  rw [mem_B_iff, row1_encode, row2_encode, row3_encode,
    valueBE_bitsBE ha, valueBE_bitsBE hb, valueBE_bitsBE hc]

/-! ### The check leaves no word out

`encode_mem_B_iff` speaks about the words `encode` builds. That would be a weak check if
`encode` only reached some words: the rest of `B` would go unexamined. It reaches all of
them. Reading a word's three rows as numbers and encoding those numbers back gives the word
again, so every word of length `n` is `encode n a b c` for some `a, b, c < 2 ^ n`. -/

/-- Reading a little-endian bit string as a number and asking for bit `i` gives bit `i` of
the string back. -/
lemma testBit_valueLE {bs : List Bool} {i : Nat} (h : i < bs.length) :
    (valueLE bs).testBit i = bs[i] := by
  induction bs generalizing i with
  | nil =>
    -- The empty string has no bit `i`.
    simp at h
  | cons b bs induction_hypothesis =>
    cases i with
    | zero =>
      -- Bit `0` of `b.toNat + 2 * valueLE bs` is its parity, which is `b`.
      cases b <;> simp [valueLE, Nat.testBit_zero]
    | succ i =>
      -- Bit `i + 1` is bit `i` after halving, and halving strips the leading bit off.
      rw [valueLE, Nat.testBit_succ]
      have hbit : b.toNat < 2 := Bool.toNat_lt b
      have hhalve : (b.toNat + 2 * valueLE bs) / 2 = valueLE bs := by omega
      rw [hhalve]
      simp only [List.getElem_cons_succ]
      exact induction_hypothesis (by simpa using h)

/-- The same for a big-endian string of known length `n`: bit `i` of the string is bit
`n - 1 - i` of the number, since big-endian counts positions the other way round. -/
lemma testBit_valueBE {bs : List Bool} {n i : Nat} (hn : bs.length = n) (h : i < n) :
    (valueBE bs).testBit (n - 1 - i) = bs[i]'(hn ▸ h) := by
  subst hn
  have hrev : bs.length - 1 - i < bs.reverse.length := by simp; omega
  have hidx : bs.length - 1 - (bs.length - 1 - i) = i := by omega
  -- `valueBE bs` is `valueLE bs.reverse`, so the bit is position `n - 1 - i` of the reverse.
  rw [valueBE, testBit_valueLE hrev]
  -- Indexing the reverse counts from the other end, which undoes the `n - 1 - ·`.
  simp [List.getElem_reverse, hidx]

/-- Every word is the encoding of the three numbers its own rows spell out. Together with
`encode_mem_B_iff` this makes the sanity check exhaustive: no word of `Σ₃*` escapes it. -/
theorem encode_rows (w : List Sigma3) :
    encode w.length (valueBE (row1 w)) (valueBE (row2 w)) (valueBE (row3 w)) = w := by
  -- Both sides have length `|w|`, so it is enough to compare them column by column.
  apply List.ext_getElem (by simp [encode])
  intro i _ hi
  -- Column `i` of the encoding holds bit `|w| - 1 - i` of each of the three numbers, because
  -- `encode` maps over `(List.range n).reverse`, whose `i`-th entry is `n - 1 - i`.
  simp only [encode, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range]
  -- Each of those bits is the `i`-th bit of the row it came from.
  rw [testBit_valueBE (by simp [row1]) hi, testBit_valueBE (by simp [row2]) hi,
    testBit_valueBE (by simp [row3]) hi]
  -- The three rows at position `i` are the three components of column `i`.
  simp [row1, row2, row3]

/-- Encoding `3 + 1 = 4` in 3 bits gives the first example's word. -/
example : encode 3 3 1 4 =
    [(false, false, true), (true, false, false), (true, true, false)] := by decide

/-- Encoding `1 + 0 ≟ 3` in 2 bits gives the second example's word. -/
example : encode 2 1 0 3 =
    [(false, false, true), (true, false, true)] := by decide

end TheoryOfComputation.Chapter1.Problem32
