import TheoryOfComputation.Chapter1_Problem32.Implementation

namespace TheoryOfComputation.Chapter1.Problem32

/-!
# Problem 1.32 — Proof

The language `B` is specified in `Specification.lean` and the adder DFA is built
in `Implementation.lean`. This file proves that the DFA recognizes `B.reverse`
(`adderDFA_accepts_B_reverse`), and concludes that `B` is regular (`B_isRegular`).

The proof works in the `rowNLE` (least significant bit first) convention the
automaton consumes columns in. The `rowNBE_reverse` lemmas convert to the `B`
side's most significant bit first convention, once, in `adderDFA_accepts_B_reverse`.
-/

/-- One column is a correct carry step: the step from carry `carryIn` lands in carry
`carryOut` exactly when `x + y + carryIn = z + 2 · carryOut`, the adder equation for a
single column. -/
lemma first_step_adds (x y z carryIn carryOut : Bool) :
    dfaStep (.carry carryIn) (x, y, z) = .carry carryOut ↔
      x.toNat + y.toNat + carryIn.toNat = z.toNat + 2 * carryOut.toNat := by
  -- The statement is a closed formula over five booleans once the variables are moved back into
  -- the goal, so `decide` can check all 32 rows of the truth table.
  revert x y z carryIn carryOut
  decide

/-- The step function of `adderDFA` is `dfaStep`. Lets `simp` replace `adderDFA.step` with
`dfaStep` without unfolding the whole `adderDFA` structure. -/
@[simp]
lemma adderDFA_step : adderDFA.step = dfaStep := rfl

/-- `dead` is a sink: once a column has contradicted the addition, no suffix recovers.

`run_invariant` peels the leading column, which is the run's first step, so the case
where that step dies leaves a whole run still to evaluate. This lemma evaluates it. -/
lemma dead_state_is_sink (w : List Sigma3) : adderDFA.evalFrom .dead w = .dead := by
  induction w with
  | nil => rfl
  | cons column columns induction_hypothesis =>
    simpa [DFA.evalFrom, adderDFA, dfaStep] using induction_hypothesis

/-- Running the adder DFA over the little-endian word `wLE` from carry `carryIn` ends in
carry `carryOut`. -/
def RunEndsWithCarry (carryIn : Bool) (wLE : List Sigma3) (carryOut : Bool) : Prop :=
  adderDFA.evalFrom (.carry carryIn) wLE = .carry carryOut

/-- A run over a nonempty word ends in a carry state exactly when its first
column produces an intermediate carry and the rest of the run produces the
final carry. -/
lemma split_run (column : Sigma3) (columnsLE : List Sigma3) (carryIn carryOut : Bool) :
    RunEndsWithCarry carryIn (column :: columnsLE) carryOut ↔
      ∃ carryMid,
        dfaStep (.carry carryIn) column = .carry carryMid ∧
        RunEndsWithCarry carryMid columnsLE carryOut := by
  -- Unfold the run and peel off its first step, so that `cases` below can split on that step.
  simp only [RunEndsWithCarry, DFA.evalFrom_cons, adderDFA_step]
  cases dfaStep (.carry carryIn) column with
  | dead =>
    rw [dead_state_is_sink]
    simp
  | carry c =>
    simp only [DFAState.carry.injEq, exists_eq_left']

/-- The binary addition equation as a whole: the rows have least significant bits `x`, `y`
and `z`, their remaining higher bits have values `a`, `b` and `d`, carry `carryIn` enters at
the low end and `k` stands for the carry out term. -/
def WholeRunAddition (x y z carryIn : Bool) (a b d k : Nat) : Prop :=
  (x.toNat + 2 * a) + (y.toNat + 2 * b) + carryIn.toNat
    = (z.toNat + 2 * d) + 2 * k

/-- The binary addition equation split in two: the adder equation for the least significant
bits `x`, `y` and `z`, and the addition equation for the remaining higher bits with values
`a`, `b` and `d`, connected by an intermediate carry. -/
def SplitRunAddition (x y z carryIn : Bool) (a b d k : Nat) : Prop :=
  ∃ carryMid : Bool,
    x.toNat + y.toNat + carryIn.toNat = z.toNat + 2 * carryMid.toNat ∧
    a + b + carryMid.toNat = d + k

/-- A binary addition equation splits into the equation for its least significant bit and
the equation for the remaining higher bits, connected by an intermediate
carry.

This iff also covers the dead-column case of the induction for free: every term other
than the least significant bits is even, so when the least significant bit has the wrong
parity no `carryMid` satisfies the right-hand side — matching the run entering `dead` on the
left. -/
lemma least_significant_bit_split (x y z carryIn : Bool) (a b d k : Nat) :
    WholeRunAddition x y z carryIn a b d k ↔
      SplitRunAddition x y z carryIn a b d k := by
  cases x <;> cases y <;> cases z <;> cases carryIn <;>
  simp [WholeRunAddition, SplitRunAddition] <;>
  omega

/-- The little-endian word `wLE` is a correct binary addition with carry `carryIn`
entering at the low end and carry `carryOut` leaving at the high end:
`row1 + row2 + carryIn = row3 + carryOut · 2^|wLE|`. -/
def WordAddsWithCarry (carryIn : Bool) (wLE : List Sigma3) (carryOut : Bool) : Prop :=
  row1LE wLE + row2LE wLE + carryIn.toNat
    = row3LE wLE + carryOut.toNat * 2 ^ wLE.length

/-- Running the adder DFA over a little-endian word `wLE` from carry
  `carryIn` lands in state carry `carryOut` when `wLE` adds up with those carries.
-/
lemma run_invariant (wLE : List Sigma3) (carryIn carryOut : Bool) :
    RunEndsWithCarry carryIn wLE carryOut ↔
      WordAddsWithCarry carryIn wLE carryOut := by
  induction wLE generalizing carryIn with
  | nil =>
    -- Over the empty word both sides reduce to `carryIn = carryOut`. After unfolding the two
    -- `Prop` definitions the statement is a closed formula over two booleans, so `decide` checks it.
    unfold RunEndsWithCarry WordAddsWithCarry
    revert carryIn carryOut
    decide
  | cons column columnsLE induction_hypothesis =>
    obtain ⟨x, y, z⟩ := column
    -- 1. On the DFA side, split the run into its first step and the run over the remaining
    --    columns and join them with an intermediate carry.
    rw [split_run]
    simp_rw [
      -- 2. Turn the first step of the DFA into arithmetic. This is the adder equation for a
      --    single column.
      first_step_adds,
      -- 3. Turn the run over the remaining columns into arithmetic using the induction
      --    hypothesis.
      induction_hypothesis
    ]
    -- 4. On the arithmetic side, show that the equation for the whole word splits into the
    --    equation for the least significant bit and the equation for the remaining bits.
    simp only [WordAddsWithCarry, row1LE_cons, row2LE_cons, row3LE_cons, List.length_cons, pow_succ']
    -- This is `least_significant_bit_split` with `k := carryOut.toNat * 2 ^ |columnsLE|`,
    -- but the two sides write the same number differently: the goal has
    -- `carryOut.toNat * (2 * 2 ^ n)` (from `pow_succ'`), the lemma has
    -- `2 * (carryOut.toNat * 2 ^ n)`. `Nat.mul_left_comm` rewrites the first into the second.
    -- `omega` can't finish instead: it doesn't handle the `∃ carryMid`.
    rw [Nat.mul_left_comm]
    exact
      Iff.symm
        (least_significant_bit_split
          x y z carryIn
          (row1LE columnsLE)
          (row2LE columnsLE)
          (row3LE columnsLE)
          (carryOut.toNat * 2 ^ columnsLE.length))

/-- The DFA recognizes the reverse of `B`

`B.reverse = { w | w.reverse ∈ B }` -/
theorem adderDFA_accepts_B_reverse : adderDFA.accepts = B.reverse := by
  -- Change the goal from "these two languages are the same" to "for an arbitrary word, the DFA accepts it iff it's in B.reverse".
  ext wLE
  -- `run_invariant` states that `RunEndsWithCarry carryIn wLE carryOut`, i.e. running the adder DFA over
  -- a little-endian word `wLE` from carry `carryIn` lands in state carry `carryOut`, holds exactly
  -- when `WordAddsWithCarry carryIn wLE carryOut` holds, i.e.
  -- `row1 + row2 + carryIn = row3 + carryOut · 2^|wLE|`.
  -- Since we initialize it with `false, false`, the  invariant is "no carry in
  -- at the low end, no carry out at the high end".
  have invariant := run_invariant wLE false false
  -- Unfold `WordAddsWithCarry` and, since the carries are zero, cancel the terms involving them from
  -- the invariant's equation which becomes `row1 + row2 = row3`.
  simp only [WordAddsWithCarry, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at invariant
  -- Acceptance is by definition "the run from the start state ends in `carry false`".
  have mem_accepts_iff : wLE ∈ adderDFA.accepts ↔ RunEndsWithCarry false wLE false := Iff.rfl
  -- Remember, the goal is `wLE ∈ adderDFA.accepts ↔ wLE ∈ B.reverse`. We need to show that both sides are equal.
  rw [
    -- First we massage the left side.
    -- Replace `wLE ∈ adderDFA.accepts` with `RunEndsWithCarry false wLE false`
    mem_accepts_iff,
    -- Replace `RunEndsWithCarry false wLE false` with
    -- `row1LE wLE + row2LE wLE = row3LE wLE`
    invariant,

    -- Then massage the right side.
    -- `B.reverse` is defined as `{ w | w.reverse ∈ B }`.
    -- Replace `wLE ∈ B.reverse` with `wLE.reverse ∈ B`.
    Language.mem_reverse,
    -- Following the exercise, we defined the `B` language as:
    -- `wBE ∈ B ↔ row3BE wBE = row1BE wBE + row2BE wBE`.
    -- Applying this definition lets us replace `wLE.reverse ∈ B` with
    -- `row3BE wLE.reverse = row1BE wLE.reverse + row2BE wLE.reverse`
    mem_B_iff
  ]
  -- We have almost met the goal now, except the right side of the equation has `rowBE wLE.reverse` instead of `rowLE wLE`.
  simp only [
    -- Reading a row of the reversed word most significant bit first is reading the row of the
    -- original word least significant bit first. Both sides now read the same three rows the
    -- same way:
    -- `row1LE wLE + row2LE wLE = row3LE wLE ↔ row3LE wLE = row1LE wLE + row2LE wLE`.
    row1BE_reverse,
    row2BE_reverse,
    row3BE_reverse,
    -- All that is left is the direction of the equation: `B` puts the sum on the right, the
    -- automaton's invariant on the left. Flipping one of them leaves `X ↔ X`, which closes the goal.
    eq_comm
  ]

/-- Corollary: `B^R` is regular since `adderDFA` is a DFA with finitely many states that recognizes it. -/
theorem B_reverse_isRegular : B.reverse.IsRegular :=
  -- `inferInstance` asks typeclass resolution for the required `Fintype DFAState` proof,
  -- which finds the instance generated by `deriving Fintype` on `DFAState`.
  ⟨DFAState, inferInstance, adderDFA, adderDFA_accepts_B_reverse⟩

/-- Hence `B` itself is regular, by closure of the regular languages under reversal. -/
theorem B_isRegular : B.IsRegular :=
  Language.isRegular_reverse_iff.mp B_reverse_isRegular

end TheoryOfComputation.Chapter1.Problem32
