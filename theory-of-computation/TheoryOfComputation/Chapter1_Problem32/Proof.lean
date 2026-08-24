import TheoryOfComputation.Chapter1_Problem32.Implementation

namespace TheoryOfComputation.Chapter1.Problem32

/-!
# Problem 1.32 — Proof

The language `B` is specified in `Specification.lean` and the adder DFA is built
in `Implementation.lean`. This file proves that the DFA recognizes `B.reverse`
(`adderDFA_accepts`), and concludes that `B` is regular (`B_isRegular`).

The proof works in the `valueLE` (least significant bit first) convention the
automaton consumes columns in. Unfolding `valueBE` converts to the `B` side's
most significant bit first convention, once, in `adderDFA_accepts`.
-/

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
lemma evalFrom_dead (w : List Sigma3) : adderDFA.evalFrom .dead w = .dead := by
  induction w with
  | nil => rfl
  | cons column columns induction_hypothesis =>
    simpa [DFA.evalFrom, adderDFA, dfaStep] using induction_hypothesis

/-- A run over a nonempty word ends in a carry state exactly when its first
column produces an intermediate carry and the rest of the run produces the
final carry. -/
lemma evalFrom_cons_carry_iff (x y z carryIn carryOut : Bool) (w : List Sigma3) :
    adderDFA.evalFrom (.carry carryIn) ((x, y, z) :: w) = .carry carryOut ↔
      ∃ carryMid, dfaStep (.carry carryIn) (x, y, z) = .carry carryMid ∧
        adderDFA.evalFrom (.carry carryMid) w = .carry carryOut := by
  change adderDFA.evalFrom (dfaStep (.carry carryIn) (x, y, z)) w = .carry carryOut ↔ _
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

/-- Running the adder DFA over a little-endian word `wLE` from carry
  `carryIn` lands in state carry `carryOut` when the equation holds:
  `row1 + row2 + carryIn = row3 + carryOut · 2^|wLE|`.
-/
lemma evalFrom_carry_iff (wLE : List Sigma3) (carryIn carryOut : Bool) :
    adderDFA.evalFrom (.carry carryIn) wLE = .carry carryOut ↔
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
theorem adderDFA_accepts : adderDFA.accepts = B.reverse := by
  -- Change the goal from "these two languages are the same" to "for an arbitrary word, the DFA accepts it iff it's in B.reverse".
  ext wLE
  -- `evalFrom_carry_iff` states that running the adder DFA over a little-endian word `wLE` from carry
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
      wLE ∈ adderDFA.accepts ↔ adderDFA.evalFrom (.carry false) wLE = .carry false := Iff.rfl
  -- Remember, the goal is `wLE ∈ adderDFA.accepts ↔ wLE ∈ B.reverse`. We need to show that both sides are equal.
  rw [
    -- First we massage the left side.
    -- Replace `wLE ∈ adderDFA.accepts` with `adderDFA.evalFrom (.carry false) wLE = .carry false`
    mem_accepts_iff,
    -- Replace `adderDFA.evalFrom (.carry false) wLE = .carry false` with 
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

/-- Corollary: `B^R` is regular since `adderDFA` is a DFA with finitely many states that recognizes it. -/
theorem B_reverse_isRegular : B.reverse.IsRegular :=
  ⟨DfaState, inferInstance, adderDFA, adderDFA_accepts⟩

/-- Hence `B` itself is regular, by closure of the regular languages under reversal. -/
theorem B_isRegular : B.IsRegular :=
  Language.isRegular_reverse_iff.mp B_reverse_isRegular

end TheoryOfComputation.Chapter1.Problem32
