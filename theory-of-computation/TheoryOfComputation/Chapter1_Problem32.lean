import TheoryOfComputation.Chapter1_Problem32.Specification
import TheoryOfComputation.Chapter1_Problem32.Implementation
import TheoryOfComputation.Chapter1_Problem32.Proof

/-!
# Problem 1.32

The solution is split into three files:

* `Specification.lean` — the problem statement: the alphabet `Σ₃`, the language
  `B`, and a sanity check that `B` matches an independent second translation of
  the statement;
* `Implementation.lean` — the adder DFA that recognizes `B.reverse`;
* `Proof.lean` — the proof that the DFA is correct and that `B` is regular.
-/
