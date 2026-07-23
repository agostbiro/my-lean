import Batteries

namespace FunctionalProgramming

/-- Solutions to exercises from https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Polymorphism -/

def myLast? {α: Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _head :: xs => myLast? xs

#eval myLast? (α := Nat) []
#eval myLast? (α := Nat) [1]
#eval myLast? (α := Nat) [1, 2]
#eval myLast? (α := Nat) [1, 2, 3]

/-- Spec: `myLast?` agrees with the standard library's `List.getLast?`. -/
theorem myLast?_eq_getLast? (xs : List α) : myLast? xs = xs.getLast? := by
  -- Use the induction principle Lean generated from `myLast?`'s own match, so the
  -- proof cases line up one-to-one with the function's three branches.
  -- The proof is a bit verbose for educationa lreasons.
  induction xs using myLast?.induct with
  | case1 => rfl
  | case2 x => rfl
  -- Induction hypothesis `myLast? xs = xs.getLast?`.
  | case3 head xs xs_not_empty induction_hypothesis =>
    -- Turn `xs ≠ []` into a concrete shape.
    obtain ⟨z, zs, xs_eq⟩ := List.exists_cons_of_ne_nil (by simpa using xs_not_empty)
    -- Substitute `z :: zs` for `xs` in the induction hypothesis.
    -- Goal is `head :: z :: zs` after this which lets us disambiguate case 3 from case 2.
    subst xs_eq
    -- LHS: `myLast?` on a 2+ list drops the head by computation. 
    rw [show myLast? (head :: z :: zs) = myLast? (z :: zs) from rfl]
    -- RHS: `getLast?` also ignores the head on a 2+ list. 
    -- We can use the library lemma `(a :: b :: l).getLast? = (b :: l).getLast?` for this.
    rw [List.getLast?_cons_cons]
    exact induction_hypothesis

end FunctionalProgramming

