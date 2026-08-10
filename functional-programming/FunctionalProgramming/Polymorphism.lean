import Batteries

namespace FunctionalProgramming

-- Solutions to exercises from
-- https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Polymorphism

/-- 1. Write a function to find the last entry in a list. It should return an Option. -/
def myLast? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _head :: xs => myLast? xs

/-- Spec: `myLast?` agrees with the standard library's `List.getLast?`. -/
theorem myLast?_eq_getLast? (xs : List α) : myLast? xs = xs.getLast? := by
  -- Use the induction principle Lean generated from `myLast?`'s own match, so the
  -- proof cases line up one-to-one with the function's three branches.
  -- The proof is a bit verbose for educational reasons.
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

/-- 2. Write a function that finds the first entry in a list that satisfies a
given predicate. Start the definition with def List.findFirst? {α : Type}
(xs : List α) (predicate : α → Bool) : Option α := …. -/
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | head :: tail => if predicate head then some head else List.findFirst? tail predicate

/-- Spec: `List.findFirst?` agrees with the standard library's `List.find?`. -/
theorem findFirst?_eq_find? (xs : List a) (predicate : a → Bool) :
    List.findFirst? xs predicate = xs.find? predicate := by
  induction xs using List.findFirst?.induct predicate with
  | case1 => rfl
  | case2 head tail head_matches => simp [List.findFirst?, List.find?, head_matches]
  | case3 head tail head_doesnt_match induction_hypothesis =>
    simp [List.findFirst?, List.find?, head_doesnt_match, induction_hypothesis]

/-- Write a function Prod.switch that switches the two fields in a pair for each
other. Start the definition with def Prod.switch {α β : Type} (pair : α × β) :
β × α := …. -/
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

theorem switch_eq_swap {α β : Type} (pair : α × β) : Prod.switch pair = pair.swap := rfl

/-- Using the analogy between types and arithmetic, write a function that
distributes products over sums. In other words, it should have type
α × (β ⊕ γ) → (α × β) ⊕ (α × γ). -/
def distributeProduct {α β γ : Type} (input : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match input with
  | Prod.mk a (Sum.inl b) => Sum.inl (Prod.mk a b)
  | Prod.mk a (Sum.inr c) => Sum.inr (Prod.mk a c)

/-- The inverse of `distributeProduct`, used to show the two types hold the same
information. -/
def undistributeProduct {α β γ : Type} : (α × β) ⊕ (α × γ) → α × (β ⊕ γ)
  | Sum.inl (a, (b : β)) => (a, Sum.inl b)
  | Sum.inr (a, (c : γ)) => (a, Sum.inr c)

/-- Verify `distributeProduct` by proving that it's the inverse of `undistributeProduct`. -/
theorem undistribute_distribute {α β γ : Type} (input : α × (β ⊕ γ)) :
    undistributeProduct (distributeProduct input) = input := by
  match input with
  | (_, Sum.inl _) => rfl
  | (_, Sum.inr _) => rfl

/-- Verify `undistributeProduct` by proving that it's the inverse of `distributeProduct`. -/
theorem distribute_undistribute {α β γ : Type} (input : (α × β) ⊕ (α × γ)) :
    distributeProduct (undistributeProduct input) = input := by
  match input with
  | Sum.inl (_, _) => rfl
  | Sum.inr (_, _) => rfl

/-- Whichever side of the sum we end up on, the first component is carried over
unchanged. -/
theorem distribute_fst {α β γ : Type} (input : α × (β ⊕ γ)) :
    (distributeProduct input).elim Prod.fst Prod.fst = input.fst := by
  match input with
  | (_, Sum.inl _) => rfl
  | (_, Sum.inr _) => rfl

end FunctionalProgramming
