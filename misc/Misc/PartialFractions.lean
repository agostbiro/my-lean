import Mathlib

namespace Misc.PartialFractions

open Polynomial

-- Partial fraction expansion means rewriting a fraction of polynomials as a sum of simpler
-- fractions. Example:
--
--     (3x + 1) / ((x - 1)(x - 2)) = A / (x - 1) + B / (x - 2)
--
-- where A and B are constants (plain numbers) to be found.
--
-- Setup. Let P(x) be the top polynomial (the numerator) and Q(x) the bottom polynomial (the
-- denominator). Suppose Q has degree n and factors into n distinct linear pieces:
--
--     Q(x) = (x - a₁)(x - a₂)⋯(x - aₙ)
--
-- where a₁, …, aₙ are distinct numbers. Assume the degree of P is less than n. The claim is that
-- constants A₁, …, Aₙ always exist with
--
--     P(x) / Q(x) = A₁ / (x - a₁) + A₂ / (x - a₂) + ⋯ + Aₙ / (x - aₙ).
--
-- The proof below follows the vector space argument: multiply out the denominators, observe that
-- the resulting polynomials Q₁, …, Qₙ are linearly independent in the n-dimensional space of
-- polynomials of degree less than n, and conclude that they span it. Mathlib has related material
-- (Lagrange interpolation, `Lagrange.basis`), so this is for educational purposes only.
--
-- Everything is done over an arbitrary field `K` (ℚ, ℝ, ℂ, …). The distinct numbers a₁, …, aₙ are
-- a function `a : Fin n → K` that is injective, which is the same as "distinct". `K[X]` is the
-- type of polynomials with coefficients in `K`, `X` is the variable and `C c` is the constant
-- polynomial `c`.

variable {K : Type*} [Field K] {n : ℕ}

/-- The denominator Q(x) = (x - a₁)(x - a₂)⋯(x - aₙ), as a product over all indices `i : Fin n`. -/
noncomputable def Q (a : Fin n → K) : K[X] := ∏ i, (X - C (a i))

/-- Qᵢ(x) is Q(x) with the factor (x - aᵢ) removed: the product over all indices except `i`. -/
noncomputable def Qi (a : Fin n → K) (i : Fin n) : K[X] := ∏ j ∈ Finset.univ.erase i, (X - C (a j))

-- Step 1: turn it into a polynomial equation.
--
-- Multiplying both sides of the claim by Q(x) turns each term Aᵢ / (x - aᵢ) on the right into
-- Aᵢ · Qᵢ(x), because Q(x) = (x - aᵢ) · Qᵢ(x). This lemma is that factorization. It is just
-- `Finset.mul_prod_erase`: pulling one factor out of a product over a finite set leaves the
-- product over the set with that element erased.
theorem Q_eq_mul_Qi (a : Fin n → K) (i : Fin n) : Q a = (X - C (a i)) * Qi a i :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

-- So the claim becomes the polynomial equation
--
--     P(x) = A₁ Q₁(x) + A₂ Q₂(x) + ⋯ + Aₙ Qₙ(x).
--
-- Each Qᵢ has degree n - 1, while P has degree at most n - 1. So the question is: can P be
-- written as a weighted sum of the Qᵢ's? In Lean the weighted sum is `∑ i, C (A i) * Qi a i`.
-- The rest of the file answers this question, then translates back to fractions at the end.

-- Two facts about evaluating the Qᵢ at the points aⱼ. They drive both the independence proof and
-- the formula for the coefficients.

-- Plugging x = aᵢ into Qⱼ with j ≠ i gives 0, because Qⱼ still contains the factor (x - aᵢ).
-- `eval_prod` evaluates a product factor by factor, and `Finset.prod_eq_zero` says a product is
-- zero as soon as one factor is (here the factor at index `i`, which is in `univ.erase j` since
-- `i ≠ j`).
theorem eval_Qi_of_ne (a : Fin n → K) {i j : Fin n} (h : j ≠ i) : (Qi a j).eval (a i) = 0 := by
  rw [Qi, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ i⟩) (by simp)

-- Plugging x = aᵢ into Qᵢ itself gives ∏_{j ≠ i} (aᵢ - aⱼ), which is nonzero because the aⱼ are
-- distinct. `Finset.prod_ne_zero_iff` reduces this to each factor being nonzero, and
-- `sub_ne_zero` plus injectivity of `a` handles a single factor.
theorem eval_Qi_self_ne_zero {a : Fin n → K} (ha : Function.Injective a) (i : Fin n) :
    (Qi a i).eval (a i) ≠ 0 := by
  rw [Qi, eval_prod, Finset.prod_ne_zero_iff]
  intro j hj
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact fun h => (Finset.mem_erase.mp hj).1 (ha h).symm

-- Step 2: why a weighted sum can reach P.
--
-- Think of polynomials of degree less than n as a vector space: a polynomial
-- c₀ + c₁x + ⋯ + cₙ₋₁xⁿ⁻¹ is the same thing as the list of n numbers (c₀, …, cₙ₋₁). Mathlib has
-- this space as the submodule `degreeLT K n` of `K[X]`, and the identification with lists of n
-- numbers as the linear equivalence `degreeLTEquiv K n : degreeLT K n ≃ₗ[K] (Fin n → K)`.
-- Linear equivalences preserve dimension (`finrank_eq`), and `Fin n → K` has dimension n
-- (`Module.finrank_fin_fun`), so `degreeLT K n` has dimension n.
theorem finrank_degreeLT : Module.finrank K (degreeLT K n) = n :=
  (degreeLTEquiv K n).finrank_eq.trans (Module.finrank_fin_fun K)

-- Having dimension n means any n linearly independent vectors in the space span it. That is
-- `LinearIndependent.span_eq_top_of_card_eq_finrank'` in Mathlib, used in the conclusion below.
-- It needs the space to be finite dimensional, which again follows from the equivalence with
-- `Fin n → K`.
instance : FiniteDimensional K (degreeLT K n) := (degreeLTEquiv K n).symm.finiteDimensional

-- Before we can place the Qᵢ in this space we need to know their degree is less than n.

-- Each Qᵢ is monic (leading coefficient 1), being a product of the monic polynomials x - aⱼ.
theorem Qi_monic (a : Fin n → K) (i : Fin n) : (Qi a i).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)

-- Each Qᵢ has degree n - 1: it is a product of n - 1 factors of degree 1. For monic polynomials
-- the degree of a product is the sum of the degrees (`natDegree_prod_of_monic`), each factor
-- contributes 1 (`natDegree_X_sub_C`), and `univ.erase i` has n - 1 elements
-- (`Finset.card_erase_of_mem`).
theorem natDegree_Qi (a : Fin n → K) (i : Fin n) : (Qi a i).natDegree = n - 1 := by
  rw [Qi, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)]
  simp [Finset.card_erase_of_mem]

-- Hence degree Qᵢ < n, i.e. Qᵢ lives in `degreeLT K n`. Here n ≥ 1 because there is an index
-- `i : Fin n`, so n - 1 < n. `degree` is the `natDegree` for nonzero polynomials (monic ones are
-- nonzero), and the comparison happens in `WithBot ℕ`, which is why there is a cast.
theorem degree_Qi_lt (a : Fin n → K) (i : Fin n) : (Qi a i).degree < n := by
  rw [degree_eq_natDegree (Qi_monic a i).ne_zero, natDegree_Qi, Nat.cast_lt]
  exact Nat.sub_one_lt fun h => Fin.elim0 (h ▸ i)

-- Step 3: the Qᵢ's are linearly independent.
--
-- "Linearly independent" means no weighted sum of them gives zero unless all weights are zero.
-- `Fintype.linearIndependent_iff` states exactly that for a finite family:
--     ∀ g, ∑ i, g i • Qi a i = 0 → ∀ i, g i = 0.
-- Suppose A₁Q₁(x) + ⋯ + AₙQₙ(x) = 0 for all x. Plug in x = aᵢ. Every Qⱼ with j ≠ i becomes 0
-- (`eval_Qi_of_ne`), so the sum collapses to Aᵢ · Qᵢ(aᵢ) (`Finset.sum_eq_single`). Since
-- Qᵢ(aᵢ) ≠ 0 (`eval_Qi_self_ne_zero`), this forces Aᵢ = 0.
theorem linearIndependent_Qi {a : Fin n → K} (ha : Function.Injective a) :
    LinearIndependent K (Qi a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- Evaluate the identity ∑ g j • Qⱼ = 0 at aᵢ. `congrArg` applies `eval (a i)` to both sides.
  have h := congrArg (eval (a i)) hg
  -- Push `eval` through the sum and the scalar multiplications, then collapse the sum.
  rw [eval_finsetSum, eval_zero, Finset.sum_eq_single i] at h
  · -- h : (g i • Qi a i).eval (a i) = 0, i.e. g i * Qi a i (a i) = 0, and the second factor
    -- is nonzero.
    rw [eval_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (eval_Qi_self_ne_zero ha i)
  · -- The other terms vanish.
    intro j _ hj
    rw [eval_smul, eval_Qi_of_ne a hj, smul_zero]
  · -- `i` is in `univ`, so this case is impossible.
    exact fun h => absurd (Finset.mem_univ i) h

-- Conclusion.
--
-- We have n independent polynomials in an n-dimensional space, so they span it. Every P of degree
-- less than n is some weighted sum of the Qᵢ's. Notice that P may have lower degree than the
-- Qᵢ's; that's fine because the weights can be chosen so the highest powers cancel. Nothing in the
-- argument needs the degree of P to be exactly n - 1.
theorem exists_eq_sum_Qi {a : Fin n → K} (ha : Function.Injective a) {P : K[X]}
    (hP : P.degree < n) : ∃ A : Fin n → K, P = ∑ i, C (A i) * Qi a i := by
  -- The Qᵢ as elements of the subspace `degreeLT K n` rather than of all of `K[X]`.
  let v : Fin n → degreeLT K n := fun i => ⟨Qi a i, mem_degreeLT.mpr (degree_Qi_lt a i)⟩
  -- They are still linearly independent there: the inclusion `(degreeLT K n).subtype` maps `v`
  -- to `Qi a`, and `LinearIndependent.of_comp` pulls independence back along a linear map.
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (degreeLT K n).subtype (linearIndependent_Qi ha)
  -- n independent vectors in a space of dimension n span it.
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_degreeLT])
  -- So P, viewed as an element of `degreeLT K n`, is in the span, and membership in the span of a
  -- finite family means being a weighted sum of it (`Submodule.mem_span_range_iff_exists_fun`).
  have hmem : (⟨P, mem_degreeLT.mpr hP⟩ : degreeLT K n) ∈ Submodule.span K (Set.range v) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨A, hA⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨A, ?_⟩
  -- `hA` is an equation in the subspace; take underlying polynomials on both sides, and turn
  -- the scalar multiplications `A i • Qi a i` into `C (A i) * Qi a i`.
  have := congrArg Subtype.val hA
  simp only [Submodule.coe_sum, Submodule.coe_smul, v, smul_eq_C_mul] at this
  exact this.symm

-- Translating back from the polynomial equation to fractions.
--
-- At any x that is not one of the aᵢ, Q(x) ≠ 0 so we can divide. This is the theorem as stated
-- at the top: the sum of fractions is an equation between values in `K`, and it holds wherever
-- both sides make sense.
theorem partial_fraction_expansion {a : Fin n → K} (ha : Function.Injective a) {P : K[X]}
    (hP : P.degree < n) :
    ∃ A : Fin n → K, ∀ x, (∀ i, x ≠ a i) → P.eval x / (Q a).eval x = ∑ i, A i / (x - a i) := by
  obtain ⟨A, hA⟩ := exists_eq_sum_Qi ha hP
  refine ⟨A, fun x hx => ?_⟩
  -- Q(x) = ∏ (x - aᵢ) is nonzero since every factor is.
  have hQ : (Q a).eval x ≠ 0 := by
    rw [Q, eval_prod, Finset.prod_ne_zero_iff]
    intro i _
    rw [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (hx i)
  -- Substitute P = ∑ Aᵢ Qᵢ, evaluate, and divide the sum term by term.
  rw [hA, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Term i: Aᵢ Qᵢ(x) / Q(x) = Aᵢ / (x - aᵢ), because Q(x) = (x - aᵢ) Qᵢ(x) and Qᵢ(x) ≠ 0 can be
  -- cancelled (`mul_div_mul_right`).
  have hQx : (Q a).eval x = (x - a i) * (Qi a i).eval x := by
    rw [Q_eq_mul_Qi a i, eval_mul, eval_sub, eval_X, eval_C]
  have hQi : (Qi a i).eval x ≠ 0 := fun h => hQ (by rw [hQx, h, mul_zero])
  rw [eval_C_mul, hQx, mul_div_mul_right _ _ hQi]

-- Bonus: finding the Aᵢ.
--
-- The same trick from Step 3 gives the values directly. Plug x = aᵢ into P(x) = ∑ Aⱼ Qⱼ(x) to get
-- P(aᵢ) = Aᵢ Qᵢ(aᵢ), so Aᵢ = P(aᵢ) / Qᵢ(aᵢ). This also shows the coefficients are unique: any two
-- families of coefficients that both work are given by the same formula.
theorem coeff_eq {a : Fin n → K} (ha : Function.Injective a) {P : K[X]} {A : Fin n → K}
    (hA : P = ∑ i, C (A i) * Qi a i) (i : Fin n) : A i = P.eval (a i) / (Qi a i).eval (a i) := by
  rw [eq_div_iff (eval_Qi_self_ne_zero ha i), hA, eval_finsetSum, Finset.sum_eq_single i]
  · rw [eval_C_mul]
  · intro j _ hj
    rw [eval_C_mul, eval_Qi_of_ne a hj, mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

theorem coeff_unique {a : Fin n → K} (ha : Function.Injective a) {P : K[X]} {A B : Fin n → K}
    (hA : P = ∑ i, C (A i) * Qi a i) (hB : P = ∑ i, C (B i) * Qi a i) : A = B :=
  funext fun i => (coeff_eq ha hA i).trans (coeff_eq ha hB i).symm

-- The example from the top, over ℚ: a₁ = 1, a₂ = 2 and P = 3x + 1. The formula gives
--     A = (3·1 + 1) / (1 - 2) = -4      and      B = (3·2 + 1) / (2 - 1) = 7.
-- With the points listed as `![1, 2] : Fin 2 → ℚ`, Q₁ = x - 2 and Q₂ = x - 1.
example : Qi (![1, 2] : Fin 2 → ℚ) 0 = X - C 2 := by
  rw [Qi, show Finset.univ.erase (0 : Fin 2) = {1} from by decide, Finset.prod_singleton]
  simp

-- The polynomial identity 3x + 1 = -4 (x - 2) + 7 (x - 1) ...
example : (3 * X + 1 : ℚ[X]) = C (-4) * (X - C 2) + C 7 * (X - C 1) := by
  simp only [map_neg, map_ofNat, map_one]
  ring

-- ... and the resulting expansion, valid away from x = 1 and x = 2.
example (x : ℚ) (h1 : x ≠ 1) (h2 : x ≠ 2) :
    (3 * x + 1) / ((x - 1) * (x - 2)) = -4 / (x - 1) + 7 / (x - 2) := by
  have h1' : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : x - 2 ≠ 0 := sub_ne_zero.mpr h2
  field_simp
  ring

-- If the degree of P is n or more: first divide P by Q with polynomial long division,
-- P = S · Q + R, where S is the quotient and R the remainder with degree less than n. Then
-- P / Q = S + R / Q, and R / Q expands as above.
--
-- In Mathlib, division by a monic polynomial is `/ₘ` (quotient) and `%ₘ` (remainder), with
-- `modByMonic_add_div : P %ₘ Q + Q * (P /ₘ Q) = P` and `degree_modByMonic_lt` bounding the
-- remainder by the degree of the divisor. Q is monic because each factor x - aᵢ is.

theorem Q_monic (a : Fin n → K) : (Q a).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)

-- Q has degree n: n monic factors of degree 1.
theorem degree_Q (a : Fin n → K) : (Q a).degree = n := by
  rw [degree_eq_natDegree (Q_monic a).ne_zero, Q,
    natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)]
  simp

theorem partial_fraction_expansion_of_degree_ge {a : Fin n → K} (ha : Function.Injective a)
    (P : K[X]) :
    ∃ S : K[X], ∃ A : Fin n → K, ∀ x, (∀ i, x ≠ a i) →
      P.eval x / (Q a).eval x = S.eval x + ∑ i, A i / (x - a i) := by
  -- The remainder has degree less than n, so the previous theorem applies to it.
  have hR : (P %ₘ Q a).degree < n := (degree_Q a) ▸ degree_modByMonic_lt P (Q_monic a)
  obtain ⟨A, hA⟩ := partial_fraction_expansion ha hR
  refine ⟨P /ₘ Q a, A, fun x hx => ?_⟩
  have hQ : (Q a).eval x ≠ 0 := by
    rw [Q, eval_prod, Finset.prod_ne_zero_iff]
    intro i _
    rw [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (hx i)
  -- Rewrite P as R + Q · S (only on the left, via `conv_lhs`), evaluate, and split the fraction:
  --     (R(x) + Q(x) S(x)) / Q(x) = R(x) / Q(x) + S(x).
  conv_lhs => rw [← modByMonic_add_div P (Q a)]
  rw [eval_add, eval_mul, add_div, mul_div_cancel_left₀ _ hQ, hA x hx, add_comm]

end Misc.PartialFractions
