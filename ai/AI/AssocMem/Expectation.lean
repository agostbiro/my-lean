import AI.AssocMem.Algebra

/-!
# Outer-product memory: the expectation step

The main theorem for any key distribution with the moment facts (H1) and (H2).
This file does not need a probability measure, only integrability.
-/

open Matrix MeasureTheory

set_option autoImplicit false

namespace AssocMem

variable {M d dv : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The moment facts (H1) and (H2) in one field, plus integrability. -/
structure KeyMoments (K : Ω → Matrix (Fin M) (Fin d) ℝ) : Prop where
  /-- (H1) and (H2): the mean of a product of two key overlaps with `K ω j`. -/
  pair : ∀ i l j, i ≠ j → l ≠ j →
    ∫ ω, (K ω i ⬝ᵥ K ω j) * (K ω l ⬝ᵥ K ω j) ∂μ
      = if i = l then 1 / (d : ℝ) else 0
  /-- Each product of two key overlaps is integrable. -/
  integrable : ∀ i l j,
    Integrable (fun ω => (K ω i ⬝ᵥ K ω j) * (K ω l ⬝ᵥ K ω j)) μ

/-- Helper. Statement: The integral of a double sum of pair terms is `1 / d` times the sum of
the diagonal weights `c i i`.

Concepts:
- The integral of a finite sum is the sum of the integrals, if each term is integrable.
- A constant factor comes out of the integral.
- The moment facts (H1) and (H2) give the integral of each pair term.
- In a sum of `if i = l then b l else 0` over `l`, only the term `l = i` stays.

Plan:
1. Move the integral inside the two sums, and move each constant `c i l` out.
2. Factor `1 / d` into the outer sum, and compare the sums term by term.
3. Replace each pair integral with its value from (H1) and (H2).
4. Keep only the diagonal term `l = i`.
-/
theorem integral_pair_sum (K : Ω → Matrix (Fin M) (Fin d) ℝ) (hK : KeyMoments μ K)
    (j : Fin M) (s : Finset (Fin M)) (hs : j ∉ s) (c : Fin M → Fin M → ℝ) :
    ∫ ω, ∑ i ∈ s, ∑ l ∈ s, (K ω i ⬝ᵥ K ω j) * (K ω l ⬝ᵥ K ω j) * c i l ∂μ
      = (1 / (d : ℝ)) * ∑ i ∈ s, c i i := by
  -- Plan 1: move the integral inside the sums
  rw [MeasureTheory.integral_finsetSum s fun i _ =>
    MeasureTheory.integrable_finsetSum s fun l _ => (hK.integrable i l j).mul_const (c i l)]
  simp only [MeasureTheory.integral_finsetSum s fun l _ => (hK.integrable _ l j).mul_const _,
    MeasureTheory.integral_mul_const]
  -- Plan 2: compare the outer sums term by term
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Plan 3: use (H1) and (H2)
  rw [Finset.sum_congr rfl fun l hl =>
    by rw [hK.pair i l j (ne_of_mem_of_not_mem hi hs) (ne_of_mem_of_not_mem hl hs)]]
  -- Plan 4: keep the diagonal term
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, if_pos hi]

/-- Statement: The mean squared length of the interference is `1 / d` times the sum of
`sqLen (V i)` over the other memories. -/
theorem expected_interference (K : Ω → Matrix (Fin M) (Fin d) ℝ)
    (hK : KeyMoments μ K) (V : Matrix (Fin M) (Fin dv) ℝ) (j : Fin M) :
    ∫ ω, sqLen (interference (K ω) V j) ∂μ
      = (1 / (d : ℝ)) * ∑ i ∈ Finset.univ.erase j, sqLen (V i) := by
  simp only [interference, sqLen_sum_smul]
  rw [integral_pair_sum μ K hK j _ (Finset.notMem_erase j _)]
  simp only [sqLen]

end AssocMem
