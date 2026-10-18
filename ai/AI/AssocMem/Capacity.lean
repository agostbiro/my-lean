import AI.AssocMem.Signs

/-!
# Outer-product memory: capacity

The main theorem and the capacity corollary for random-sign keys.
-/

open Matrix MeasureTheory

set_option autoImplicit false

namespace AssocMem

variable {M d dv : ℕ}

/-- Statement: For random-sign keys, the mean squared recall error of memory `j` is `1 / d`
times the sum of `sqLen (V i)` over the other memories.

Concepts:
- A key has squared length 1, so its recall is its value plus the interference.
- The moment facts (H1) and (H2) give the mean squared length of the interference.

Plan:
1. Show that the recall error is the interference, for each sign pattern.
2. Replace the recall error with the interference under the integral.
3. Use the expectation step with the moment facts of random-sign keys.
-/
theorem main (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      = (1 / (d : ℝ)) * ∑ i ∈ Finset.univ.erase j, sqLen (V i) := by
  -- Plan 1: the recall error is the interference
  have h : ∀ ω : Signs M d,
      retrieve (signKeys ω) V (signKeys ω j) - V j = interference (signKeys ω) V j := by
    intro ω
    rw [retrieve_split _ _ _ (sqLen_signKeys _ _ hd), add_sub_cancel_left]
  -- Plan 2: rewrite under the integral
  simp only [h]
  -- Plan 3: use the expectation step
  exact expected_interference _ _ (signKeys_moments hd) V j

/-- Statement: If each value has squared length 1, then the mean squared recall error is
`(M - 1) / d`. -/
theorem main_unit (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ)
    (hV : ∀ i, sqLen (V i) = 1) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      = ((M : ℝ) - 1) / d := by
  rw [main hd V j]
  simp only [hV, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    Nat.cast_pred (Fin.pos j)]
  rw [one_div, inv_mul_eq_div]

/-- Helper. Statement: `(M - 1) / d ≤ 1` if and only if `M ≤ d + 1`. -/
theorem div_le_one_iff_le_succ (hd : 0 < d) :
    ((M : ℝ) - 1) / d ≤ 1 ↔ M ≤ d + 1 := by
  rw [div_le_one (Nat.cast_pos.mpr hd), sub_le_iff_le_add, ← Nat.cast_add_one, Nat.cast_le]

/-- Statement: The capacity. The mean-square interference is not more than the signal
if and only if `M ≤ d + 1`. -/
theorem capacity (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ)
    (hV : ∀ i, sqLen (V i) = 1) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      ≤ sqLen (V j) ↔ M ≤ d + 1 := by
  rw [main_unit hd V hV j, hV j]
  exact div_le_one_iff_le_succ hd

end AssocMem
