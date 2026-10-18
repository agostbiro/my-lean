import AI.AssocMem.Defs

/-!
# Outer-product memory: exact algebra

The algebra of the store. This file uses no probability.
-/

open Matrix

set_option autoImplicit false

namespace AssocMem

variable {M d dv : ℕ} (K : Matrix (Fin M) (Fin d) ℝ) (V : Matrix (Fin M) (Fin dv) ℝ)

/-- Statement: The recall of `x` is the sum of the values `V i`, each scaled by `K i ⬝ᵥ x`. -/
theorem retrieve_eq_sum (x : Fin d → ℝ) :
    retrieve K V x = ∑ i, (K i ⬝ᵥ x) • V i := by
  rw [retrieve, store, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  simp only [Matrix.mulVec]

/-- Statement: The recall of a unit key `K j` is the value `V j` plus the interference. -/
theorem retrieve_split (j : Fin M) (hj : sqLen (K j) = 1) :
    retrieve K V (K j) = V j + interference K V j := by
  rw [sqLen] at hj
  rw [retrieve_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, one_smul, interference]

/-- Statement: If the other keys are orthogonal to `K j`, then the interference is 0.

Concepts:
- The interference is a sum over all memories other than `j`.
- A sum is 0 if each term is 0.

Plan:
1. Unfold the interference into its sum.
2. Show that each term is 0, because its dot product is 0.
-/
theorem interference_eq_zero_of_orthogonal (j : Fin M)
    (h : ∀ i, i ≠ j → K i ⬝ᵥ K j = 0) :
    interference K V j = 0 := by
  -- Plan 1: unfold the interference
  rw [interference]
  -- Plan 2: each term is 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [h i (Finset.ne_of_mem_erase hi), zero_smul]

/-- Statement: To store one more memory, add the outer product `v kᵀ`. -/
theorem store_cons (k : Fin d → ℝ) (v : Fin dv → ℝ) :
    store (Matrix.of (Matrix.vecCons k K)) (Matrix.of (Matrix.vecCons v V))
      = Matrix.vecMulVec v k + store K V := by
  ext b a
  simp only [store, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.vecMulVec_apply]

/-- Statement: A gradient step on `y = W x` adds the outer product `(-η yBar) xᵀ`.

The gradient formula `∇_W L = yBar xᵀ` is an assumption. This theorem does not prove it.
The theorem only shows that the step `W - η ∇_W L` is a write to the store. -/
theorem gradient_step_eq_write (W : Matrix (Fin dv) (Fin d) ℝ)
    (η : ℝ) (yBar : Fin dv → ℝ) (x : Fin d → ℝ) :
    W - η • Matrix.vecMulVec yBar x = W + Matrix.vecMulVec (-η • yBar) x := by
  rw [Matrix.smul_vecMulVec, neg_smul, sub_eq_add_neg]

/-- Statement: The squared length of a weighted sum of values is a double sum of dot products. -/
theorem sqLen_sum_smul (s : Finset (Fin M)) (c : Fin M → ℝ) :
    sqLen (∑ i ∈ s, c i • V i) = ∑ i ∈ s, ∑ l ∈ s, c i * c l * (V i ⬝ᵥ V l) := by
  rw [sqLen, sum_dotProduct]
  simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_assoc,
    mul_left_comm]

end AssocMem
