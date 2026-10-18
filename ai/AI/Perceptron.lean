import Mathlib

/-!
# Perceptrons and XOR

A perceptron is a single threshold unit: it fires when an affine function of its input is
positive. XOR is not linearly separable, so no perceptron computes it. A two-layer network
of perceptrons does.
-/

open Matrix

/-- Embed a pair of booleans as a vector in `ℝ²`, mapping `false ↦ 0` and `true ↦ 1`. -/
def embed (a b : Bool) : Fin 2 → ℝ :=
  ![if a then 1 else 0, if b then 1 else 0]

/-- A perceptron with weights `w` and bias `c` fires when `0 < w ⬝ᵥ x + c`.
Noncomputable because `<` on `ℝ` is not decidable at runtime. -/
noncomputable def perceptron {n : ℕ} (w : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) : Bool :=
  decide (0 < w ⬝ᵥ x + c)

/-- XOR is not linearly separable: no affine function is positive exactly on the inputs
where XOR is true. -/
theorem xor_not_linearly_separable :
    ¬ ∃ (w : Fin 2 → ℝ) (c : ℝ), ∀ a b, xor a b = true ↔ 0 < w ⬝ᵥ embed a b + c := by
  rintro ⟨w, c, h⟩
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp [embed, dotProduct, Fin.sum_univ_two] at h00 h01 h10 h11
  linarith

/-- No perceptron computes XOR. -/
theorem perceptron_ne_xor :
    ¬ ∃ (w : Fin 2 → ℝ) (c : ℝ), ∀ a b, perceptron w c (embed a b) = xor a b := by
  rintro ⟨w, c, h⟩
  refine xor_not_linearly_separable ⟨w, c, fun a b => ?_⟩
  rw [← h a b, perceptron, decide_eq_true_iff]

/-- A two-layer network that computes XOR. The hidden layer has an OR unit and an AND unit;
the output unit fires when OR fires and AND does not. -/
noncomputable def xorNet (a b : Bool) : Bool :=
  let x := embed a b
  let orUnit  := perceptron ![1, 1] (-1/2) x
  let andUnit := perceptron ![1, 1] (-3/2) x
  perceptron ![1, -1] (-1/2) (embed orUnit andUnit)

theorem xorNet_eq_xor (a b : Bool) : xorNet a b = xor a b := by
  cases a <;> cases b <;> norm_num [xorNet, perceptron, embed, dotProduct, Fin.sum_univ_two]
