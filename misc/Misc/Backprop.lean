import Mathlib

open InnerProductSpace Matrix WithLp

/-- Vectors of dimension `n` with the Euclidean inner product.

`EuclideanSpace ℝ (Fin n)` is `WithLp 2 (Fin n → ℝ)`: a copy of the type `Fin n → ℝ` that
carries the Euclidean (L2) norm instead of the default sup norm. `ofLp` unwraps a `Vec n` into a
plain `Fin n → ℝ` and `toLp 2` wraps one back up. Both are the identity at runtime; they only
tell Lean which norm to use. Matrix operations like `W *ᵥ v` work on plain functions, while
`HasGradientAt` and the inner product need the `Vec n` type, so the code below converts between
the two with `ofLp` and `toLp 2`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The continuous linear map `v ↦ J *ᵥ v` on `Vec n`. Only used inside proofs. -/
noncomputable def Matrix.toVecCLM {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Vec n →L[ℝ] Vec n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin J)

theorem Matrix.toVecCLM_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) :
    J.toVecCLM v = toLp 2 (J *ᵥ ofLp v) := rfl

/-- A layer: a function, its Jacobian matrix at every point, and a proof they match.
Simplification: every layer maps `Vec n → Vec n` (same dimension in and out). -/
structure Layer (n : ℕ) where
  /-- The function the layer computes. -/
  f  : Vec n → Vec n
  /-- The Jacobian matrix of `f` at each point. -/
  J  : Vec n → Matrix (Fin n) (Fin n) ℝ
  /-- Proof that `J x` is the derivative of `f` at `x`. -/
  hf : ∀ x, HasFDerivAt f (J x).toVecCLM x

variable {n : ℕ}

/-- Forward pass. The head of the list is applied first. -/
def forward : List (Layer n) → Vec n → Vec n
  | [],      x => x
  | l :: ls, x => forward ls (l.f x)

/-- Backward pass. `g` is the gradient of the loss at the output.
Returns the gradient at the input `x`.
Each step multiplies by the transpose of the layer's Jacobian. -/
def backward : List (Layer n) → Vec n → Vec n → Vec n
  | [],      _, g => g
  | l :: ls, x, g => toLp 2 ((l.J x)ᵀ *ᵥ ofLp (backward ls (l.f x) g))

/-- One backprop step: the chain rule, written with gradients and transposes. -/
theorem HasGradientAt.comp_transpose {φ : Vec n → ℝ} {f : Vec n → Vec n}
    {J : Matrix (Fin n) (Fin n) ℝ} {g x : Vec n}
    (hφ : HasGradientAt φ g (f x)) (hf : HasFDerivAt f J.toVecCLM x) :
    HasGradientAt (φ ∘ f) (toLp 2 (Jᵀ *ᵥ ofLp g)) x := by
  have h := hφ.hasFDerivAt.comp x hf
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  ext v
  -- goal: ⟪g, J *ᵥ v⟫ = ⟪Jᵀ *ᵥ g, v⟫
  simp only [ContinuousLinearMap.comp_apply, toDual_apply_apply, Matrix.toVecCLM_apply,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.mulVec_transpose]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- Backprop is correct: `backward` computes the gradient of `L ∘ forward ls`. -/
theorem backward_correct (L : Vec n → ℝ) (ls : List (Layer n)) (x g : Vec n)
    (hL : HasGradientAt L g (forward ls x)) :
    HasGradientAt (L ∘ forward ls) (backward ls x g) x := by
  induction ls generalizing x with
  | nil => simpa [forward, backward, Function.comp_def] using hL
  | cons l ls ih =>
    -- gradient of the rest of the network, at the output of layer `l`
    have h := ih (l.f x) hL
    -- one more chain rule step through `l`
    exact h.comp_transpose (l.hf x)

/-! ## Examples -/

/-- An affine layer `x ↦ W x + b`. Its Jacobian is `W` at every point. -/
def Layer.affine (W : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : Layer n where
  f x := toLp 2 (W *ᵥ ofLp x) + b
  J _ := W
  hf _ := W.toVecCLM.hasFDerivAt.add_const b

/-- Squared-error loss against a target `t`, written as a dot product so it stays computable. -/
def sqLoss (t y : Vec n) : ℝ := ofLp (y - t) ⬝ᵥ ofLp (y - t)

theorem sqLoss_eq_norm_sq (t y : Vec n) : sqLoss t y = ‖y - t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rfl

/-- The gradient of the squared-error loss is `2 (y - t)`. -/
theorem hasGradientAt_sqLoss (t y : Vec n) : HasGradientAt (sqLoss t) (2 • (y - t)) y := by
  rw [show sqLoss t = fun y => ‖y - t‖ ^ 2 from funext (sqLoss_eq_norm_sq t),
    hasGradientAt_iff_hasFDerivAt]
  have h := ((hasFDerivAt_id y).sub_const t).norm_sq
  refine h.congr_fderiv ?_
  ext v
  simp [toDual_apply_apply, two_smul]

/-- Two affine layers: the backward pass multiplies by the transposes in reverse order. -/
example (W₁ W₂ : Matrix (Fin n) (Fin n) ℝ) (b₁ b₂ x g : Vec n) :
    backward [Layer.affine W₁ b₁, Layer.affine W₂ b₂] x g =
      toLp 2 (W₁ᵀ *ᵥ (W₂ᵀ *ᵥ ofLp g)) := rfl

/-- End to end: the gradient of the loss of a two-layer network with respect to its input. -/
example (W₁ W₂ : Matrix (Fin n) (Fin n) ℝ) (b₁ b₂ x t : Vec n) :
    let net := [Layer.affine W₁ b₁, Layer.affine W₂ b₂]
    HasGradientAt (sqLoss t ∘ forward net)
      (toLp 2 (W₁ᵀ *ᵥ (W₂ᵀ *ᵥ ofLp (2 • (forward net x - t))))) x :=
  backward_correct _ _ x _ (hasGradientAt_sqLoss t _)

/-- A concrete computation: `Wᵀ g` for `W = [[1, 2], [3, 4]]` and `g = [1, 1]`. -/
example :
    backward [Layer.affine !![1, 2; 3, 4] 0] 0 (toLp 2 ![1, 1]) = toLp 2 ![4, 6] := by
  ext i
  fin_cases i <;> simp [backward, Layer.affine, Matrix.transpose, dotProduct, Fin.sum_univ_two]
    <;> norm_num
