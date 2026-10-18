import AI.AssocMem.Expectation

/-!
# Outer-product memory: random-sign keys

Random-sign keys satisfy the moment facts (H1) and (H2).
The proofs use a finite average and a sign flip. They do not use the independence API.
-/

open Matrix MeasureTheory

set_option autoImplicit false

namespace AssocMem

variable {M d : ℕ}

/-- The sample space: one sign for each key entry. -/
abbrev Signs (M d : ℕ) := Fin M → Fin d → Bool

/-- The keys. Each entry is `1 / √d` or `-1 / √d`. -/
noncomputable def signKeys (ω : Signs M d) : Matrix (Fin M) (Fin d) ℝ :=
  Matrix.of fun i a => (if ω i a then 1 else -1) / Real.sqrt (d : ℝ)

/-- The average of `f` over all sign patterns. -/
noncomputable def avg (f : Signs M d → ℝ) : ℝ :=
  (Fintype.card (Signs M d) : ℝ)⁻¹ * ∑ ω, f ω

/-- Flip the sign of entry `(i, a)`. -/
def flipSign (i : Fin M) (a : Fin d) (ω : Signs M d) : Signs M d :=
  Function.update ω i (Function.update (ω i) a (!ω i a))

/-- The uniform probability measure on the sign patterns. -/
noncomputable def signMeasure (M d : ℕ) : Measure (Signs M d) :=
  (PMF.uniformOfFintype (Signs M d)).toMeasure

instance : IsProbabilityMeasure (signMeasure M d) := by
  unfold signMeasure
  infer_instance

variable (ω : Signs M d) (i i' j l : Fin M) (a a' : Fin d)

/-- Statement: Two flips of the same entry give the original sign pattern. -/
theorem flipSign_flipSign : flipSign i a (flipSign i a ω) = ω := by
  simp only [flipSign, Function.update_self, Bool.not_not, Function.update_idem,
    Function.update_eq_self]

/-- Statement: If the flip of `(i, a)` changes the sign of `f`, then the sum of `f` is 0. -/
theorem sum_eq_zero_of_flipSign_neg (f : Signs M d → ℝ)
    (h : ∀ ω, f (flipSign i a ω) = -f ω) : ∑ ω, f ω = 0 := by
  have he : ∑ ω, f (flipSign i a ω) = ∑ ω, f ω :=
    Equiv.sum_comp (Function.Involutive.toPerm _ fun ω => flipSign_flipSign ω i a) f
  simp only [h, Finset.sum_neg_distrib] at he
  linarith

/-- Statement: The flip of `(i, a)` changes the sign of the key entry `(i, a)`. -/
theorem signKeys_flipSign_self : signKeys (flipSign i a ω) i a = -signKeys ω i a := by
  simp only [signKeys, Matrix.of_apply, flipSign, Function.update_self]
  cases ω i a <;> simp [neg_div]

variable {ω i i' a a'} in
/-- Statement: The flip of `(i, a)` does not change an entry in a different row. -/
theorem signKeys_flipSign_of_ne_row (h : i' ≠ i) :
    signKeys (flipSign i a ω) i' a' = signKeys ω i' a' := by
  simp only [signKeys, Matrix.of_apply, flipSign, Function.update_of_ne h]

variable {ω i a a'} in
/-- Statement: The flip of `(i, a)` does not change an entry in a different column. -/
theorem signKeys_flipSign_of_ne_col (h : a' ≠ a) :
    signKeys (flipSign i a ω) i a' = signKeys ω i a' := by
  simp only [signKeys, Matrix.of_apply, flipSign, Function.update_self, Function.update_of_ne h]

/-- Statement: The square of a key entry is `1 / d`. -/
theorem signKeys_sq : signKeys ω i a ^ 2 = 1 / d := by
  simp only [signKeys, Matrix.of_apply, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  cases ω i a <;> norm_num

/-- Statement: Each key has squared length 1. -/
theorem sqLen_signKeys (hd : 0 < d) : sqLen (signKeys ω i) = 1 := by
  simp only [sqLen, dotProduct, ← sq, signKeys_sq ω i _, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Statement: The average of a finite sum is the sum of the averages. -/
theorem avg_sum {ι : Type*} (s : Finset ι) (g : ι → Signs M d → ℝ) :
    avg (fun ω : Signs M d => ∑ a ∈ s, g a ω) = ∑ a ∈ s, avg (g a) := by
  simp only [avg]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Statement: The average of a constant is the constant. -/
theorem avg_const (c : ℝ) : avg (fun _ : Signs M d => c) = c := by
  simp only [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Statement: If the flip of `(i, a)` changes the sign of `f`, then the average of `f` is 0. -/
theorem avg_eq_zero_of_flipSign_neg (f : Signs M d → ℝ)
    (h : ∀ ω, f (flipSign i a ω) = -f ω) : avg f = 0 := by
  rw [avg, sum_eq_zero_of_flipSign_neg i a f h, mul_zero]

variable {i j a} in
/-- Helper. Statement: The average of one term of `(K i ⬝ᵥ K j)²` with `a ≠ b` is 0.

Concepts:
- The flip of entry `(i, a)` changes the sign of `K i a` only.
- If a flip changes the sign of a function, then its average is 0.

Plan:
1. Reduce the claim to a sign change under the flip of `(i, a)`.
2. Show the sign change. Only the factor `K i a` changes, because `i ≠ j` and `a ≠ b`.
-/
theorem avg_term_eq_zero_of_ne {b : Fin d} (hij : i ≠ j) (hab : a ≠ b) :
    avg (fun ω : Signs M d =>
      signKeys ω i a * signKeys ω j a * (signKeys ω i b * signKeys ω j b)) = 0 := by
  -- Plan 1: reduce to a sign change
  apply avg_eq_zero_of_flipSign_neg i a
  intro ω
  -- Plan 2: only the factor `K i a` changes
  rw [signKeys_flipSign_self, signKeys_flipSign_of_ne_row hij.symm,
    signKeys_flipSign_of_ne_col hab.symm, signKeys_flipSign_of_ne_row hij.symm]
  ring

variable {i j} in
/-- Statement: (H1) The mean square of the overlap of two different keys is `1 / d`.

Concepts:
- The overlap `K i ⬝ᵥ K j` is a sum over the entries `a`.
- The square of a sum is a double sum over the pairs `(a, b)`.
- The average of a term with `a ≠ b` is 0.
- Each key entry squared is `1 / d`.

Plan:
1. Expand the product into a double sum, and move the average inside.
2. Keep only the terms with `b = a`.
3. Each such term is `1 / d²`. The sum of `d` such terms is `1 / d`.
-/
theorem avg_sq (hd : 0 < d) (hij : i ≠ j) :
    avg (fun ω : Signs M d =>
      (signKeys ω i ⬝ᵥ signKeys ω j) * (signKeys ω i ⬝ᵥ signKeys ω j)) = 1 / d := by
  -- Plan 1: expand into a double sum of averages
  simp only [dotProduct, Finset.sum_mul_sum, avg_sum]
  -- Plan 2: keep the terms with `b = a`
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_eq_single_of_mem a (Finset.mem_univ a)
    fun _ _ hb => avg_term_eq_zero_of_ne hij hb.symm]
  -- Plan 3: each term is `1 / d²`
  simp only [← sq, mul_pow, signKeys_sq, avg_const, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

variable {i j l} in
/-- Statement: (H2) The mean product of the overlaps of `K i` and `K l` with `K j` is 0.

Concepts:
- The product of two overlaps is a double sum over the entries `(a, b)`.
- The flip of entry `(i, a)` changes the sign of `K i a` only.
- If a flip changes the sign of a function, then its average is 0.

Plan:
1. Expand the product into a double sum, and move the average inside.
2. Show that each term is 0 by the flip of `(i, a)`.
3. Show the sign change. Only `K i a` changes, because `i ≠ j` and `i ≠ l`.

The lemma does not need `l ≠ j`.
-/
theorem avg_cross (hij : i ≠ j) (hil : i ≠ l) :
    avg (fun ω : Signs M d =>
      (signKeys ω i ⬝ᵥ signKeys ω j) * (signKeys ω l ⬝ᵥ signKeys ω j)) = 0 := by
  -- Plan 1: expand into a double sum of averages
  simp only [dotProduct, Finset.sum_mul_sum, avg_sum]
  -- Plan 2: each term is 0 by the flip of `(i, a)`
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  apply avg_eq_zero_of_flipSign_neg i a
  intro ω
  -- Plan 3: only the factor `K i a` changes
  rw [signKeys_flipSign_self, signKeys_flipSign_of_ne_row hij.symm,
    signKeys_flipSign_of_ne_row hil.symm, signKeys_flipSign_of_ne_row hij.symm]
  ring

/-- Statement: The integral over `signMeasure M d` is the finite average. -/
theorem integral_eq_avg (f : Signs M d → ℝ) : ∫ ω, f ω ∂signMeasure M d = avg f := by
  rw [signMeasure, PMF.integral_eq_sum, avg, Finset.mul_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Statement: Random-sign keys satisfy the moment facts (H1) and (H2).

Concepts:
- The sample space is finite, so each function on it is integrable.
- The integral over `signMeasure M d` is the finite average.

Plan:
1. Split the claim into the moment facts and integrability.
2. Change each integral into an average.
3. If `i = l`, use (H1). If `i ≠ l`, use (H2).
-/
theorem signKeys_moments (hd : 0 < d) :
    KeyMoments (signMeasure M d) (signKeys (M := M) (d := d)) := by
  -- Plan 1: split into the moment facts and integrability
  refine ⟨fun i l j hij hlj => ?_, fun i l j => MeasureTheory.Integrable.of_finite⟩
  -- Plan 2: change the integral into an average
  rw [integral_eq_avg]
  -- Plan 3: use (H1) or (H2)
  split_ifs with hil
  · subst hil
    exact avg_sq hd hij
  · exact avg_cross hij hil

end AssocMem
