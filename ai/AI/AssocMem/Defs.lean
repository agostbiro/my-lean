import Mathlib

/-!
# Outer-product memory: definitions

The definitions of the store, the recall, and the interference.
The source is the article "You could have invented transformers from memory" (Alex Wang, 2026):
https://alexwang.ai/posts/associative-memory/
-/

open Matrix

set_option autoImplicit false

namespace AssocMem

variable {M d dv n : ℕ}

/-- The outer-product store. It is the sum of `v_i k_iᵀ` over all memories. -/
def store (K : Matrix (Fin M) (Fin d) ℝ) (V : Matrix (Fin M) (Fin dv) ℝ) :
    Matrix (Fin dv) (Fin d) ℝ :=
  Vᵀ * K

/-- The recall of the query `x`. The store multiplies the query.
The name is not `recall`, because Mathlib uses `recall` as a command keyword. -/
def retrieve (K : Matrix (Fin M) (Fin d) ℝ) (V : Matrix (Fin M) (Fin dv) ℝ)
    (x : Fin d → ℝ) : Fin dv → ℝ :=
  store K V *ᵥ x

/-- The interference in the recall of memory `j`. -/
def interference (K : Matrix (Fin M) (Fin d) ℝ) (V : Matrix (Fin M) (Fin dv) ℝ)
    (j : Fin M) : Fin dv → ℝ :=
  ∑ i ∈ Finset.univ.erase j, (K i ⬝ᵥ K j) • V i

/-- The squared length of a vector, from the dot product. -/
def sqLen (v : Fin n → ℝ) : ℝ := v ⬝ᵥ v

end AssocMem
