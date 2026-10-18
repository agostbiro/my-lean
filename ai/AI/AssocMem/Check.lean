import AI.AssocMem

/-!
# Outer-product memory: final checks

The axiom guards make sure that each main result uses only the standard axioms.
If a proof uses `sorry`, its axiom list changes and the guard fails.
The statement guards make sure that the main statements match the plan.
This file is not part of the `AI` library. Run `lake env lean ai/AI/AssocMem/Check.lean`.
-/

/-- info: 'AssocMem.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AssocMem.main

/-- info: 'AssocMem.main_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AssocMem.main_unit

/-- info: 'AssocMem.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AssocMem.capacity

open MeasureTheory AssocMem in
/-- `PMF.integral_eq_sum` in `integral_eq_avg` needs this instance. -/
example {M d : ℕ} : MeasurableSingletonClass (Signs M d) := inferInstance

open Matrix MeasureTheory AssocMem in
example {M d dv : ℕ} (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      = (1 / (d : ℝ)) * ∑ i ∈ Finset.univ.erase j, sqLen (V i) :=
  main hd V j

open Matrix MeasureTheory AssocMem in
example {M d dv : ℕ} (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ)
    (hV : ∀ i, sqLen (V i) = 1) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      = ((M : ℝ) - 1) / d :=
  main_unit hd V hV j

open Matrix MeasureTheory AssocMem in
example {M d dv : ℕ} (hd : 0 < d) (V : Matrix (Fin M) (Fin dv) ℝ)
    (hV : ∀ i, sqLen (V i) = 1) (j : Fin M) :
    ∫ ω, sqLen (retrieve (signKeys ω) V (signKeys ω j) - V j) ∂signMeasure M d
      ≤ sqLen (V j) ↔ M ≤ d + 1 :=
  capacity hd V hV j
