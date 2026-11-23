import Mathlib

/-!
Finite exact decomposition for arbitrary complex coefficients, including
arbitrary kappa. No number-theoretic input is assumed proved here.
Director: Maicol Borghetti. Proof engineering: GPT-6.
-/

namespace BorghettiRH

/-- A parity-separated finite sum, with no restriction on complex kappa.
    The sign hypothesis is precisely the missing Jacobi parity identity. -/
theorem finite_parity_decomposition
    {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (odd : ι → Prop) [DecidablePred odd]
    (weight kappa sigma : ι → ℂ)
    (h_even : ∀ i ∈ F, ¬ odd i → sigma i = 1) :
    (∑ i ∈ F, weight i * kappa i * sigma i) =
      (∑ i ∈ F, if odd i then (0 : ℂ) else weight i * kappa i) +
      (∑ i ∈ F, if odd i then weight i * kappa i * sigma i else (0 : ℂ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : odd i
  · simp [h]
  · simp [h, h_even i hi h]

#print axioms BorghettiRH.finite_parity_decomposition

end BorghettiRH
