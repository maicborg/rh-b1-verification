import Mathlib

open Real Set MeasureTheory Finset
namespace RFH123S

/-- Exact elementary kernel for the finite Abel summation formula. -/
lemma tail_kernel (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Set.Icc a b, t ^ (-2 : ℝ)) = 1/a - 1/b := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h := @integral_rpow a b (-2 : ℝ) (Or.inr ⟨by norm_num, by
    rw [Set.uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1⟩)
  rw [h]
  norm_num [Real.rpow_neg_one]
  ring

/-- Finite Fubini step: integrate each weighted jump separately.
No prime estimate is used. -/
lemma finite_weighted_kernel (S : Finset ℕ) (w : ℕ → ℝ) (z : ℝ)
    (hS : ∀ n ∈ S, 0 < (n : ℝ) ∧ (n : ℝ) ≤ z) :
    (∫ t : ℝ, ∑ n ∈ S, (Set.Icc (n : ℝ) z).indicator
      (fun t => w n * t ^ (-2 : ℝ)) t) =
    ∑ n ∈ S, w n * (1/(n : ℝ) - 1/z) := by
  rw [integral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_indicator measurableSet_Icc, integral_const_mul,
      tail_kernel _ _ (hS n hn).1 (hS n hn).2]
  · intro n hn
    have hpos := (hS n hn).1
    have hhalf : 0 < (n : ℝ)/2 := by positivity
    have hInt : IntegrableOn (fun t : ℝ => w n * t ^ (-2 : ℝ))
        (Ioi ((n : ℝ)/2)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hhalf).const_mul _
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact hInt.mono_set (fun t ht => by have := ht.1; linarith)

#print axioms tail_kernel
#print axioms finite_weighted_kernel
end RFH123S
