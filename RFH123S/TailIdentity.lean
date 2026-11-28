import Mathlib

open Real Set MeasureTheory
namespace RFH123S

/-- The constant must equal the whole convergent error integral; once
that has been proved, the normalized remainder is exactly the negative tail. -/
lemma primeError_eq_neg_tail_of_constant (f : ℝ → ℝ) (z k R : ℝ)
    (hz : 1 ≤ z) (hf : IntegrableOn f (Ioi 1))
    (hk : k = ∫ t in Ioi (1 : ℝ), f t)
    (hR : R = (∫ t in (1 : ℝ)..z, f t) - k) :
    R = -(∫ t in Ioi z, f t) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hf hz
  rw [hR, hk, ← hsplit]
  ring

/-- Subtracting the linear main term before integration gives the log
normalization of the prime remainder. -/
lemma subtract_main_term (A : ℝ → ℝ) (a z : ℝ) (hz : 1 ≤ z)
    (hA : IntervalIntegrable (fun t => A t / t^2) volume 1 z) :
    (∫ t in (1 : ℝ)..z, A t / t^2) - a * log z =
    ∫ t in (1 : ℝ)..z, (A t - a*t) / t^2 := by
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 z :=
    ContinuousOn.intervalIntegrable (fun t ht => continuousAt_inv₀ (by
      have hh : t ∈ Set.Icc (1 : ℝ) z := by simpa [Set.uIcc_of_le hz] using ht
      linarith [hh.1]) |>.continuousWithinAt)
  have heq : (∫ t in (1 : ℝ)..z, t⁻¹) = log z := by
    rw [integral_inv]
    · simp [Real.log_div (by linarith : z ≠ 0) one_ne_zero]
    · rw [Set.uIcc_of_le hz]
      exact fun h => by norm_num at h
  calc
    _ = (∫ t in (1 : ℝ)..z, A t / t^2) -
        (∫ t in (1 : ℝ)..z, a*t⁻¹) := by rw [intervalIntegral.integral_const_mul, heq]
    _ = ∫ t in (1 : ℝ)..z, (A t / t^2 - a*t⁻¹) := by
      rw [intervalIntegral.integral_sub hA (hinv.const_mul a)]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hh : t ∈ Set.Icc (1 : ℝ) z := by simpa [Set.uIcc_of_le hz] using ht
      have hne : t ≠ 0 := by linarith [hh.1]
      field_simp
      ring

#print axioms primeError_eq_neg_tail_of_constant
#print axioms subtract_main_term
end RFH123S
