import Mathlib

open Real
namespace RFH123S

/-- Capacity for the rounded Behrend base follows from a lower logarithmic
bound on W; the selected base also has the required upper logarithm. -/
lemma density_capacity (u v W L : ℝ) (q : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (hW : 0 < W) (hL : 1 ≤ L)
    (hq : 0 < q) (hqhi : (q : ℝ) ≤ 2 * sqrt (u / v))
    (hlogL : log (2 * L) ≤ 2 * v) (hlogW : 8 * u ≤ log W) :
    (2 * L)^q ≤ W := by
  let z := sqrt (u / v)
  have hz : 0 ≤ z := by positivity
  have hz2 : z^2 = u / v := Real.sq_sqrt (by positivity)
  have hzv : z * v ≤ u := by
    have hsq : (z * v)^2 ≤ u^2 := by
      rw [mul_pow, hz2]
      have h := mul_le_mul_of_nonneg_left hvu hu.le
      calc
        u / v * v^2 = u * v := by field_simp
        _ ≤ u^2 := by nlinarith
    nlinarith [mul_nonneg hz hv.le]
  have hlog : log ((2 * L)^q) ≤ log W := by
    rw [Real.log_pow]
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    calc
      (q : ℝ) * log (2 * L) ≤ (q : ℝ) * (2 * v) :=
        mul_le_mul_of_nonneg_left hlogL hq0
      _ ≤ (2 * z) * (2 * v) := mul_le_mul_of_nonneg_right hqhi (by positivity)
      _ ≤ log W := by linarith
  exact (Real.log_le_log_iff (by positivity) hW).mp hlog

lemma density_base_log (u W L A : ℝ) (q : ℕ)
    (hW : 0 < W) (hL : 1 ≤ L) (hA : 0 < A) (hq : 0 < q)
    (hfit : A^q * L^q ≤ W) (hlogW : log W ≤ 12 * u) :
    log A ≤ 12 * u / (q : ℝ) := by
  have h := Real.log_le_log (by positivity : 0 < A^q * L^q) hfit
  rw [Real.log_mul (by positivity : A^q ≠ 0) (by positivity : L^q ≠ 0),
    Real.log_pow, Real.log_pow] at h
  have hnon : 0 ≤ (q : ℝ) * log L := mul_nonneg (by positivity) (Real.log_nonneg hL)
  apply (le_div_iff₀ (show 0 < (q : ℝ) by exact_mod_cast hq)).2
  linarith

#print axioms density_capacity
#print axioms density_base_log
end RFH123S
