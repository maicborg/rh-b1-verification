import Mathlib

open Real Filter Asymptotics
namespace RFH123S

/-- Uniform scalar logarithm bounds from the polynomial overhead of the
geometric rank. C is fixed; no assumption on primes or RH is used. -/
lemma eventually_density_log_scales (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ u : ℝ in atTop, ∀ H W L : ℝ,
      0 < H → 0 < W → 1 ≤ L →
      H / W ≤ C * u^2 → L ≤ C * u →
      exp (11 * u) / (C * u) ≤ W → W ≤ C * exp (11 * u) →
      log (H / W) ≤ 3 * log u ∧ log (2 * L) ≤ 2 * log u ∧
      8 * u ≤ log W ∧ log W ≤ 12 * u := by
  have hc : 0 < C := by linarith
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) zero_lt_one).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (max (2 * C) (log C))] with u hu hU H W L hH hW hL hratio hLupper hWlower hWupper
  have huc : 2 * C ≤ u := (le_max_left _ _).trans hU
  have huc' : log C ≤ u := (le_max_right _ _).trans hU
  have hup : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hlogu : log u ≤ u := by
    have h : |log u| ≤ u := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hup.le] using hu
    exact (le_abs_self _).trans h
  have hC_u : C ≤ u := by linarith
  have hlogC : log C ≤ log u := Real.log_le_log hc hC_u
  have h2C : log (2 * C) ≤ log u := Real.log_le_log (by positivity) huc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Real.log_le_log (by positivity : 0 < H / W) hratio
    rw [Real.log_mul hc.ne' (by positivity : u^2 ≠ 0), Real.log_pow] at h
    linarith
  · have h := Real.log_le_log (by positivity : 0 < 2 * L)
      (mul_le_mul_of_nonneg_left hLupper (by norm_num : (0 : ℝ) ≤ 2))
    have heq : 2 * (C * u) = (2 * C) * u := by ring
    rw [heq, Real.log_mul (by positivity : 2 * C ≠ 0) hup.ne'] at h
    linarith
  · have h := Real.log_le_log (by positivity : 0 < exp (11 * u) / (C * u)) hWlower
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity : C*u ≠ 0),
      Real.log_exp, Real.log_mul hc.ne' hup.ne'] at h
    linarith
  · have h := Real.log_le_log hW hWupper
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    linarith

#print axioms eventually_density_log_scales
end RFH123S
