import Mathlib

open Real Filter Asymptotics
namespace RFH123S

/-- Logarithmic growth is smaller than every positive linear slope. -/
lemma eventually_log_le_linear (a : ℝ) (ha : 0 < a) :
    ∀ᶠ u : ℝ in atTop, log u ≤ a * u := by
  have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) zero_lt_one).bound ha
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with u hu h0
  have hu' : |log u| ≤ a * u := by
    simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg h0] using hu
  exact (le_abs_self _).trans hu'

/-- The density loss in the new data interface is subexponential in log x. -/
lemma eventually_density_exp (e : ℝ) (he : 0 < e) :
    ∀ᶠ u : ℝ in atTop, exp (40 * sqrt (u * log u)) ≤ exp (e * u / 2) := by
  filter_upwards [eventually_log_le_linear ((e / 80)^2) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with u hu h1
  have h0 : 0 ≤ u := by linarith
  have hl : 0 ≤ log u := Real.log_nonneg h1
  have hs : sqrt (u * log u) ≤ e * u / 80 := by
    have hmul := mul_le_mul_of_nonneg_left hu h0
    have hsq : u * log u ≤ (e * u / 80)^2 := by
      calc
        u * log u ≤ u * ((e / 80)^2 * u) := hmul
        _ = _ := by ring
    calc
      sqrt (u * log u) ≤ sqrt ((e * u / 80)^2) := Real.sqrt_le_sqrt hsq
      _ = e * u / 80 := by rw [Real.sqrt_sq (by positivity)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The polynomial part of the cost is subexponential in log x. -/
lemma eventually_polylog_exp (C e : ℝ) (hC : 0 < C) (he : 0 < e) :
    ∀ᶠ u : ℝ in atTop, C * (10^6 * u)^30 ≤ exp (e * u / 2) := by
  let K := log C + 30 * log (10^6 : ℝ)
  filter_upwards [eventually_log_le_linear (e / 120) (by positivity),
    eventually_ge_atTop (max 1 (4 * K / e))] with u hu hu'
  have h1 : 1 ≤ u := (le_max_left _ _).trans hu'
  have hku : 4 * K / e ≤ u := (le_max_right _ _).trans hu'
  have hk : K ≤ e * u / 4 := by
    have h := (div_le_iff₀ he).mp hku
    linarith
  have hpos : 0 < u := by linarith
  have hlog : log (C * (10^6 * u)^30) = K + 30 * log u := by
    rw [Real.log_mul hC.ne' (by positivity : (10^6 * u)^30 ≠ 0),
      Real.log_pow, Real.log_mul (by norm_num : (10^6 : ℝ) ≠ 0) hpos.ne']
    unfold K
    norm_num
    ring
  calc
    C * (10^6 * u)^30 = exp (log (C * (10^6 * u)^30)) :=
      (Real.exp_log (by positivity)).symm
    _ ≤ exp (e * u / 2) := Real.exp_le_exp.mpr (by rw [hlog]; linarith)

/-- Complete scalar absorption at the proposed scale. -/
lemma eventually_cost_exp (C e : ℝ) (hC : 0 < C) (he : 0 < e) :
    ∀ᶠ u : ℝ in atTop,
      C * (10^6 * u)^30 * exp (40 * sqrt (u * log u)) ≤ exp (e * u) := by
  filter_upwards [eventually_polylog_exp C e hC he,
    eventually_density_exp e he] with u hp hd
  calc
    _ ≤ exp (e * u / 2) * exp (e * u / 2) :=
      mul_le_mul hp hd (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end RFH123S
