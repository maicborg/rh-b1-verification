import RFH123S.Scale
import RFH123S.CostAsymptotic

open Real Filter
namespace RFH123S

/-- The five scale conditions really do hold eventually for each fixed
parameter c: neither prime windows nor density are assumed. -/
lemma eventually_polylog_scale (c : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      10^12 * c ≤ log ((10^6 * u)^6) ∧
      100 * log ((10^6 * u)^6) ≤ u ∧
      10^6 * u ≤ 10^6 * u ∧
      10^6 * (10^6 * u) ≤ (10^6 * u)^6 ∧
      6 * log (10^6 * u) ≤ log ((10^6 * u)^6) := by
  have ht : Tendsto (fun u : ℝ => log (10^6 * u)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_id.const_mul_atTop (r := (10^6 : ℝ)) (by norm_num))
  filter_upwards [ht.eventually_ge_atTop (10^12 * c / 6),
    eventually_log_le_linear (1 / 1200) (by norm_num),
    eventually_ge_atTop (max 1 (1200 * log (10^6 : ℝ)))] with u hlow hlog hu
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hc : 10^12 * c ≤ 6 * log (10^6 * u) := by linarith
  have h100 : 100 * (6 * log (10^6 * u)) ≤ u := by
    rw [Real.log_mul (by norm_num : (10^6 : ℝ) ≠ 0) (by linarith : u ≠ 0)]
    have hK := (le_max_right _ _).trans hu
    linarith
  exact polylog_scale u c hu1 hc h100

end RFH123S
