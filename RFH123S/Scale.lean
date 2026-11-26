import Mathlib

namespace RFH123S
open Real

/-- The arithmetic of the original five scale conditions, with log X1 = 10^6 log X.
The two eventual inequalities are explicit inputs, not assumed results on primes. -/
lemma polylog_scale (u c : ℝ) (hu : 1 ≤ u)
    (hc : 10^12 * c ≤ 6 * log (10^6 * u))
    (h100 : 100 * (6 * log (10^6 * u)) ≤ u) :
    10^12 * c ≤ log ((10^6 * u)^6) ∧
    100 * log ((10^6 * u)^6) ≤ u ∧
    10^6 * u ≤ 10^6 * u ∧
    10^6 * (10^6 * u) ≤ (10^6 * u)^6 ∧
    6 * log (10^6 * u) ≤ log ((10^6 * u)^6) := by
  have hp : (0 : ℝ) < 10^6 * u := by positivity
  rw [Real.log_pow]
  refine ⟨?_, ?_, le_rfl, ?_, ?_⟩
  · simpa using hc
  · simpa using h100
  · have hq : (10^6 : ℝ) ≤ 10^6 * u := by linarith
    have h1 : (1 : ℝ) ≤ 10^6 * u := by linarith
    have h2 : (10^6 * u)^2 ≤ (10^6 * u)^6 := by
      calc
        (10^6 * u)^2 = (10^6 * u)^2 * 1 := by ring
        _ ≤ (10^6 * u)^2 * (10^6 * u)^4 := by
          gcongr
          exact one_le_pow₀ h1
        _ = _ := by ring
    calc
      10^6 * (10^6 * u) ≤ (10^6 * u)^2 := by nlinarith
      _ ≤ _ := h2
  · simp

/-- Density loss from a Behrend lower cardinality, before asymptotic estimates. -/
lemma density_from_cardinality (h N M q T : ℝ)
    (hh : 0 < h) (hN : 0 < N) (hM : 0 < M) (hq : 0 < q) (hT : 0 < T)
    (hcard : M ≤ T * q) :
    h / T ≤ h * q / M := by
  apply (div_le_div_iff₀ hT hM).2
  nlinarith [mul_le_mul_of_nonneg_left hcard hh.le]

end RFH123S
