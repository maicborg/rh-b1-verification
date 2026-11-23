import Mathlib

/-! RH1.1 B2 single-endpoint algebraic transfer.
This proves only the numerical ratio step, NOT PNTAPRelW or OpenAI 7/8.
Director: Maicol Borghetti. -/

theorem b2_single_endpoint_ratio
    (T R Em EM J P : ℝ)
    (hT : 0 < T) (hR : 0 ≤ R)
    (hEm : 0 ≤ Em) (hEm4 : Em ≤ 1 / 4)
    (hR4 : R ≤ T / 4)
    (hJ : |J| ≤ EM * T + R)
    (hP : (1 - Em) * T - R ≤ P) :
    |J| ≤ (2 * EM + 2 * R / T) * P := by
  have hP2 : T / 2 ≤ P := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hEm4) (le_of_lt hT)]
  have hEM : 0 ≤ EM := by
    nlinarith [abs_nonneg J]
  have hcoef : 0 ≤ 2 * EM + 2 * R / T := by positivity
  have hmul : (EM + R / T) * T ≤ (2 * EM + 2 * R / T) * P := by
    have h : (EM + R / T) * T ≤ (2 * EM + 2 * R / T) * (T / 2) := by
      field_simp
      ring
    exact h.trans (mul_le_mul_of_nonneg_left hP2 hcoef)
  have hrewrite : (EM + R / T) * T = EM * T + R := by
    field_simp
    ring
  linarith

#print axioms b2_single_endpoint_ratio
