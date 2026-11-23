import Mathlib

/-! RH1.1 B2 single-endpoint algebraic transfer.
Only the numerical ratio step, not PNTAPRelW or OpenAI 7/8. -/

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
  have hsum : 0 ≤ EM * T + R := le_trans (abs_nonneg J) hJ
  have hcoef : 0 ≤ 2 * EM + 2 * R / T := by
    have hdiv : 0 ≤ (EM * T + R) / T :=
      div_nonneg hsum (le_of_lt hT)
    have heq : 2 * EM + 2 * R / T = 2 * ((EM * T + R) / T) := by
      field_simp
      <;> ring
    rw [heq]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hP2 hcoef
  have heq : (2 * EM + 2 * R / T) * (T / 2) = EM * T + R := by
    field_simp
    <;> ring
  rw [heq] at hmul
  exact hJ.trans hmul

#print axioms b2_single_endpoint_ratio
