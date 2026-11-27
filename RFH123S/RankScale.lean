import Mathlib

open Real
namespace RFH123S

/-- Select the two integer ranks at the new logarithmic scale. -/
lemma rank_scale (u : ℝ) (hu : 10000 ≤ u) :
    ∃ (o e : ℕ),
      ((2 : ℝ) ^ (o + 1)) ∈ Set.Icc (exp (u / 2)) (2 * exp (u / 2)) ∧
      ((3 : ℝ) ^ (e + 1)) ∈ Set.Icc (exp (5 * u)) (3 * exp (5 * u)) ∧
      ((o + 1) * 22 : ℝ) ≤ 32 * u := by
  have h2 : (1 : ℝ) ≤ exp (u / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : (1 : ℝ) ≤ exp (5 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨o, ho, ho'⟩ := exists_nat_pow_near h2 (by norm_num : (1 : ℝ) < 2)
  obtain ⟨e, he, he'⟩ := exists_nat_pow_near h3 (by norm_num : (1 : ℝ) < 3)
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ)^o) ho
  rw [Real.log_pow, Real.log_exp] at hlog
  have hln : (0.69 : ℝ) < log 2 := (show (0.69 : ℝ) < 0.6931471803 by norm_num).trans Real.log_two_gt_d9
  have ho0 : 0 ≤ (o : ℝ) := by positivity
  have ho1 : (o : ℝ) * 0.69 ≤ u / 2 :=
    (mul_le_mul_of_nonneg_left hln.le ho0).trans hlog
  refine ⟨o, e, ⟨ho'.le, ?_⟩, ⟨he'.le, ?_⟩, ?_⟩
  · rw [pow_succ']
    exact mul_le_mul_of_nonneg_left ho (by norm_num)
  · rw [pow_succ']
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  · linarith

#print axioms rank_scale
end RFH123S
