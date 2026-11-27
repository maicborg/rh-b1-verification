import RFH123S.CostAsymptotic

open Real Filter
namespace RFH123S

/-- Absorption of the density loss against the much stronger second-scale decay. -/
lemma eventually_tail_scalar (C e : ℝ) (hC : 0 ≤ C) (he : 0 < e) :
    ∀ᶠ u : ℝ in atTop,
      (1 + exp (40 * sqrt (u * log u))) * (C * exp (-(62500 : ℝ) * u)) ≤
        exp ((e - 1/2) * u) / 2 := by
  filter_upwards [eventually_density_exp 1 zero_lt_one,
    eventually_ge_atTop (max 0 (4 * C))] with u hd hu
  have h0 : 0 ≤ u := (le_max_left _ _).trans hu
  have h4 : 4 * C ≤ u := (le_max_right _ _).trans hu
  have hex : 4 * C ≤ exp u := by linarith [Real.add_one_le_exp u]
  have hhalf : 1 ≤ exp (u / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hd' : exp (40 * sqrt (u * log u)) ≤ exp (u / 2) := by simpa using hd
  calc
    _ ≤ (2 * exp (u / 2)) * (C * exp (-(62500 : ℝ) * u)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hd', hhalf]) (by positivity)
    _ = (4 * C) * exp ((1/2 - 62500) * u) / 2 := by
      rw [show (1/2 - 62500 : ℝ) * u = u / 2 + (-(62500 : ℝ)) * u by ring,
        Real.exp_add]
      ring
    _ ≤ exp u * exp ((1/2 - 62500) * u) / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hex (Real.exp_pos _).le) (by norm_num)
    _ = exp ((3/2 - 62500) * u) / 2 := by
      rw [← Real.exp_add]
      congr 2 <;> ring
    _ ≤ exp ((e - 1/2) * u) / 2 :=
      div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) h0)) (by norm_num)

end RFH123S
