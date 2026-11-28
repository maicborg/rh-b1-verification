import Mathlib
open Complex Finset Real
namespace RFH123S
noncomputable section

/-- Centering one period makes the reference term cancel exactly. -/
theorem centered_period_sum {ι : Type*} [Fintype ι] (a b : ι → ℂ) (c : ℂ)
    (ha : ∑ i, a i = 0) :
    (∑ i, a i * (b i - c)) = ∑ i, a i * b i := by
  simp [mul_sub, sum_sub_distrib, ← sum_mul, ha]

/-- The block norm estimate reduces to pointwise estimates of the
difference of powers. The block itself is an authentic finite sum. -/
theorem centered_block_norm {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (c : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ 2) (hb : ∀ i, ‖b i - c‖ ≤ D) :
    ‖∑ i, a i * (b i - c)‖ ≤ 2 * Fintype.card ι * D := calc
  _ ≤ ∑ i, ‖a i * (b i - c)‖ := norm_sum_le _ _
  _ ≤ ∑ _i : ι, 2*D := Finset.sum_le_sum (by
    intro i _
    rw [norm_mul]
    exact mul_le_mul (ha i) (hb i) (norm_nonneg _) (by norm_num))
  _ = _ := by simp [nsmul_eq_mul]; ring

/-- Uniform explicit polynomial bound after assembling the two series. -/
theorem growth_assemble (q : ℝ) (s c A Z : ℂ) (hq : 1 ≤ q)
    (hc : ‖c‖ ≤ 1) (ha : ‖A‖ ≤ (4+5*‖s‖)*q)
    (hz : ‖Z‖ ≤ 1 + 3*‖s‖*‖s-1‖) :
    ‖c*Z + (s-1)*A‖ ≤ 12*q*(2+‖s‖)^2 := by
  have hs : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s (1:ℂ)
  have h1 : ‖c*Z‖ ≤ 1 + 3*‖s‖*(‖s‖+1) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (1 + 3*‖s‖*‖s-1‖) := mul_le_mul hc hz (norm_nonneg _) (by norm_num)
      _ ≤ _ := by gcongr; linarith
  have h2 : ‖(s-1)*A‖ ≤ (‖s‖+1)*((4+5*‖s‖)*q) := by
    rw [norm_mul]
    exact mul_le_mul hs ha (norm_nonneg _) (by positivity)
  have h3 := norm_add_le (c*Z) ((s-1)*A)
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg ‖s‖),
    mul_nonneg (sub_nonneg.mpr hq) (norm_nonneg s), norm_nonneg s]

#print axioms centered_period_sum
#print axioms centered_block_norm
#print axioms growth_assemble
end
end RFH123S
