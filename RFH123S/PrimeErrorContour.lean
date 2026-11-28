import Mathlib
/-! Pole-free contour shift, using Mathlib's Cauchy-Goursat theorem.
Limit argument adapted from PrimeNumberTheoremAnd/PerronFormula.lean
at pin 127b50e33f6033e2147921167a117af96d9ba4ea. -/
open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RFH123S

theorem poleFree_vertical_shift {a b : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ([[a,b]] ×ℂ Set.univ))
    (hbot : Tendsto (fun y : ℝ ↦ ∫ x : ℝ in a..b, f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun y : ℝ ↦ ∫ x : ℝ in a..b, f (x + y * I)) atTop (𝓝 0))
    (ha : Integrable (fun y : ℝ ↦ f (a + y * I)))
    (hb : Integrable (fun y : ℝ ↦ f (b + y * I))) :
    (∫ y : ℝ, f (a + y * I)) = ∫ y : ℝ, f (b + y * I) := by
  let R : ℝ → ℂ := fun T ↦
    (∫ x : ℝ in a..b, f (x + (-T : ℝ) * I)) -
    (∫ x : ℝ in a..b, f (x + T * I)) +
    I • (∫ y : ℝ in -T..T, f (b + y * I)) -
    I • (∫ y : ℝ in -T..T, f (a + y * I))
  have hz : ∀ T : ℝ, R T = 0 := by
    intro T
    have H := integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - I * T) ((b : ℂ) + I * T) (hf.mono (by
        intro z hz
        exact ⟨by simpa using hz.1, trivial⟩))
    simpa [R, sub_re, add_re, mul_re, I_re, I_im, sub_im, add_im,
      mul_im, ofReal_re, ofReal_im] using H
  have hlim : Tendsto R atTop
      (𝓝 (I • (∫ y : ℝ, f (b + y * I)) - I • (∫ y : ℝ, f (a + y * I)))) := by
    unfold R
    rw [← zero_add (I • (∫ y : ℝ, f (b + y * I))), ← sub_self (0 : ℂ)]
    exact (((hbot.comp tendsto_neg_atTop_atBot).sub htop).add
      ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_smul I)).sub
      ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_smul I)
  have hconst : Tendsto R atTop (𝓝 (0 : ℂ)) := by simp [hz]
  have heq := tendsto_nhds_unique hlim hconst
  have hh : I * (∫ y : ℝ, f (b + y * I)) = I * (∫ y : ℝ, f (a + y * I)) :=
    sub_eq_zero.mp (by simpa [smul_eq_mul] using heq)
  exact (mul_left_cancel₀ I_ne_zero hh).symm

#print axioms poleFree_vertical_shift
end
