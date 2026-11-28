import Mathlib
open Complex Set
namespace RFH123S
noncomputable section

/-- Entire extension across s=1 is built, not postulated. -/
def centeredKernel (g : ℂ → ℂ) (s : ℂ) : ℂ := dslope g 1 s / s

lemma centeredKernel_eq (g : ℂ → ℂ) {s : ℂ} (hs : s ≠ 1) :
    centeredKernel g s = (g s - g 1) / (s * (s - 1)) := by
  rw [centeredKernel, dslope_of_ne g hs, slope_def_field]
  by_cases h0 : s = 0
  · simp [h0]
  · field_simp [hs, h0] <;> ring

lemma centeredKernel_analyticAt (g : ℂ → ℂ) {s : ℂ}
    (hg : AnalyticAt ℂ g s) (hs : s ≠ 0) :
    AnalyticAt ℂ (centeredKernel g) s := by
  exact (hg.dslope 1).div analyticAt_id hs

lemma centeredKernel_at_one (g : ℂ → ℂ) :
    centeredKernel g 1 = deriv g 1 := by simp [centeredKernel]

lemma centered_transform_algebra (g k s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (g / s - k) / (s - 1) + k / s = (g - k) / (s * (s - 1)) := by
  field_simp [hs0, sub_ne_zero.mpr hs1] <;> ring

#print axioms centeredKernel_eq
#print axioms centeredKernel_analyticAt
#print axioms centeredKernel_at_one
#print axioms centered_transform_algebra
end
end RFH123S
