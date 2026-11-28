import Mathlib
open Complex MeasureTheory
open scoped FourierTransform
namespace RFH123S

/-- Actual Fourier inversion, with the normalization of Mathlib. -/
theorem inverse_fourier_real_integral (f : ℝ → ℂ)
    (hf : Integrable f) (hF : Integrable (𝓕 f)) (v : ℝ)
    (hv : ContinuousAt f v) :
    f v = ∫ t : ℝ, Complex.exp ((↑(2 * Real.pi * (v * t)) : ℂ) * I) * (𝓕 f) t := by
  have H := hf.fourierInv_fourier_eq hF hv
  rw [Real.fourierInv_eq'] at H
  simpa [Real.inner_apply, smul_eq_mul, mul_assoc] using H.symm

/-- The inverse transform gives a direct L1 bound, with no residue calculation. -/
theorem norm_le_integral_fourier (f : ℝ → ℂ)
    (hf : Integrable f) (hF : Integrable (𝓕 f)) (v : ℝ)
    (hv : ContinuousAt f v) : ‖f v‖ ≤ ∫ t : ℝ, ‖(𝓕 f) t‖ := by
  rw [inverse_fourier_real_integral f hf hF v hv]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp]
  simp

#print axioms inverse_fourier_real_integral
#print axioms norm_le_integral_fourier
end RFH123S
