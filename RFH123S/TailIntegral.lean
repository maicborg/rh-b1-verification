import Mathlib

open Real Set MeasureTheory
namespace RFH123S

/-- The absolutely integrable tail of a power-saving error yields the
exact exponent 1/16. An identity expressing primeError as such an
integral must be supplied separately; this lemma does not assert it. -/
lemma integral_tail_one_sixteenth (f : ℝ → ℝ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 0 < z)
    (hf : IntegrableOn f (Ioi z))
    (hbound : ∀ t ∈ Ioi z, |f t| ≤ C*t^(-(17/16 : ℝ))) :
    |∫ t in Ioi z, f t| ≤ 16*C*z^(-(1/16 : ℝ)) := by
  have hg : IntegrableOn (fun t : ℝ => C*t^(-(17/16 : ℝ))) (Ioi z) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(17/16 : ℝ) < -1) hz).const_mul C
  have hnorm : IntegrableOn (fun t => ‖f t‖) (Ioi z) := hf.norm
  have hmono : (∫ t in Ioi z, ‖f t‖) ≤ ∫ t in Ioi z, C*t^(-(17/16 : ℝ)) := by
    apply setIntegral_mono_on hnorm hg measurableSet_Ioi
    intro t ht
    simpa [Real.norm_eq_abs] using hbound t ht
  have heq : (∫ t in Ioi z, C*t^(-(17/16 : ℝ))) = 16*C*z^(-(1/16 : ℝ)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(17/16 : ℝ) < -1) hz]
    have he : -(17/16 : ℝ)+1 = -(1/16 : ℝ) := by norm_num
    rw [he]
    ring
  calc
    _ = ‖∫ t in Ioi z, f t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Ioi z, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ _ := hmono.trans_eq heq

#print axioms integral_tail_one_sixteenth
end RFH123S
