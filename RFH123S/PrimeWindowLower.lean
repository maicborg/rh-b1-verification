import Mathlib

open Real Finset
namespace RFH123S

/-- One-sided prime mass estimate with a lower main term /q.
Unlike a symmetric error about /q, this is compatible with the
actual arithmetic progression main term /phi(q). -/
lemma prime_window_positive_lower (A B u U q mass : ℝ)
    (hu : 1 ≤ u) (hlarge : 16*(A+B)+1 ≤ u) (hU : u^2 ≤ U)
    (hq : 0 < q) (hqB : q ≤ exp (B*u))
    (hlower : exp U/q - exp (A*u+(15/16:ℝ)*U) ≤ mass) :
    0 < mass := by
  have hup : 0 < u := by linarith
  have hmul := mul_le_mul_of_nonneg_right hlarge hup.le
  have hgap : A*u+(15/16:ℝ)*U+B*u < U := by nlinarith
  have hE : exp (A*u+(15/16:ℝ)*U) < exp U/q := by
    apply (lt_div_iff₀ hq).2
    calc
      _ ≤ exp (A*u+(15/16:ℝ)*U)*exp (B*u) :=
        mul_le_mul_of_nonneg_left hqB (Real.exp_pos _).le
      _ = exp (A*u+(15/16:ℝ)*U+B*u) := (Real.exp_add _ _).symm
      _ < exp U := Real.exp_lt_exp.mpr hgap
  linarith

/-- The correct main term divided by a positive totient no larger than q
implies the lower estimate. -/
lemma prime_mass_lower_of_totient (U q phi E mass : ℝ)
    (hq : 0 < q) (hp : 0 < phi) (hpq : phi ≤ q)
    (herr : (exp (U+1)-exp U)/phi - E ≤ mass) :
    exp U/q - E ≤ mass := by
  have h2 : (2 : ℝ) ≤ exp 1 := calc
    (2 : ℝ) = 1+1 := by norm_num
    _ ≤ exp 1 := Real.add_one_le_exp (1 : ℝ)
  have hdiff : exp U ≤ exp (U+1)-exp U := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos U).le]
  have hqphi : exp U/q ≤ exp U/phi := by
    apply (div_le_div_iff₀ hq hp).2
    exact mul_le_mul_of_nonneg_left hpq (Real.exp_pos U).le
  have hm := div_le_div_of_nonneg_right hdiff hp.le
  linarith

#print axioms prime_window_positive_lower
#print axioms prime_mass_lower_of_totient
end RFH123S
