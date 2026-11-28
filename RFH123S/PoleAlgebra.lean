import Mathlib
open Complex
namespace RFH123S

/-- Exact algebraic removal of the double pole from the shifted Perron
integrand. A(w) stands for the holomorphic factor x^w/(1+w).
No assumption about L-functions is used here. -/
lemma remove_double_pole (w d A B : ℂ) (hw : w ≠ 0) :
    (d/w-B)*A/w - d/w^2 =
      (d*((A-1)/w)-B*A)/w := by
  field_simp [hw] <;> ring

/-- Coefficient of the linear term in the holomorphic factor. -/
lemma perron_factor_derivative (l : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (w*l)/(1+w)) (l-1) 0 := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp (w*l)) l 0 := by
    simpa using (((hasDerivAt_id (0:ℂ)).mul_const l).cexp)
  have hd : HasDerivAt (fun w : ℂ => 1+w) 1 0 := by
    simpa using (hasDerivAt_id (0:ℂ)).const_add (1:ℂ)
  convert he.div hd (by norm_num : (1:ℂ)+0 ≠ 0) using 1 <;> norm_num

/-- The arithmetic constant from a principal-character pole is
d(log x-1), not d log x. -/
lemma perron_residue_coefficient (d l B : ℂ) :
    d*(l-1)-B = d*l-d-B := by ring

#print axioms remove_double_pole
#print axioms perron_factor_derivative
#print axioms perron_residue_coefficient
end RFH123S
