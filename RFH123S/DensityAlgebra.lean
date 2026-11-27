import Mathlib

open Real
namespace RFH123S

/-- Turn the Behrend cardinality lower bound and a rounded base into an
explicit density loss. No geometric or prime-distribution assumptions. -/
lemma behrend_density_majorant (H W A L n T : ℝ) (q : ℕ)
    (hH : 0 ≤ H) (hW : 0 < W) (hA : 0 < A) (hL : 0 < L)
    (hn : 0 < n) (hT : 0 < T)
    (hcard : A ^ q / (n * A ^ 2) ≤ T)
    (hround : W ≤ A ^ q * (2 * L) ^ q) :
    H / T ≤ (H / W) * (n * A ^ 2 * (2 * L) ^ q) := by
  have hnA : 0 < n * A ^ 2 := by positivity
  have hcard' := (div_le_iff₀ hnA).mp hcard
  have hWT : W ≤ T * (n * A ^ 2 * (2 * L) ^ q) := calc
    W ≤ A ^ q * (2 * L) ^ q := hround
    _ ≤ (T * (n * A ^ 2)) * (2 * L) ^ q :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by ring
  apply (div_le_iff₀ hT).2
  calc
    H = H / W * W := by field_simp
    _ ≤ H / W * (T * (n * A ^ 2 * (2 * L) ^ q)) :=
      mul_le_mul_of_nonneg_left hWT (by positivity)
    _ = _ := by ring

/-- Separate the four logarithmic losses, so that choosing the Behrend
dimension and base only requires upper bounds for those four scalars. -/
lemma behrend_density_log (H W A L n T B : ℝ) (q : ℕ)
    (hH : 0 < H) (hW : 0 < W) (hA : 0 < A) (hL : 0 < L)
    (hn : 0 < n) (hT : 0 < T)
    (hcard : A ^ q / (n * A ^ 2) ≤ T)
    (hround : W ≤ A ^ q * (2 * L) ^ q)
    (hlog : log (H / W) + log n + 2 * log A + q * log (2 * L) ≤ B) :
    H / T ≤ exp B := by
  have h := behrend_density_majorant H W A L n T q hH.le hW hA hL hn hT hcard hround
  have hp : 0 < H / W := by positivity
  have hnA : 0 < n * A ^ 2 := by positivity
  have hpow : 0 < (2 * L) ^ q := by positivity
  have hprod : 0 < (H / W) * (n * A ^ 2 * (2 * L) ^ q) := by positivity
  refine h.trans ?_
  calc
    _ = exp (log ((H / W) * (n * A ^ 2 * (2 * L) ^ q))) :=
      (Real.exp_log hprod).symm
    _ ≤ exp B := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul hp.ne' (by positivity : n * A ^ 2 * (2 * L) ^ q ≠ 0),
        Real.log_mul hnA.ne' hpow.ne', Real.log_mul hn.ne' (by positivity : A ^ 2 ≠ 0),
        Real.log_pow, Real.log_pow]
      linarith

end RFH123S
