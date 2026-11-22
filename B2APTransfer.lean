import Mathlib

/-!
# B2: transfer of uniform arithmetic progression errors to quadratic correlations

Program director: Maicol Borghetti (@maicborg).
Proof engineering with GPT-6.

This verifies the elementary analytic-to-combinatorial transfer ONLY.
The equidistribution estimate and the cancellation of character signs
are explicitly assumed, not derived from the OpenAI paper here.
-/

namespace BorghettiRH

/--
If the main terms cancel when weighted by character signs, a uniform
per-residue error bound E gives a correlation error |R| E.

The cancellation hcancel will eventually be proved by CRT and
quadratic character orthogonality. The per-residue error herror
will eventually come from OpenAI's 11/12 prime AP corollary.
-/
theorem ap_error_to_weighted_correlation
    {α : Type*} [DecidableEq α]
    (R : Finset α) (sigma count : α → ℝ) (main E : ℝ)
    (hcancel : (∑ r ∈ R, sigma r) = 0)
    (hsigma : ∀ r ∈ R, |sigma r| ≤ 1)
    (herror : ∀ r ∈ R, |count r - main| ≤ E)
    (hE : 0 ≤ E) :
    |∑ r ∈ R, sigma r * count r| ≤ (R.card : ℝ) * E := by
  classical
  have hid :
      (∑ r ∈ R, sigma r * count r) =
        ∑ r ∈ R, sigma r * (count r - main) := by
    calc
      _ = (∑ r ∈ R, sigma r * (count r - main)) +
            main * (∑ r ∈ R, sigma r) := by
              rw [mul_comm main (∑ r ∈ R, sigma r), Finset.sum_mul]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r hr
              ring
      _ = _ := by simp [hcancel]
  rw [hid]
  calc
    |∑ r ∈ R, sigma r * (count r - main)| ≤
        ∑ r ∈ R, |sigma r * (count r - main)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ R, E := by
          apply Finset.sum_le_sum
          intro r hr
          rw [abs_mul]
          calc
            |sigma r| * |count r - main| ≤ 1 * E := by
              exact mul_le_mul (hsigma r hr) (herror r hr)
                (abs_nonneg _) (by norm_num)
            _ = E := by ring
    _ = (R.card : ℝ) * E := by simp

#print axioms BorghettiRH.ap_error_to_weighted_correlation

end BorghettiRH
