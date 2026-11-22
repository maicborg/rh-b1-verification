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


/--
An AP count on (sqrt U, U] is the difference of two AP counting
functions. The common main terms cancel at both endpoints.

This is the precise finite-sum reduction needed when applying
OpenAI's 11/12 AP corollary separately at U and sqrt U.
-/
theorem ap_interval_error_to_correlation
    {α : Type*} [DecidableEq α]
    (R : Finset α) (sigma hi lo : α → ℝ)
    (mainHi mainLo EHi ELo : ℝ)
    (hcancel : (∑ r ∈ R, sigma r) = 0)
    (hsigma : ∀ r ∈ R, |sigma r| ≤ 1)
    (hHi : ∀ r ∈ R, |hi r - mainHi| ≤ EHi)
    (hLo : ∀ r ∈ R, |lo r - mainLo| ≤ ELo)
    (hEHi : 0 ≤ EHi)
    (hELo : 0 ≤ ELo) :
    |∑ r ∈ R, sigma r * (hi r - lo r)| ≤
      (R.card : ℝ) * (EHi + ELo) := by
  apply ap_error_to_weighted_correlation R sigma
    (fun r => hi r - lo r) (mainHi - mainLo) (EHi + ELo)
    hcancel hsigma
  · intro r hr
    calc
      |(hi r - lo r) - (mainHi - mainLo)| =
          |(hi r - mainHi) - (lo r - mainLo)| := by ring
      _ ≤ |hi r - mainHi| + |lo r - mainLo| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (hi r - mainHi) 0 (lo r - mainLo))
      _ ≤ EHi + ELo := add_le_add (hHi r hr) (hLo r hr)
  · exact add_nonneg hEHi hELo

#print axioms BorghettiRH.ap_interval_error_to_correlation

/--
Once CRT identifies the admissible residue classes with a product of
two unit groups, orthogonality in one factor cancels the full product.

This proves the FINITE PRODUCT TRANSFER; it does not yet establish
the Legendre-character cancellation in the prime unit group itself.
-/
theorem crt_product_cancellation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β)
    (chi : α → ℝ) (psi : β → ℝ)
    (hchi : (∑ a ∈ A, chi a) = 0) :
    (∑ t ∈ A.product B, chi t.1 * psi t.2) = 0 := by
  calc
    (∑ t ∈ A.product B, chi t.1 * psi t.2) =
        ∑ a ∈ A, ∑ b ∈ B, chi a * psi b := by
      exact Finset.sum_product' A B (fun a b => chi a * psi b)
    _ = (∑ a ∈ A, chi a) * (∑ b ∈ B, psi b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = 0 := by rw [hchi, zero_mul]

#print axioms BorghettiRH.crt_product_cancellation

end BorghettiRH
