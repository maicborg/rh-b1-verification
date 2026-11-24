import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentBoundV1

open Finset
noncomputable section
namespace BorghettiRH

theorem b23_complex_pow_le (z : ℂ) (k : ℕ) :
    ‖z‖^(2*k) ≤ (2 : ℝ)^k * (z.re^(2*k) + z.im^(2*k)) := by
  have hz : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hr : 0 ≤ z.re^(2*k) := by rw [pow_mul]; positivity
  have hi : 0 ≤ z.im^(2*k) := by rw [pow_mul]; positivity
  by_cases h : z.re^2 ≤ z.im^2
  · calc
      ‖z‖^(2*k) = (‖z‖^2)^k := pow_mul _ _ _
      _ ≤ (2*z.im^2)^k := pow_le_pow_left₀ (sq_nonneg _) (by linarith) _
      _ = (2 : ℝ)^k * z.im^(2*k) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hr) (by positivity)
  · calc
      ‖z‖^(2*k) = (‖z‖^2)^k := pow_mul _ _ _
      _ ≤ (2*z.re^2)^k := pow_le_pow_left₀ (sq_nonneg _) (by linarith) _
      _ = (2 : ℝ)^k * z.re^(2*k) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hi) (by positivity)

theorem b23_complex_high_moment {α β : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (P : Finset β) (a : α → ℂ) (χ : β → α → ℝ)
    (k : ℕ) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (ha : ∀ p, ‖a p‖ ≤ L)
    (hχ : ∀ q ∈ P, ∀ p, |χ q p| ≤ 1)
    (hcorr : ∀ f : Fin (2*k) → α, k < (b23Range f).card →
      |∑ q ∈ P, ∏ i, χ q (f i)| ≤ δ * (P.card : ℝ)) :
    (∑ q ∈ P, ‖∑ p : α, a p * (χ q p : ℂ)‖^(2*k)) ≤
      (2 : ℝ)^(k+1) * (L^(2*k) * (P.card : ℝ) *
        (((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ) +
          δ * ((Fintype.card α)^(2*k) : ℕ))) := by
  classical
  let z : β → ℂ := fun q => ∑ p : α, a p * (χ q p : ℂ)
  have hre (q : β) : (z q).re = ∑ p : α, (a p).re * χ q p := by
    simp [z, Complex.re_sum, Complex.mul_re]
  have him (q : β) : (z q).im = ∑ p : α, (a p).im * χ q p := by
    simp [z, Complex.im_sum, Complex.mul_im]
  have hreal := b23_real_high_moment P (fun p => (a p).re) χ k L δ hL hδ
    (fun p => (Complex.abs_re_le_norm (a p)).trans (ha p)) hχ hcorr
  have himag := b23_real_high_moment P (fun p => (a p).im) χ k L δ hL hδ
    (fun p => (Complex.abs_im_le_norm (a p)).trans (ha p)) hχ hcorr
  let R : ℝ := L^(2*k) * (P.card : ℝ) *
      (((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ) +
        δ * ((Fintype.card α)^(2*k) : ℕ))
  change (∑ q ∈ P, ‖z q‖^(2*k)) ≤ (2 : ℝ)^(k+1) * R
  calc
    _ ≤ ∑ q ∈ P, (2 : ℝ)^k * ((z q).re^(2*k) + (z q).im^(2*k)) :=
      sum_le_sum (fun q _ => b23_complex_pow_le (z q) k)
    _ = (2 : ℝ)^k * ((∑ q ∈ P, (z q).re^(2*k)) +
        (∑ q ∈ P, (z q).im^(2*k))) := by rw [← mul_sum, sum_add_distrib]
    _ ≤ (2 : ℝ)^k * (R + R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp_rw [hre, him]
      exact add_le_add hreal himag
    _ = _ := by rw [pow_succ]; ring

#print axioms BorghettiRH.b23_complex_pow_le
#print axioms BorghettiRH.b23_complex_high_moment
end BorghettiRH
