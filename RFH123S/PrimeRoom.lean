import Mathlib

open Real Filter
namespace RFH123S

/-- All auxiliary-prime windows fit inside the available logarithmic
range. The class number is fixed while u tends to infinity. -/
lemma eventually_prime_room (h : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      let L : ℝ := (10^6*u)^6
      0 < L ∧ (2*(h : ℝ)+1)*sqrt L ≤ L ∧ 11*L ≤ exp (11*u) := by
  filter_upwards [eventually_ge_atTop (max (10^40 : ℝ) (2*(h : ℝ)+1))] with u hu
  have hlarge : (10^40 : ℝ) ≤ u := (le_max_left _ _).trans hu
  have hh : 2*(h : ℝ)+1 ≤ u := (le_max_right _ _).trans hu
  have hu1 : 1 ≤ u := by linarith
  have hup : 0 < u := by linarith
  let B : ℝ := 10^6*u
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by dsimp [B]; linarith
  have hBu : u ≤ B := by dsimp [B]; linarith
  have hpow : B ≤ B^3 := by
    have h := mul_nonneg (show 0 ≤ B-1 by linarith) (show 0 ≤ B^2+B by positivity)
    nlinarith
  have hsqrt : sqrt (B^6) = B^3 := by
    rw [show B^6 = (B^3)^2 by ring, Real.sqrt_sq (by positivity)]
  have hr : (2*(h : ℝ)+1)*sqrt (B^6) ≤ B^6 := by
    rw [hsqrt]
    calc
      _ ≤ B^3*B^3 := mul_le_mul_of_nonneg_right (hh.trans (hBu.trans hpow)) (by positivity)
      _ = _ := by ring
  have hcoef : (11*10^36 : ℝ) ≤ (11^7/5040 : ℝ)*u := by
    norm_num
    linarith
  have hex := Real.pow_div_factorial_le_exp (11*u) (show 0 ≤ 11*u by positivity) 7
  norm_num at hex
  have hL : 11*B^6 ≤ exp (11*u) := calc
    11*B^6 = (11*10^36 : ℝ)*u^6 := by dsimp [B]; ring
    _ ≤ ((11^7/5040 : ℝ)*u)*u^6 := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (11*u)^7/5040 := by ring
    _ ≤ _ := hex
  exact ⟨by positivity,hr,hL⟩

#print axioms eventually_prime_room
end RFH123S
