import Mathlib
open Real
namespace RFH123S

/-- Reciprocal variables a=1/n and b=1/x. This is the exact weight
of F(x)-3 F(3x/2)+2 F(2x). -/
noncomputable def tentWeight (a b : ℝ) : ℝ :=
  max (a-b) 0 - 3 * max (a-2*b/3) 0 + 2 * max (a-b/2) 0

lemma tent_weight_outside_right (a b : ℝ) (hb : 0 ≤ b) (ha : b ≤ a) :
    tentWeight a b = 0 := by
  unfold tentWeight
  rw [max_eq_left (by linarith : 0 ≤ a-b),
    max_eq_left (by linarith : 0 ≤ a-2*b/3),
    max_eq_left (by linarith : 0 ≤ a-b/2)]
  ring

lemma tent_weight_outside_left (a b : ℝ) (hb : 0 ≤ b) (ha : a ≤ b/2) :
    tentWeight a b = 0 := by
  unfold tentWeight
  rw [max_eq_right (by linarith : a-b ≤ 0),
    max_eq_right (by linarith : a-2*b/3 ≤ 0),
    max_eq_right (by linarith : a-b/2 ≤ 0)]
  ring

lemma tent_weight_bounds (a b : ℝ) (hb : 0 ≤ b) :
    0 ≤ tentWeight a b ∧ tentWeight a b ≤ b/3 := by
  by_cases h : b ≤ a
  · rw [tent_weight_outside_right a b hb h]
    constructor <;> linarith
  by_cases l : a ≤ b/2
  · rw [tent_weight_outside_left a b hb l]
    constructor <;> linarith
  unfold tentWeight
  rw [max_eq_right (by linarith : a-b ≤ 0),
    max_eq_left (by linarith : 0 ≤ a-b/2)]
  by_cases m : 2*b/3 ≤ a
  · rw [max_eq_left (by linarith : 0 ≤ a-2*b/3)]
    constructor <;> linarith
  · rw [max_eq_right (by linarith : a-2*b/3 ≤ 0)]
    constructor <;> linarith

lemma tent_log_main (x : ℝ) (hx : 0 < x) :
    log x - 3*log (3*x/2) + 2*log (2*x) = log (32/27 : ℝ) := by
  rw [show 3*x/2 = x*(3/2) by ring, show 2*x = x*2 by ring,
    Real.log_mul hx.ne' (by norm_num : (3/2:ℝ) ≠ 0),
    Real.log_mul hx.ne' (by norm_num : (2:ℝ) ≠ 0)]
  calc
    _ = 2*log 2 - 3*log (3/2) := by ring
    _ = log ((2:ℝ)^2 / (3/2:ℝ)^3) := by
      have h₂ : log ((2:ℝ)^2) = 2*log 2 := by rw [Real.log_pow]; norm_num
      have h₃ : log ((3/2:ℝ)^3) = 3*log (3/2) := by rw [Real.log_pow]; norm_num
      calc
        _ = log ((2:ℝ)^2) - log ((3/2:ℝ)^3) := by rw [h₂, h₃]
        _ = _ := (Real.log_div (by positivity) (by positivity)).symm
    _ = _ := by norm_num

lemma tent_log_positive : 0 < log (32/27 : ℝ) :=
  Real.log_pos (by norm_num)

#print axioms tent_weight_outside_right
#print axioms tent_weight_outside_left
#print axioms tent_weight_bounds
#print axioms tent_log_main
#print axioms tent_log_positive
end RFH123S
