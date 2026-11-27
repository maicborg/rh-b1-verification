import Mathlib

open Real
namespace RFH123S

/-- The selected rank implies the exponential scale of the cyclic group. -/
lemma rank_power_bounds (u : ℝ) (o : ℕ)
    (hm : (2 : ℝ)^(o+1) ∈ Set.Icc (exp (u/2)) (2*exp (u/2))) :
    exp (11*u) ≤ (2 : ℝ)^((o+1)*22) ∧
      (2 : ℝ)^((o+1)*22) ≤ (2 : ℝ)^22 * exp (11*u) := by
  have he : exp (u/2)^22 = exp (11*u) := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  rw [pow_mul]
  constructor
  · rw [← he]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hm.1 _
  · rw [← he, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hm.2 _

/-- Concrete polynomial overhead of the tower, including the loss in
the order lower bound, at the new rank. -/
lemma density_rank_overhead (N s : ℕ) (u : ℝ)
    (hu : 1 ≤ u) (hs : 0 < s) (hsu : (s : ℝ) ≤ 32*u)
    (hlo : exp (11*u) ≤ (2 : ℝ)^s)
    (hhi : (2 : ℝ)^s ≤ (2 : ℝ)^22 * exp (11*u)) :
    let K : ℝ := (3 : ℝ)^(Nat.log 3 s + 5)
    let H : ℝ := K * 2^s
    let W : ℝ := 2^s / ((N : ℝ)*K+2)
    let L : ℝ := 324*s
    let C : ℝ := 10^10 * ((N : ℝ)+1)
    0 < H ∧ 0 < W ∧ 1 ≤ L ∧ H/W ≤ C*u^2 ∧ L ≤ C*u ∧
      exp (11*u)/(C*u) ≤ W ∧ W ≤ C*exp (11*u) := by
  dsimp only
  let K : ℝ := (3 : ℝ)^(Nat.log 3 s + 5)
  let D : ℝ := (N : ℝ)*K+2
  let C : ℝ := 10^10*((N : ℝ)+1)
  have hK : 0 < K := by positivity
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD2 : 1 ≤ D := by dsimp [D]; nlinarith
  have hC2 : (2 : ℝ)^22 ≤ C := by dsimp [C]; norm_num; linarith
  have hKs : K ≤ 243*(s : ℝ) := by
    have hn := Nat.pow_log_le_self 3 hs.ne'
    have hnr : (3 : ℝ)^(Nat.log 3 s) ≤ (s : ℝ) := by exact_mod_cast hn
    dsimp [K]
    rw [pow_add]
    norm_num
    linarith
  have hKu : K ≤ 7776*u := by linarith
  have hDupper : D ≤ 7778*((N : ℝ)+1)*u := by
    dsimp [D]
    have h := mul_le_mul_of_nonneg_left hKu hN
    nlinarith
  have hDC : D ≤ C*u := by
    dsimp [C]
    nlinarith
  have hKD : K*D ≤ C*u^2 := by
    calc
      K*D ≤ (7776*u)*(7778*((N : ℝ)+1)*u) :=
        mul_le_mul hKu hDupper hD.le (by positivity)
      _ ≤ C*u^2 := by dsimp [C]; nlinarith [mul_nonneg (show 0 ≤ (N : ℝ)+1 by positivity) (sq_nonneg u)]
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  change 0 < K*2^s ∧ 0 < (2 : ℝ)^s/D ∧ 1 ≤ 324*(s : ℝ) ∧
    K*2^s / ((2 : ℝ)^s/D) ≤ C*u^2 ∧ 324*(s : ℝ) ≤ C*u ∧
    exp (11*u)/(C*u) ≤ (2 : ℝ)^s/D ∧ (2 : ℝ)^s/D ≤ C*exp (11*u)
  refine ⟨by positivity, by positivity, by linarith, ?_, ?_, ?_, ?_⟩
  · have heq : K*2^s / ((2 : ℝ)^s/D) = K*D := by field_simp
    rw [heq]
    exact hKD
  · dsimp [C]
    nlinarith [mul_nonneg hN (show 0 ≤ u by linarith)]
  · exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hD hDC).trans
      (div_le_div_of_nonneg_right hlo hD.le)
  · calc
      (2 : ℝ)^s/D ≤ (2 : ℝ)^s := (div_le_self (by positivity) hD2)
      _ ≤ (2 : ℝ)^22 * exp (11*u) := hhi
      _ ≤ C * exp (11*u) := mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le

#print axioms rank_power_bounds
#print axioms density_rank_overhead
end RFH123S
