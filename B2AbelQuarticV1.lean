import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentLastMileV1

/-! B2.3: algebraic Abel bound using fourth roots of the weights.
No integration or maximal theorem. The prefix bound is explicit and is
needed only at the endpoint and where the weights strictly decrease. -/
open Finset
noncomputable section
namespace BorghettiRH

theorem b23_quartic_difference (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    a^4-b^4 ≤ 4*a^3*(a-b) := by
  have ha : 0 ≤ a := hb.trans hba
  have h : 0 ≤ (a-b)^2 * (3*a^2+2*a*b+b^2) := by positivity
  calc
    a^4-b^4 ≤ (a^4-b^4)+(a-b)^2*(3*a^2+2*a*b+b^2) := by linarith
    _ = _ := by ring

theorem b23_telescope_real (v : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, (v n-v (n+1))) = v 0-v N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    ring

theorem b23_abel_quartic (a : ℕ → ℂ) (v : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hv : ∀ n, 0 ≤ v n) (hv0 : v 0 ≤ 1)
    (hmono : ∀ n, v (n+1) ≤ v n)
    (hA : ∀ n < N, v (n+1) < v n →
      v n ^ 3 * ‖∑ j ∈ range (n+1), a j‖ ≤ C)
    (hN : v N ^ 3 * ‖∑ j ∈ range (N+1), a j‖ ≤ C) :
    ‖∑ n ∈ range (N+1), ((v n ^ 4 : ℝ) : ℂ) * a n‖ ≤ 4*C := by
  let w : ℕ → ℂ := fun n => ((v n ^ 4 : ℝ) : ℂ)
  let g : ℕ → ℝ := fun n => ‖∑ j ∈ range (n+1), a j‖
  have hnorm (n : ℕ) : ‖w n‖ = v n ^ 4 := by
    change ‖((v n ^ 4 : ℝ) : ℂ)‖ = v n ^ 4
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hv n) 4)]
  have hdiff (n : ℕ) : ‖w n-w (n+1)‖ = v n ^ 4-v (n+1)^4 := by
    have hp : v (n+1)^4 ≤ v n^4 := pow_le_pow_left₀ (hv (n+1)) (hmono n) 4
    dsimp [w]
    rw [← Complex.ofReal_sub]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp)]
  have he : ‖w N‖ * g N ≤ C*v N := by
    rw [hnorm]
    calc
      v N^4*g N = v N*(v N^3*g N) := by ring
      _ ≤ v N*C := mul_le_mul_of_nonneg_left hN (hv N)
      _ = _ := by ring
  have hd : ∀ n ∈ range N, ‖w n-w (n+1)‖*g n ≤
      4*C*(v n-v (n+1)) := by
    intro n hn
    rw [hdiff]
    by_cases hlt : v (n+1) < v n
    · have h := hA n (mem_range.mp hn) hlt
      calc
        _ ≤ (4*v n^3*(v n-v (n+1)))*g n :=
          mul_le_mul_of_nonneg_right
            (b23_quartic_difference _ _ (hv (n+1)) (hmono n)) (norm_nonneg _)
        _ = (4*(v n-v (n+1)))*(v n^3*g n) := by ring
        _ ≤ (4*(v n-v (n+1)))*C :=
          mul_le_mul_of_nonneg_left h (by
            exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hmono n)))
        _ = _ := by ring
    · have heq : v (n+1) = v n := le_antisymm (hmono n) (le_of_not_gt hlt)
      simp [heq]
  change ‖∑ n ∈ range (N+1), w n*a n‖ ≤ 4*C
  calc
    _ ≤ ‖w N‖*g N + ∑ n ∈ range N, ‖w n-w (n+1)‖*g n :=
      b23_discrete_abel_norm a w N g (fun n _ => le_rfl)
    _ ≤ C*v N + ∑ n ∈ range N, 4*C*(v n-v (n+1)) :=
      add_le_add he (sum_le_sum hd)
    _ = C*v N + 4*C*(v 0-v N) := by rw [← mul_sum, b23_telescope_real]
    _ = 4*C*v 0 - 3*C*v N := by ring
    _ ≤ 4*C*v 0 := sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num) hC) (hv N))
    _ ≤ 4*C*1 := mul_le_mul_of_nonneg_left hv0 (mul_nonneg (by norm_num) hC)
    _ = _ := by ring

#print axioms BorghettiRH.b23_quartic_difference
#print axioms BorghettiRH.b23_telescope_real
#print axioms BorghettiRH.b23_abel_quartic
end BorghettiRH
