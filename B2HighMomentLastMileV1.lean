import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentUnionV1

/-! B2.3 deterministic last-mile tools: absorb the off-diagonal moment
term, sum exceptional fractions, and discrete Abel summation without
any measure theory. Analytic scale specialization and the replacement
of QH.stage are not asserted by this file. -/

open Finset
noncomputable section
namespace BorghettiRH

theorem b23_moment_error_absorb (n δ C : ℝ) (k : ℕ)
    (hn : 0 ≤ n) (hsmall : δ*n^k ≤ 1) :
    C*n^k + δ*n^(2*k) ≤ (C+1)*n^k := by
  have h : δ*n^(2*k) = (δ*n^k)*n^k := by
    rw [show 2*k=k+k by omega, pow_add]
    ring
  rw [h]
  have hh := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hn k)
  linarith

theorem b23_power_threshold_identity (t α : ℝ) (k : ℕ) (ht : 0 < t) :
    t^k = (t^((1/2 : ℝ)+α))^(2*k) * t^(-2*(k:ℝ)*α) := by
  have hp : (t^((1/2 : ℝ)+α))^(2*k) =
      t^(((1/2 : ℝ)+α)*(2*(k:ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rfl
  rw [hp, ← Real.rpow_add ht, ← Real.rpow_natCast]
  congr 1
  ring

theorem b23_uniform_tail_count {α β : Type*}
    (P B : Finset α) (T : Finset β) (f : α → β → ℝ)
    (u : β → ℝ) (r : ℕ) (δ η : ℝ)
    (hB : B ⊆ P) (hf : ∀ q ∈ P, ∀ t ∈ T, 0 ≤ f q t)
    (hu : ∀ t ∈ T, 0 < u t)
    (hbad : ∀ q ∈ B, ∃ t ∈ T, u t ≤ f q t)
    (hm : ∀ t ∈ T, (∑ q ∈ P, f q t^r) ≤
      u t^r * (δ*(P.card : ℝ)))
    (hbudget : (T.card : ℝ)*δ ≤ η) :
    (B.card : ℝ) ≤ η*(P.card : ℝ) := by
  have h := b2_highmoment_uniform_bad P B T f u
    (fun _ => δ*(P.card : ℝ)) r hB hf hu hbad hm
  calc
    _ ≤ ∑ _t ∈ T, δ*(P.card : ℝ) := h
    _ = ((T.card : ℝ)*δ)*(P.card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)

/-- Finite summation by parts, for arbitrary complex coefficients and
weights. The index 0 can be made zero to obtain the original S sum. -/
theorem b23_discrete_abel (a w : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (N+1), w n * a n) =
      w N * (∑ n ∈ range (N+1), a n) +
        ∑ n ∈ range N, (w n - w (n+1)) *
          (∑ j ∈ range (n+1), a j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Nat.succ_eq_add_one]
    rw [sum_range_succ (fun n => w n * a n) (N+1), ih,
        sum_range_succ a (N+1),
        sum_range_succ (fun n => (w n - w (n+1)) *
          (∑ j ∈ range (n+1), a j)) N]
    ring

theorem b23_discrete_abel_norm (a w : ℕ → ℂ) (N : ℕ)
    (g : ℕ → ℝ)
    (hA : ∀ n ≤ N, ‖∑ j ∈ range (n+1), a j‖ ≤ g n) :
    ‖∑ n ∈ range (N+1), w n * a n‖ ≤
      ‖w N‖*g N + ∑ n ∈ range N, ‖w n-w (n+1)‖*g n := by
  rw [b23_discrete_abel]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hA N le_rfl) (norm_nonneg _)
  · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
    intro n hn
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hA n (Nat.le_of_lt (mem_range.mp hn)))
      (norm_nonneg _)

#print axioms BorghettiRH.b23_moment_error_absorb
#print axioms BorghettiRH.b23_power_threshold_identity
#print axioms BorghettiRH.b23_uniform_tail_count
#print axioms BorghettiRH.b23_discrete_abel
#print axioms BorghettiRH.b23_discrete_abel_norm
end BorghettiRH
