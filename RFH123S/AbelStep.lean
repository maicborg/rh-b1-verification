import Mathlib

open Real Finset
namespace RFH123S

/-- The two finite weighted sums in the actual prime remainder
reduce to the Abel kernel. No distribution hypothesis. -/
lemma finite_lambda_diff (S : Finset ℕ) (w : ℕ → ℝ) (z : ℝ)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, w n / (n : ℝ)) -
      (∑ n ∈ S, w n / (n : ℝ) * (n : ℝ)) / z =
      ∑ n ∈ S, w n * (1/(n : ℝ) - 1/z) := by
  have hc : (∑ n ∈ S, w n / (n : ℝ) * (n : ℝ)) = ∑ n ∈ S, w n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hS n hn))
    exact div_mul_cancel₀ _ hn0
  rw [hc, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The floor cutoff is exactly the finite filter for the step
function on the real interval. -/
lemma floor_cutoff_filter (t z : ℝ) (ht : 0 ≤ t) (htz : t ≤ z) :
    ((Finset.Icc 1 ⌊z⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t)) =
      Finset.Icc 1 ⌊t⌋₊ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [← Nat.le_floor_iff ht]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1,h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨⟨h1,h2.trans (Nat.floor_mono htz)⟩,h2⟩

/-- Inside the integration interval the sum of weighted jump
indicators is precisely the cumulative arithmetic sum times the kernel. -/
lemma cumulative_kernel_eq (w : ℕ → ℝ) (t z : ℝ)
    (ht : 1 ≤ t) (htz : t ≤ z) :
    (∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
      (Set.Icc (n : ℝ) z).indicator (fun t => w n * t ^ (-2 : ℝ)) t) =
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, w n) * t ^ (-2 : ℝ) := by
  classical
  rw [← floor_cutoff_filter t z (by linarith) htz, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : (n : ℝ) ≤ t
  · simp [Set.indicator, Set.mem_Icc, h, htz]
  · simp [Set.indicator, Set.mem_Icc, h]

#print axioms finite_lambda_diff
#print axioms floor_cutoff_filter
#print axioms cumulative_kernel_eq
end RFH123S
