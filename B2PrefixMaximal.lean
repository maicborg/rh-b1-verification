import Mathlib

/-!
B2.2: elementary finite maximal inequality, independent of Alpoge.
Direction: Maicol Borghetti. Formalization: GPT-6.2.
The interval second moment is an explicit input. No assertion about
Dirichlet characters or RH is made in this module.
-/
open Finset
noncomputable section
namespace BorghettiRH

def prefixSum (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, f i

theorem prefix_split (f : ℕ → ℝ) (a b : ℕ) :
    prefixSum f (a+b) = prefixSum f a + prefixSum (fun i => f (a+i)) b := by
  simpa [prefixSum, Nat.add_comm] using (Finset.sum_range_add f a b)

/-- Sum of the squared full sums at every node of a complete binary tree. -/
def prefixTreeEnergy : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => (prefixSum f 1)^2
  | d+1, f => (prefixSum f (2^(d+1)))^2 + prefixTreeEnergy d f +
      prefixTreeEnergy d (fun i => f (2^d+i))

theorem prefixTreeEnergy_nonneg (d : ℕ) (f : ℕ → ℝ) :
    0 ≤ prefixTreeEnergy d f := by
  induction d generalizing f with
  | zero => exact sq_nonneg _
  | succ d ih =>
    simp only [prefixTreeEnergy]
    exact add_nonneg (add_nonneg (sq_nonneg _) (ih f)) (ih _)

/-- Weighted two-block Cauchy inequality. -/
theorem prefix_join_bound (r x y E : ℝ) (hr : 0 < r)
    (hy : y^2 ≤ r*E) : (x+y)^2 ≤ (r+1)*(x^2+E) := by
  have h : 0 ≤ (r*x-y)^2 + (r+1)*(r*E-y^2) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sub_nonneg.mpr hy))
  have he : (r*x-y)^2 + (r+1)*(r*E-y^2) =
      r*((r+1)*(x^2+E)-(x+y)^2) := by ring
  rw [he] at h
  by_contra! hn
  exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hr (sub_neg.mpr hn))

/-- Every prefix uses at most one completed block per tree level. -/
theorem prefixTreeEnergy_root (d : ℕ) (f : ℕ → ℝ) :
    (prefixSum f (2^d))^2 ≤ prefixTreeEnergy d f := by
  cases d with
  | zero => simp [prefixTreeEnergy]
  | succ d =>
    simp only [prefixTreeEnergy]
    have h1 := prefixTreeEnergy_nonneg d f
    have h2 := prefixTreeEnergy_nonneg d (fun i => f (2^d+i))
    linarith

theorem prefix_tree_bound (d : ℕ) (f : ℕ → ℝ) (k : ℕ)
    (hk : k ≤ 2^d) :
    (prefixSum f k)^2 ≤ ((d:ℝ)+1)*prefixTreeEnergy d f := by
  induction d generalizing f k with
  | zero =>
    simp only [pow_zero] at hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl
    · simp [prefixSum, prefixTreeEnergy, sq_nonneg]
    · simp [prefixTreeEnergy]
  | succ d ih =>
    have hL := prefixTreeEnergy_nonneg d f
    have hR := prefixTreeEnergy_nonneg d (fun i => f (2^d+i))
    have hT := prefixTreeEnergy_nonneg (d+1) f
    have hroot : 0 ≤ (prefixSum f (2^(d+1)))^2 := sq_nonneg _
    by_cases h : k ≤ 2^d
    · have hle : prefixTreeEnergy d f ≤ prefixTreeEnergy (d+1) f := by
        simp only [prefixTreeEnergy]
        linarith
      calc
        _ ≤ ((d:ℝ)+1)*prefixTreeEnergy d f := ih f k h
        _ ≤ ((d:ℝ)+1)*prefixTreeEnergy (d+1) f :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ (((d+1:ℕ):ℝ)+1)*prefixTreeEnergy (d+1) f := by
          apply mul_le_mul_of_nonneg_right _ hT
          push_cast
          linarith
    · have hk' : k-2^d ≤ 2^d := by
        rw [pow_succ, Nat.mul_two] at hk
        omega
      have hke : 2^d+(k-2^d) = k := by omega
      have he : prefixSum f k = prefixSum f (2^d) +
          prefixSum (fun i => f (2^d+i)) (k-2^d) := by
        calc
          _ = prefixSum f (2^d+(k-2^d)) := by rw [hke]
          _ = _ := prefix_split f _ _
      have hy := ih (fun i => f (2^d+i)) (k-2^d) hk'
      have hfull := prefixTreeEnergy_root d f
      have hle : (prefixSum f (2^d))^2 +
          prefixTreeEnergy d (fun i => f (2^d+i)) ≤ prefixTreeEnergy (d+1) f := by
        simp only [prefixTreeEnergy]
        linarith
      rw [he]
      calc
        _ ≤ ((d:ℝ)+1+1)*((prefixSum f (2^d))^2 +
            prefixTreeEnergy d (fun i => f (2^d+i))) :=
          prefix_join_bound ((d:ℝ)+1) _ _ _ (by positivity) hy
        _ ≤ ((d:ℝ)+1+1)*prefixTreeEnergy (d+1) f :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ = _ := by push_cast; ring

/-- One possibly uncontrolled unordered pair costs at most one diagonal budget. -/
theorem exceptional_pair_absorb (a b D E : ℝ)
    (h : a^2+b^2 ≤ D) :
    D + E + 2 * |a| * |b| ≤ 2 * D + E := by
  have hs := sq_nonneg (|a|-|b|)
  nlinarith [sq_abs a, sq_abs b]

/-- Arbitrarily chosen prefix per sample, using the sum of tree energies. -/
theorem prefix_selected_bound {α : Type*} (P : Finset α)
    (f : α → ℕ → ℝ) (d : ℕ) (k : α → ℕ)
    (hk : ∀ q ∈ P, k q ≤ 2^d) :
    (∑ q ∈ P, (prefixSum (f q) (k q))^2) ≤
      ((d:ℝ)+1)*(∑ q ∈ P, prefixTreeEnergy d (f q)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun q hq => prefix_tree_bound d (f q) (k q) (hk q hq)

#print axioms BorghettiRH.prefix_split
#print axioms BorghettiRH.prefix_join_bound
#print axioms BorghettiRH.prefix_tree_bound
#print axioms BorghettiRH.exceptional_pair_absorb
#print axioms BorghettiRH.prefix_selected_bound
end BorghettiRH
