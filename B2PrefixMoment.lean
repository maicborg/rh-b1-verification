import B2PrefixMaximal

/-!
The deterministic prefix-tree lemma gives a finite maximal second moment
from the interval second moment. The sample may choose a DIFFERENT prefix
at each point. This is the discrete Rademacher–Menshov mechanism, not RH.
Direction: Maicol Borghetti. Formalization: GPT-6.2.
-/
open Finset
noncomputable section
namespace BorghettiRH

theorem prefix_tree_moment {α : Type*} (P : Finset α)
    (f : α → ℕ → ℝ) (w : ℕ → ℝ) (D : ℝ)
    (h : ∀ a n : ℕ,
      (∑ q ∈ P, (prefixSum (fun i => f q (a+i)) n)^2) ≤
        D*prefixSum (fun i => w (a+i)) n)
    (d a : ℕ) :
    (∑ q ∈ P, prefixTreeEnergy d (fun i => f q (a+i))) ≤
      ((d:ℝ)+1)*D*prefixSum (fun i => w (a+i)) (2^d) := by
  induction d generalizing a with
  | zero =>
    simpa [prefixTreeEnergy] using h a 1
  | succ d ih =>
    have hroot := h a (2^(d+1))
    have hl := ih a
    have hr := ih (a+2^d)
    have hs : prefixSum (fun i => w (a+i)) (2^(d+1)) =
        prefixSum (fun i => w (a+i)) (2^d) +
        prefixSum (fun i => w ((a+2^d)+i)) (2^d) := by
      rw [pow_succ, Nat.mul_two, prefix_split]
      simp only [Nat.add_assoc]
    simp only [prefixTreeEnergy, Finset.sum_add_distrib, ← Nat.add_assoc, Nat.cast_succ]
    calc
      _ ≤ D*prefixSum (fun i => w (a+i)) (2^(d+1)) +
          ((d:ℝ)+1)*D*prefixSum (fun i => w (a+i)) (2^d) +
          ((d:ℝ)+1)*D*prefixSum (fun i => w ((a+2^d)+i)) (2^d) :=
        add_le_add (add_le_add hroot hl) hr
      _ = _ := by rw [hs]; ring

/-- A maximal bound with logarithmic-squared overhead.
    A sample-dependent maximizer is allowed; there is no union bound over prefixes.
    The interval second moment remains an explicit assumption. -/
theorem prefix_maximal_moment {α : Type*} (P : Finset α)
    (f : α → ℕ → ℝ) (w : ℕ → ℝ) (D : ℝ)
    (h : ∀ a n : ℕ,
      (∑ q ∈ P, (prefixSum (fun i => f q (a+i)) n)^2) ≤
        D*prefixSum (fun i => w (a+i)) n)
    (d : ℕ) (k : α → ℕ) (hk : ∀ q ∈ P, k q ≤ 2^d) :
    (∑ q ∈ P, (prefixSum (f q) (k q))^2) ≤
      ((d:ℝ)+1)^2*D*prefixSum w (2^d) := by
  have he := prefix_tree_moment P f w D h d 0
  simp only [zero_add] at he
  calc
    _ ≤ ((d:ℝ)+1)*(∑ q ∈ P, prefixTreeEnergy d (f q)) :=
      prefix_selected_bound P f d k hk
    _ ≤ ((d:ℝ)+1)*(((d:ℝ)+1)*D*prefixSum w (2^d)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

#print axioms BorghettiRH.prefix_tree_moment
#print axioms BorghettiRH.prefix_maximal_moment
end BorghettiRH
