import Mathlib

/-!
B2.3 core: use a coarse count of even tuples instead of constructing
pairings. For fixed k a constant k^(2*k) suffices for the stage
application. The arithmetic assumption is a product correlation bound,
not a high-moment assumption. Real coefficients; complex follows
by splitting into real and imaginary parts.
-/
open Finset
noncomputable section
namespace BorghettiRH

def b23Range {α : Type*} [DecidableEq α] {k : ℕ}
    (f : Fin (2*k) → α) : Finset α := univ.image f

theorem b23_even_range_le {α : Type*} [DecidableEq α] (k : ℕ)
    (f : Fin (2*k) → α)
    (he : ∀ a : α, Even ((univ.filter (fun i => f i = a)).card)) :
    (b23Range f).card ≤ k := by
  classical
  let s := b23Range f
  have hs : ∀ a ∈ s, 2 ≤ (univ.filter (fun i => f i = a)).card := by
    intro a ha
    obtain ⟨i, hi, hia⟩ := mem_image.mp ha
    have hp : 0 < (univ.filter (fun j => f j = a)).card :=
      card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hia⟩⟩
    obtain ⟨r, hr⟩ := he a
    omega
  have hsum := sum_card_fiberwise_eq_card_filter
    (univ : Finset (Fin (2*k))) s f
  have hfilter : univ.filter (fun i => f i ∈ s) =
      (univ : Finset (Fin (2*k))) := by
    ext i
    simp [s, b23Range]
  rw [hfilter] at hsum
  have hle : 2 * s.card ≤ ∑ a ∈ s,
      (univ.filter (fun i => f i = a)).card := by
    calc
      _ = ∑ _a ∈ s, (2 : ℕ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hs
  have htotal : (∑ a ∈ s, (univ.filter (fun i => f i = a)).card) = 2*k := by
    simpa using hsum
  rw [htotal] at hle
  change s.card ≤ k
  omega

/-- Encode a tuple with at most k distinct values by k labels and a
map from its 2k positions to those labels. This bounds the even tuples
without needing to enumerate matchings or prove the exact double factorial. -/
theorem b23_sparse_tuple_count {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (k : ℕ) :
    ((univ : Finset (Fin (2*k) → α)).filter
      (fun f => (b23Range f).card ≤ k)).card ≤
        k ^ (2*k) * (Fintype.card α) ^ k := by
  classical
  let enc : ((Fin (2*k) → Fin k) × (Fin k → α)) → (Fin (2*k) → α) :=
    fun uv i => uv.2 (uv.1 i)
  have hsub : ((univ : Finset (Fin (2*k) → α)).filter
      (fun f => (b23Range f).card ≤ k)) ⊆ univ.image enc := by
    intro f hf
    let s := b23Range f
    have hk : s.card ≤ k := (mem_filter.mp hf).2
    let e := s.equivFin
    let r : Fin (2*k) → s := fun i =>
      ⟨f i, mem_image_of_mem f (mem_univ i)⟩
    let u : Fin (2*k) → Fin k := fun i =>
      ⟨(e (r i)).val, (e (r i)).isLt.trans_le hk⟩
    let v : Fin k → α := fun j =>
      if hj : j.val < s.card then (e.symm ⟨j.val, hj⟩).val
      else Classical.choice (inferInstance : Nonempty α)
    apply mem_image.mpr
    refine ⟨(u,v), mem_univ _, ?_⟩
    funext i
    have hlt : (u i).val < s.card := (e (r i)).isLt
    change v (u i) = f i
    simp only [v, dif_pos hlt]
    have heq : (⟨(u i).val, hlt⟩ : Fin s.card) = e (r i) :=
      Fin.ext rfl
    rw [heq, e.symm_apply_apply]
  calc
    _ ≤ (univ.image enc).card := card_le_card hsub
    _ ≤ (univ : Finset ((Fin (2*k) → Fin k) × (Fin k → α))).card :=
      card_image_le
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fun]

theorem b23_even_tuple_count {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (k : ℕ) :
    ((univ : Finset (Fin (2*k) → α)).filter (fun f =>
      ∀ a : α, Even ((univ.filter (fun i => f i = a)).card))).card ≤
        k ^ (2*k) * (Fintype.card α) ^ k := by
  classical
  have hsub : ((univ : Finset (Fin (2*k) → α)).filter (fun f =>
      ∀ a : α, Even ((univ.filter (fun i => f i = a)).card))) ⊆
      univ.filter (fun f : Fin (2*k) → α => (b23Range f).card ≤ k) := by
    intro f hf
    exact mem_filter.mpr ⟨mem_univ _, b23_even_range_le k f (mem_filter.mp hf).2⟩
  exact (card_le_card hsub).trans (b23_sparse_tuple_count k)

/-- Finite real moment expansion with arbitrary correlations. -/
theorem b23_moment_expand {α β : Type*} [Fintype α]
    (P : Finset β) (a : α → ℝ) (χ : β → α → ℝ) (r : ℕ) :
    (∑ q ∈ P, (∑ p : α, a p * χ q p)^r) =
      ∑ f : Fin r → α, (∏ i, a (f i)) *
        (∑ q ∈ P, ∏ i, χ q (f i)) := by
  classical
  calc
    _ = ∑ q ∈ P, ∑ f : Fin r → α, ∏ i, a (f i) * χ q (f i) := by
      apply sum_congr rfl
      intro q hq
      exact Fintype.sum_pow (f := fun p : α => a p * χ q p) r
    _ = _ := by
      simp_rw [prod_mul_distrib]
      rw [sum_comm]
      apply sum_congr rfl
      intro f hf
      rw [mul_sum]

#print axioms BorghettiRH.b23_even_range_le
#print axioms BorghettiRH.b23_sparse_tuple_count
#print axioms BorghettiRH.b23_even_tuple_count
#print axioms BorghettiRH.b23_moment_expand
end BorghettiRH
