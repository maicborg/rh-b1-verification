import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentCoreV1

open Finset
noncomputable section
namespace BorghettiRH

/-- Arbitrary-order real moments from bounded coefficients and small
correlations for tuples with more than k distinct entries. The latter
tuples necessarily have some odd multiplicity, by b23_even_range_le.
No high-moment estimate is assumed. -/
theorem b23_real_high_moment {α β : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (P : Finset β) (a : α → ℝ) (χ : β → α → ℝ)
    (k : ℕ) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (ha : ∀ p, |a p| ≤ L)
    (hχ : ∀ q ∈ P, ∀ p, |χ q p| ≤ 1)
    (hcorr : ∀ f : Fin (2*k) → α, k < (b23Range f).card →
      |∑ q ∈ P, ∏ i, χ q (f i)| ≤ δ * (P.card : ℝ)) :
    (∑ q ∈ P, (∑ p : α, a p * χ q p)^(2*k)) ≤
      L^(2*k) * (P.card : ℝ) *
        (((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ) +
          δ * ((Fintype.card α)^(2*k) : ℕ)) := by
  classical
  let G : Finset (Fin (2*k) → α) :=
    univ.filter (fun f => (b23Range f).card ≤ k)
  let H : Finset (Fin (2*k) → α) :=
    univ.filter (fun f => ¬ (b23Range f).card ≤ k)
  let b : (Fin (2*k) → α) → ℝ :=
    fun f => (∏ i, a (f i)) * (∑ q ∈ P, ∏ i, χ q (f i))
  have ha' (f : Fin (2*k) → α) : |∏ i, a (f i)| ≤ L^(2*k) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin (2*k), L :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => ha (f i))
      _ = _ := by simp
  have htriv (f : Fin (2*k) → α) :
      |∑ q ∈ P, ∏ i, χ q (f i)| ≤ (P.card : ℝ) := by
    calc
      _ ≤ ∑ q ∈ P, |∏ i, χ q (f i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ P, (1 : ℝ) := by
        apply sum_le_sum
        intro q hq
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _i : Fin (2*k), (1 : ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hχ q hq (f i))
          _ = _ := by simp
      _ = _ := by simp
  have hG : (∑ f ∈ G, b f) ≤ (G.card : ℝ) * (L^(2*k) * (P.card : ℝ)) := by
    calc
      _ ≤ ∑ _f ∈ G, L^(2*k) * (P.card : ℝ) := by
        apply sum_le_sum
        intro f hf
        calc
          b f ≤ |b f| := le_abs_self _
          _ = |∏ i, a (f i)| * |∑ q ∈ P, ∏ i, χ q (f i)| := abs_mul _ _
          _ ≤ _ := mul_le_mul (ha' f) (htriv f) (abs_nonneg _) (pow_nonneg hL _)
      _ = _ := by simp [mul_comm]
  have hH : (∑ f ∈ H, b f) ≤ (H.card : ℝ) * (L^(2*k) * (δ * (P.card : ℝ))) := by
    calc
      _ ≤ ∑ _f ∈ H, L^(2*k) * (δ * (P.card : ℝ)) := by
        apply sum_le_sum
        intro f hf
        have h := hcorr f (lt_of_not_ge (mem_filter.mp hf).2)
        calc
          b f ≤ |b f| := le_abs_self _
          _ = |∏ i, a (f i)| * |∑ q ∈ P, ∏ i, χ q (f i)| := abs_mul _ _
          _ ≤ _ := mul_le_mul (ha' f) h (abs_nonneg _) (pow_nonneg hL _)
      _ = _ := by simp [mul_comm]
  have hg : (G.card : ℝ) ≤ ((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ) := by
    exact_mod_cast (b23_sparse_tuple_count (α := α) k)
  have hh : (H.card : ℝ) ≤ (((Fintype.card α)^(2*k) : ℕ) : ℝ) := by
    have hn := card_filter_le (s := (univ : Finset (Fin (2*k) → α)))
      (fun f => ¬ (b23Range f).card ≤ k)
    exact_mod_cast (show H.card ≤ (Fintype.card α)^(2*k) from by
      simpa [H, Fintype.card_fun] using hn)
  rw [b23_moment_expand P a χ (2*k)]
  change (∑ f, b f) ≤ _
  rw [← sum_filter_add_sum_filter_not univ (fun f => (b23Range f).card ≤ k) b]
  change (∑ f ∈ G, b f) + (∑ f ∈ H, b f) ≤ _
  calc
    _ ≤ (G.card : ℝ) * (L^(2*k) * (P.card : ℝ)) +
          (H.card : ℝ) * (L^(2*k) * (δ * (P.card : ℝ))) := add_le_add hG hH
    _ ≤ _ := by
      calc
        _ ≤ (((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ)) *
              (L^(2*k) * (P.card : ℝ)) +
              (((Fintype.card α)^(2*k) : ℕ) : ℝ) *
                (L^(2*k) * (δ * (P.card : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_right hg (by positivity))
            (mul_le_mul_of_nonneg_right hh (by positivity))
        _ = _ := by ring

#print axioms BorghettiRH.b23_real_high_moment
end BorghettiRH
