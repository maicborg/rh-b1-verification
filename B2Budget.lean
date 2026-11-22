import Mathlib

/-!
# B₂ budget after eliminating B₁ — conditional counting lemma

Program direction: Maicol Borghetti (@maicborg).
Formalization assisted by GPT-6, 22 November 2026.

THIS IS ONLY A COMBINATORIAL LEMMA. The strong analytic input `hB₂`
is an EXPLICIT ASSUMPTION, not a proof of the mean-square estimate.
It reproduces the final union-bound logic in Alpöge's QH.stage
after the B₁ term has been proved empty by the separate B1 bridge.
-/

namespace BorghettiRH

/--
If B is covered by B₁ and at most R exceptional subsets B₂(ξ),
and B₁ is empty, each B₂ may receive a budget η/(R+1) of |P|
instead of the old η/(2*(R+1)).
The analytic estimate `hB₂` is assumed, not established.
-/
theorem b2_budget_after_b1_empty
    {α : Type*} [DecidableEq α]
    (η : ℝ) (R : ℕ) (P B B₁ : Finset ℕ) (Ξ : Finset α)
    (B₂ : α → Finset ℕ)
    (hη : 0 < η)
    (hB₁ : B₁ = ∅)
    (hcover : B ⊆ B₁ ∪ Ξ.biUnion B₂)
    (hΞ : Ξ.card ≤ R)
    (hB₂ : ∀ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) ≤
        η / ((R : ℝ) + 1) * (P.card : ℝ)) :
    (B.card : ℝ) ≤ η * (P.card : ℝ) := by
  classical
  have hcover' : B ⊆ Ξ.biUnion B₂ := by
    simpa [hB₁] using hcover
  have hR : (Ξ.card : ℝ) ≤ (R : ℝ) + 1 := by
    exact_mod_cast (hΞ.trans (Nat.le_succ R))
  calc
    (B.card : ℝ) ≤ ((Ξ.biUnion B₂).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hcover'
    _ ≤ ∑ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ Ξ.card • (η / ((R : ℝ) + 1) * (P.card : ℝ)) :=
      Finset.sum_le_card_nsmul _ _ _ hB₂
    _ = (Ξ.card : ℝ) * (η / ((R : ℝ) + 1) * (P.card : ℝ)) := by
      rw [nsmul_eq_mul]
    _ ≤ ((R : ℝ) + 1) * (η / ((R : ℝ) + 1) * (P.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    _ = η * (P.card : ℝ) := by
      have hden : (R : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

#print axioms BorghettiRH.b2_budget_after_b1_empty

end BorghettiRH
