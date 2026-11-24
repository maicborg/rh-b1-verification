import Mathlib

/-!
B2.3 (candidate) -- a finite moment-to-uniform-exception lemma.

This is the discrete union-bound step for the alternative HIGH MOMENT
route from the verified OpenAI/Alpoge all-odd twistK to the exact S-bound
used by QH.stage. It does not import a maximal inequality, measure
theory, or the Alpoge mean-square/BadShare proof.

The arithmetical 2k-th moment estimate is an EXPLICIT INPUT, not an
axiom of the program and not yet formalized here. Its intended proof
uses squarefree products of at most 2k primes and even multiplicity
pairings. This file is only the abstract finite tail/union bridge.

Direction: Maicol Borghetti, UNO-DUE-TRE.
RH0 formalization, 2026-11-24.
-/

open Finset

namespace BorghettiRH

/-- Count exceptional samples by an arbitrary positive threshold
and a finite power moment. No probability-space normalization needed. -/
theorem b2_highmoment_count {α : Type*} (P B : Finset α)
    (f : α → ℝ) (u M : ℝ) (r : ℕ)
    (hB : B ⊆ P)
    (hf : ∀ q ∈ P, 0 ≤ f q)
    (hu : 0 < u)
    (hbad : ∀ q ∈ B, u ≤ f q)
    (hmoment : (∑ q ∈ P, f q ^ r) ≤ u ^ r * M) :
    (B.card : ℝ) ≤ M := by
  have hlow : u ^ r * (B.card : ℝ) ≤ ∑ q ∈ B, f q ^ r := by
    calc
      _ = ∑ _q ∈ B, u ^ r := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun q hq =>
        pow_le_pow_left₀ hu.le (hbad q hq) r)
  have hsub : (∑ q ∈ B, f q ^ r) ≤ ∑ q ∈ P, f q ^ r :=
    Finset.sum_le_sum_of_subset_of_nonneg hB
      (fun q hq _ => pow_nonneg (hf q hq) r)
  exact le_of_mul_le_mul_left
    (hlow.trans (hsub.trans hmoment)) (pow_pos hu r)

/-- Every bad sample may choose its own exceptional scale. Summing
a high-moment tail budget over scales controls the full exceptional set.
This is a finite elementary alternative to the maximal-tree route. -/
theorem b2_highmoment_uniform_bad
    {α β : Type*} (P B : Finset α) (T : Finset β)
    (f : α → β → ℝ) (u M : β → ℝ) (r : ℕ)
    (hB : B ⊆ P)
    (hf : ∀ q ∈ P, ∀ t ∈ T, 0 ≤ f q t)
    (hu : ∀ t ∈ T, 0 < u t)
    (hbad : ∀ q ∈ B, ∃ t ∈ T, u t ≤ f q t)
    (hmoment : ∀ t ∈ T,
      (∑ q ∈ P, f q t ^ r) ≤ u t ^ r * M t) :
    (B.card : ℝ) ≤ ∑ t ∈ T, M t := by
  classical
  let E : β → Finset α := fun t => P.filter (fun q => u t ≤ f q t)
  have hcover : B ⊆ T.biUnion E := by
    intro q hq
    obtain ⟨t, ht, hqt⟩ := hbad q hq
    exact Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_filter.mpr ⟨hB hq, hqt⟩⟩
  have hcount : ∀ t ∈ T, ((E t).card : ℝ) ≤ M t := by
    intro t ht
    exact b2_highmoment_count P (E t) (fun q => f q t)
      (u t) (M t) r
      (Finset.filter_subset _ _)
      (fun q hq => hf q hq t ht) (hu t ht)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (hmoment t ht)
  calc
    (B.card : ℝ) ≤ ((T.biUnion E).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ t ∈ T, ((E t).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ t ∈ T, M t := Finset.sum_le_sum hcount

#print axioms BorghettiRH.b2_highmoment_count
#print axioms BorghettiRH.b2_highmoment_uniform_bad

end BorghettiRH
