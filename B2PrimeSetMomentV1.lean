import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentActualV1
import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentLastMileV1

/-! Actual finite prime-set moment with the error absorbed. No abstract
correlation input. The remaining scale and log inequalities are explicit. -/
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section
namespace QH
open BorghettiRH

theorem b23_prime_set_moment :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a N k T : ℕ),
      admitted ε Y U m a →
      (∀ q ∈ PPset m a U, q.Prime ∧ q % m = a % m ∧ N^2 < q) →
      (N : ℝ) ≤ Y^A → T^(2*k) ≤ N →
      (∀ q ∈ PPset m a U, T < q) →
      Y^(-B)*(T : ℝ)^k ≤ 1 →
      ∀ (s : Finset ℕ) (c : ℕ → ℂ) (L : ℝ),
        (∀ p ∈ s, p.Prime ∧ ¬ p ∣ m ∧ p ≤ T) →
        s.card ≤ T → 0 ≤ L → (∀ p ∈ s, ‖c p‖ ≤ L) →
        (∑ q ∈ PPset m a U, ‖∑ p ∈ s, c p *
          ((jacobiSym (p : ℤ) q : ℤ) : ℂ)‖^(2*k)) ≤
          (2 : ℝ)^(k+1) * (L^(2*k) * ((PPset m a U).card : ℝ) *
            (((k : ℝ)^(2*k)+1)*(T : ℝ)^k)) := by
  intro ε A B hε hA hB
  obtain ⟨Ybase, hbase⟩ := b23_jacobi_prime_product_moment ε A B hε hA hB
  refine ⟨max Ybase 1, ?_⟩
  intro Y hY U m a N k T hAd hP hN hTN hTq hsmall s c L hs hcard hL hc
  classical
  have hYbase : Ybase ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 ≤ Y := by linarith [le_trans (le_max_right Ybase (1 : ℝ)) hY]
  by_cases hempty : s.Nonempty
  · letI : Nonempty ↥s := ⟨⟨hempty.choose, hempty.choose_spec⟩⟩
    have hprod : ∀ f : Fin (2*k) → ↥s, (∏ i, (f i : ℕ)) ≤ N := by
      intro f
      calc
        _ ≤ ∏ _i : Fin (2*k), T :=
          prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun i _ => (hs (f i) (f i).property).2.2)
        _ = T^(2*k) := by simp
        _ ≤ N := hTN
    have hm := hbase Y hYbase U m a N k hAd hP (↥s)
      (fun i => (i : ℕ)) (fun i => c i) L
      (fun i => (hs i i.property).1) Subtype.val_injective
      (fun i => (hs i i.property).2.1)
      (fun q hq i => lt_of_le_of_lt (hs i i.property).2.2 (hTq q hq))
      hprod hN hL (fun i => hc i i.property)
    have hu : (univ : Finset ↥s) = s.attach := by ext i; simp
    have hsum (q : ℕ) :
        (∑ i : ↥s, c i * ((jacobiSym ((i : ℕ) : ℤ) q : ℤ) : ℂ)) =
        ∑ p ∈ s, c p * ((jacobiSym (p : ℤ) q : ℤ) : ℂ) := by
      rw [hu, Finset.sum_attach]
    simp_rw [hsum] at hm
    simp only [Fintype.card_coe, Nat.cast_mul, Nat.cast_pow] at hm
    have hn : (s.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hcard
    have hnk : (s.card : ℝ)^k ≤ (T : ℝ)^k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hn k
    have hns : Y^(-B)*(s.card : ℝ)^k ≤ 1 :=
      (mul_le_mul_of_nonneg_left hnk (Real.rpow_nonneg hY0 _)).trans hsmall
    have habs := b23_moment_error_absorb (s.card : ℝ) (Y^(-B))
      ((k : ℝ)^(2*k)) k (Nat.cast_nonneg _) hns
    have hscale := habs.trans
      (mul_le_mul_of_nonneg_left hnk (show 0 ≤ (k : ℝ)^(2*k)+1 by positivity))
    exact hm.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hscale (by positivity)) (by positivity))
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst s
    by_cases hk : k = 0
    · subst k
      simp
      positivity
    · have h2k : 2*k ≠ 0 := by omega
      simp [h2k, zero_pow h2k]
      positivity

#print axioms QH.b23_prime_set_moment
end QH
