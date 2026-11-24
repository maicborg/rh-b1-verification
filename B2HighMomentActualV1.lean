import Development.AutomorphicArithmetic.MeanSquareBounds.B2HighMomentComplexV1
import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiProductCorrelationV1

/-! B2.3: eliminate the abstract correlation hypothesis for actual
prime products, by unique factorization and the certified all-odd twist.
The analytic sizes/admitted specialization and Abel are separate. -/
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section
namespace QH
open BorghettiRH

theorem b23_prime_tuple_factorization {α : Type*} [DecidableEq α]
    (k : ℕ) (p : α → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (f : Fin (2*k) → α) (a : α) :
    (∏ i, p (f i)).factorization (p a) =
      (univ.filter (fun i => f i = a)).card := by
  classical
  rw [Nat.factorization_prod_apply (fun i _ => (hp (f i)).ne_zero)]
  calc
    _ = ∑ i : Fin (2*k), if f i = a then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [(hp (f i)).factorization, Finsupp.single_apply]
      by_cases h : f i = a
      · simp [h]
      · have h' : p (f i) ≠ p a := fun he => h (hinj he)
        simp [h, h', Ne.symm h']
    _ = _ := by rw [card_eq_sum_ones, sum_filter]

theorem b23_soutPart_nontrivial {α : Type*} [DecidableEq α]
    (k m : ℕ) (p : α → ℕ) (hp : ∀ a, (p a).Prime)
    (hinj : Function.Injective p) (hpm : ∀ a, ¬ p a ∣ m)
    (f : Fin (2*k) → α) (hf : k < (b23Range f).card) :
    1 < soutPart m (∏ i, p (f i)) := by
  classical
  let n : ℕ := ∏ i, p (f i)
  have hex : ∃ a : α, ¬ Even ((univ.filter (fun i => f i = a)).card) := by
    by_contra! hall
    exact (not_lt_of_ge (b23_even_range_le k f hall)) hf
  obtain ⟨a, ha⟩ := hex
  have hfac : n.factorization (p a) = (univ.filter (fun i => f i = a)).card :=
    b23_prime_tuple_factorization k p hp hinj f a
  have ho : Odd (n.factorization (p a)) := by
    rw [hfac]
    exact Nat.not_even_iff_odd.mp ha
  have hnz : n.factorization (p a) ≠ 0 := by
    intro h
    rw [h] at ho
    norm_num at ho
  have hmem : p a ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hnz
  have hd : p a ∣ soutPart m n := by
    unfold soutPart
    exact dvd_prod_of_mem id (mem_filter.mpr ⟨hmem, ho, hpm a⟩)
  exact (hp a).one_lt.trans_le (Nat.le_of_dvd (soutPart_pos m n) hd)

theorem b23_jacobi_prime_product_moment :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a N k : ℕ),
        admitted ε Y U m a →
        (∀ q ∈ PPset m a U, q.Prime ∧ q % m = a % m ∧ N^2 < q) →
        ∀ (α : Type) [Fintype α] [Nonempty α] [DecidableEq α]
          (p : α → ℕ) (c : α → ℂ) (L : ℝ),
        (∀ i, (p i).Prime) → Function.Injective p →
        (∀ i, ¬ p i ∣ m) →
        (∀ q ∈ PPset m a U, ∀ i, p i < q) →
        (∀ f : Fin (2*k) → α, (∏ i, p (f i)) ≤ N) →
        (N : ℝ) ≤ Y^A →
        0 ≤ L → (∀ i, ‖c i‖ ≤ L) →
        (∑ q ∈ PPset m a U, ‖∑ i : α, c i *
          ((jacobiSym (p i : ℤ) q : ℤ) : ℂ)‖^(2*k)) ≤
          (2 : ℝ)^(k+1) * (L^(2*k) * ((PPset m a U).card : ℝ) *
            (((k^(2*k) * (Fintype.card α)^k : ℕ) : ℝ) +
              Y^(-B) * ((Fintype.card α)^(2*k) : ℕ))) := by
  intro ε A B hε hA hB
  obtain ⟨Ybase, hbase⟩ := b2_jacobi_pair_average_of_twistK_v1 ε A B hε hA hB
  refine ⟨max Ybase 1, ?_⟩
  intro Y hY U m a N k hAd hP α _ _ _ p c L hp hinj hpm hpq hprod hN hL hc
  classical
  have hYbase : Ybase ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 ≤ Y := by linarith [le_trans (le_max_right Ybase (1 : ℝ)) hY]
  let χ : ℕ → α → ℝ := fun q i => (jacobiSym (p i : ℤ) q : ℝ)
  have hχ : ∀ q ∈ PPset m a U, ∀ i, |χ q i| ≤ 1 := by
    intro q hq i
    rcases jacobiSym.eq_one_or_neg_one (gcd_prime_lt (hp i) (hP q hq).1
      (hpq q hq i)).1 with h | h <;> simp [χ, h]
  have hcorr : ∀ f : Fin (2*k) → α, k < (b23Range f).card →
      |∑ q ∈ PPset m a U, ∏ i, χ q (f i)| ≤
        Y^(-B) * ((PPset m a U).card : ℝ) := by
    intro f hf
    let n : ℕ := ∏ i, p (f i)
    have hn : 0 < n := prod_pos (fun i _ => (hp (f i)).pos)
    have hnN : n ≤ N := hprod f
    have hs : 1 < soutPart m n := b23_soutPart_nontrivial k m p hp hinj hpm f hf
    have hsn : (soutPart m n : ℝ) ≤ Y^A := by
      have hcast : (soutPart m n : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (soutPart_le m n hn).trans hnN
      exact hcast.trans hN
    have h := hbase Y hYbase U m a N n 1 hAd hP hn hnN
      (by norm_num) (by omega) (by simpa only [Nat.mul_one] using hs)
      (by simpa only [Nat.mul_one] using hsn)
    have heq (q : ℕ) : (∏ i, χ q (f i)) = (jacobiSym (n : ℤ) q : ℝ) := by
      dsimp [χ]
      have he : (∏ i, jacobiSym (p (f i) : ℤ) q) = jacobiSym (n : ℤ) q := by
        rw [show (n : ℤ) = ∏ i, (p (f i) : ℤ) by simp [n, Nat.cast_prod],
          jacobiSym_prod_left]
      exact_mod_cast he
    simp_rw [heq]
    simpa only [Nat.cast_one, jacobiSym.one_left, mul_one] using h
  have h := b23_complex_high_moment (PPset m a U) c χ k L (Y^(-B))
    hL (Real.rpow_nonneg hY0 _) hc hχ hcorr
  simpa [χ] using h

#print axioms QH.b23_prime_tuple_factorization
#print axioms QH.b23_soutPart_nontrivial
#print axioms QH.b23_jacobi_prime_product_moment
end QH
