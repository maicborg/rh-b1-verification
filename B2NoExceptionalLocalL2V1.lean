import Development.AutomorphicArithmetic.MeanSquareBounds.B2IntervalLocalEnergyV1

/-!
B2.2 -- Direct interval second moment with NO exceptional pair.

The original Alpoge's meansq_split is invoked with nstar=1, so its
two exceptional contributions coincide with the diagonal; BOTH are
bounded by pairs_one. Consequently the correction 2*W^2 vanishes,
and the remaining bound is local in the interval cardinality.

Uses genuine OpenAI 7/8 no-exception twistK via QH.b2_actual_twistK_all_odd.
Not yet a maximal or stage theorem. Direction: Maicol Borghetti.
Formalization: GPT-6.
-/

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section

namespace QH

set_option maxHeartbeats 2000000 in
theorem b2_weighted_meanSq_abs_noexception
    (P : Finset ℕ) (m a N : ℕ) (η : ℝ)
    (c : ℕ → ℝ) (κ : ℕ → ℂ)
    (h8 : 8 ∣ m) (hcop : a.Coprime m)
    (hc : ∀ n, 0 ≤ c n)
    (hpp : ∀ n, c n ≠ 0 → IsPrimePow n)
    (hη : 0 ≤ η)
    (hP : ∀ q ∈ P, q.Prime ∧ q % m = a % m ∧ N ^ 2 < q)
    (hκ : ∀ n, ‖κ n‖ ≤ 1)
    (hJ : ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
      s.Coprime m → s ≤ N ^ 2 →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) :
    (∑ q ∈ P, ‖∑ n ∈ Icc 1 N,
      ((c n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      (2 * ((∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
        RR c m N ^ 2) +
        η * (∑ n ∈ Icc 1 N, c n) ^ 2) * P.card := by
  have hexp := meansq_expand P (Icc 1 N) c hc κ hκ
    (fun n q => jacobiSym (n : ℤ) q)
  have hpair : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      |∑ q ∈ P,
        ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ P,
        (jacobiSym (q : ℤ) (soutPart m (n * n')) : ℝ)| := by
    intro n hn n' hn'
    rw [Finset.mem_Icc] at hn hn'
    refine abs_pair_sum_eq P m a n n' h8 hcop (by omega) (by omega) ?_
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hP q hq
    refine ⟨h1, h2, lt_of_le_of_lt ?_ h3⟩
    rw [pow_two]
    exact Nat.mul_le_mul hn.2 hn'.2
  have hsplit := meansq_split (Icc 1 N) c hc
    (fun n n' => soutPart m (n * n'))
    (fun n n' =>
      |∑ q ∈ P,
        ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|)
    (P.card : ℝ) η (by positivity) hη 1
    (by
      intro n hn n' hn'
      rw [hpair n hn n' hn']
      exact abs_sum_jacobi_le P _)
    (by
      intro n hn n' hn' hr1 _
      rw [hpair n hn n' hn']
      rw [Finset.mem_Icc] at hn hn'
      have hnn : 0 < n * n' := Nat.mul_pos (by omega) (by omega)
      have hle : soutPart m (n * n') ≤ N ^ 2 := by
        refine (soutPart_le m _ hnn).trans ?_
        rw [pow_two]
        exact Nat.mul_le_mul hn.2 hn'.2
      exact hJ _ (by have h := soutPart_pos m (n*n'); omega)
        (soutPart_odd m _ (dvd_trans (by norm_num) h8))
        (soutPart_squarefree m _)
        (soutPart_coprime m _) hle)
  beta_reduce at hsplit
  have hdiag := pairs_one c hc hpp m N
  refine hexp.trans (hsplit.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
theorem b2_interval_local_L2_from_twistK :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
        ∀ (U : ℝ) (m a N : ℕ) (x : ℝ) (I : Finset ℕ)
          (c : ℕ → ℝ) (κ : ℕ → ℂ) (L : ℝ),
        admitted ε Y U m a →
        (∀ q ∈ PPset m a U,
          q.Prime ∧ q % m = a % m ∧ N ^ 2 < q) →
        (N : ℝ) ^ 2 ≤ Y ^ A →
        Real.exp 1 ≤ x →
        N ≤ ⌊x ^ 400⌋₊ →
        (∀ n, 0 ≤ c n) →
        (∀ n, c n ≤ cN x n) →
        (∀ n, IsPrimePow n →
          (Even (n.factorization n.minFac) ∨ n.minFac ∣ m) → c n = 0) →
        I ⊆ Icc 1 N →
        (∀ n ∈ Icc 1 N, n ∉ I → c n = 0) →
        (∀ n ∈ I, c n ≤ L) →
        (∀ n, ‖κ n‖ ≤ 1) →
        (∑ q ∈ PPset m a U, ‖∑ n ∈ Icc 1 N,
          ((c n : ℝ) : ℂ) * κ n *
            ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
          (2 * (801 * Real.log x * L * (I.card : ℝ)) +
            Y ^ (-B) * (∑ n ∈ Icc 1 N, c n) ^ 2) *
            ((PPset m a U).card : ℝ) := by
  intro ε A B hε hA hB
  obtain ⟨Ybase, hbase⟩ := b2_actual_twistK_all_odd ε A B hε hA hB
  refine ⟨max Ybase 2, ?_⟩
  intro Y hY U m a N x I c κ L hAd hP hN2 hx hNx
    hc hdom hodd hI hout hL hκ
  have hYbase : Ybase ≤ Y := (le_max_left _ _).trans hY
  have hYnonneg : 0 ≤ Y := by
    have h2 : (2 : ℝ) ≤ Y := (le_max_right _ _).trans hY
    linarith
  have hδ : 0 ≤ Y ^ (-B) := Real.rpow_nonneg hYnonneg _
  have hJ : ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
      s.Coprime m → s ≤ N ^ 2 →
        |∑ q ∈ PPset m a U,
          (jacobiSym (q : ℤ) s : ℝ)| ≤
          Y ^ (-B) * ((PPset m a U).card : ℝ) := by
    intro s hs ho hsq hcop hsN
    have hsn : (s : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hsN
    exact hbase Y hYbase U m a hAd s hs ho hsq hcop (hsn.trans hN2)
  have hpp : ∀ n, c n ≠ 0 → IsPrimePow n :=
    b2_dominated_primepower_support x c hc hdom
  have hmain := b2_weighted_meanSq_abs_noexception
    (PPset m a U) m a N (Y ^ (-B)) c κ
    hAd.eight hAd.coprime hc hpp hδ hP hκ hJ
  have hRR : RR c m N = 0 := b2_RR_zero_of_odd_primepowers c m N hodd
  have hdiag :
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
        801 * Real.log x * L * (I.card : ℝ) :=
    b2_interval_local_energy_801 x hx N hNx I L c hc hdom hI hout hL
  refine hmain.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [hRR]
  nlinarith

#print axioms QH.b2_weighted_meanSq_abs_noexception
#print axioms QH.b2_interval_local_L2_from_twistK
end QH
