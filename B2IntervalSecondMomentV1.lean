import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiPairCorrelationV1

/-!
B2.2: an interval-ready L2 estimate for arbitrary nonnegative coefficients
supported on prime powers. Setting c(n)=Lambda(n)*1_{n in I} specializes
the theorem to any integer interval I (the specialization is NOT yet
formalized). Uses the verified OpenAI 7/8 bound with no excluded modulus.

No MeanSq C Z P A assumption is made, and no BadShare theorem is used.
Next: bound the diagonal prime-power budget by T*polylog(T), then
pass to the finite prefix maximal lemma and to QH.stage.

Direction: Maicol Borghetti. Formalization: GPT-6.
-/
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

set_option maxHeartbeats 2000000 in
theorem b2_weighted_meanSq_abs
    (P : Finset ℕ) (m a nstar N : ℕ) (η W : ℝ)
    (c : ℕ → ℝ) (κ : ℕ → ℂ)
    (h8 : 8 ∣ m) (hcop : a.Coprime m) (hη : 0 ≤ η)
    (hc : ∀ n, 0 ≤ c n)
    (hpp : ∀ n, c n ≠ 0 → IsPrimePow n)
    (hP : ∀ q ∈ P, q.Prime ∧ q % m = a % m ∧ N ^ 2 < q)
    (hκ : ∀ n, ‖κ n‖ ≤ 1)
    (hW : ∀ p, sP c N p ≤ W)
    (hJ : ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
      s.Coprime m → s ≤ N ^ 2 → s ≠ nstar →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) :
    (∑ q ∈ P, ‖∑ n ∈ Icc 1 N,
        ((c n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      ((∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
        RR c m N ^ 2 + (2 * W ^ 2 + 2 * W * RR c m N) +
        η * (∑ n ∈ Icc 1 N, c n) ^ 2) * P.card := by
  have hexp := meansq_expand P (Icc 1 N) c hc κ hκ
    (fun n q => jacobiSym (n : ℤ) q)
  have hpair : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
        |∑ q ∈ P, (jacobiSym (q : ℤ) (soutPart m (n * n')) : ℝ)| := by
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
    (P.card : ℝ) η (by positivity) hη (max nstar 2)
    (by
      intro n hn n' hn'
      rw [hpair n hn n' hn']
      exact abs_sum_jacobi_le P _)
    (by
      intro n hn n' hn' hr1 hrs
      rw [hpair n hn n' hn']
      rw [Finset.mem_Icc] at hn hn'
      have hpos := soutPart_pos m (n * n')
      have hnn : 0 < n * n' := Nat.mul_pos (by omega) (by omega)
      have hle : soutPart m (n * n') ≤ N ^ 2 := by
        refine (soutPart_le m _ hnn).trans ?_
        rw [pow_two]
        exact Nat.mul_le_mul hn.2 hn'.2
      refine hJ _ (by omega) (soutPart_odd m _ (dvd_trans (by norm_num) h8))
        (soutPart_squarefree m _) (soutPart_coprime m _) hle ?_
      intro h
      apply hrs
      omega)
  beta_reduce at hsplit
  have h1 := pairs_one c hc hpp m N
  have h2 := pairs_r c hc hpp m N (max nstar 2) (by omega) W hW
  refine hexp.trans (hsplit.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
theorem b2_interval_second_moment_from_twistK_v1 :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a N : ℕ)
        (c : ℕ → ℝ) (κ : ℕ → ℂ) (W : ℝ),
        admitted ε Y U m a →
        (∀ q ∈ PPset m a U,
          q.Prime ∧ q % m = a % m ∧ N ^ 2 < q) →
        (N : ℝ) ^ 2 ≤ Y ^ A →
        (∀ n, 0 ≤ c n) →
        (∀ n, c n ≠ 0 → IsPrimePow n) →
        (∀ n, ‖κ n‖ ≤ 1) →
        (∀ p, sP c N p ≤ W) →
        (∑ q ∈ PPset m a U, ‖∑ n ∈ Icc 1 N,
          ((c n : ℝ) : ℂ) * κ n *
            ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
        ((∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
          RR c m N ^ 2 + (2 * W ^ 2 + 2 * W * RR c m N) +
          Y ^ (-B) * (∑ n ∈ Icc 1 N, c n) ^ 2) *
          ((PPset m a U).card : ℝ) := by
  intro ε A B hε hA hB
  obtain ⟨Ybase, hbase⟩ := b2_actual_twistK_all_odd ε A B hε hA hB
  refine ⟨max Ybase 2, ?_⟩
  intro Y hY U m a N c κ W hAd hP hN2 hc hpp hκ hW
  have hYbase : Ybase ≤ Y := (le_max_left _ _).trans hY
  have hYnonneg : 0 ≤ Y := by
    have h2 : (2 : ℝ) ≤ Y := (le_max_right _ _).trans hY
    linarith
  have hδ : 0 ≤ Y ^ (-B) := Real.rpow_nonneg hYnonneg _
  have hJ : ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
      s.Coprime m → s ≤ N ^ 2 → s ≠ (2 : ℕ) →
        |∑ q ∈ PPset m a U,
          (jacobiSym (q : ℤ) s : ℝ)| ≤
          Y ^ (-B) * ((PPset m a U).card : ℝ) := by
    intro s hs ho hsq hcop hsN _
    have hsn : (s : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hsN
    exact hbase Y hYbase U m a hAd s hs ho hsq hcop (hsn.trans hN2)
  exact b2_weighted_meanSq_abs (PPset m a U) m a 2 N (Y ^ (-B)) W c κ
    hAd.eight hAd.coprime hδ hc hpp hP hκ hW hJ

#print axioms QH.b2_weighted_meanSq_abs
#print axioms QH.b2_interval_second_moment_from_twistK_v1
end QH
