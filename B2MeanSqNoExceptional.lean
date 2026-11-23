import Development.AutomorphicArithmetic.MeanSquareBounds.MeanSqAbs

/-!
B2: conditional mean-square without exceptional pairing packet.
Program director: Maicol Borghetti. Proof development: GPT-6.
It reuses original Alpoge meansq_expand, meansq_split and pairs_one.
This file is conditional on all Jacobi correlations hJ being small:
it does NOT by itself import OpenAI 7/8 or prove RH.
-/

open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_meansq_split_without_exception
    (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η)
    (hno2 : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 2)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I,
        if r n n' = 1 then c n * c n' else 0) +
        η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hsplit :=
    meansq_split I c hc r A P η hP hη 2 hA
      (by
        intro n hn n' hn' hne _
        exact hA' n hn n' hn' hne)
  have hzero :
      (∑ n ∈ I, ∑ n' ∈ I,
        if r n n' = 2 then c n * c n' else (0 : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro n' hn'
    simp [hno2 n hn n' hn']
  simpa only [hzero, add_zero] using hsplit

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_meansq_split_without_exception

theorem b2_meanSq_abs_without_exception :
    ∀ (P : Finset ℕ) (m₀ a₀ : ℕ) (Z y η : ℝ) (κ : ℕ → ℂ),
      8 ∣ m₀ → a₀.Coprime m₀ → 0 ≤ y → 0 ≤ η →
      (∀ q ∈ P, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q) →
      (∀ n, ‖κ n‖ ≤ 1) →
      (∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ →
        s ≤ ⌊Z⌋₊ ^ 2 →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) →
      ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤
        ((∑ p ∈ (Icc 1 ⌊Z⌋₊).filter Nat.Prime, sP (cN y) ⌊Z⌋₊ p ^ 2) +
          RR (cN y) m₀ ⌊Z⌋₊ ^ 2 +
          η * (∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n) ^ 2) * P.card := by
  intro P m₀ a₀ Z y η κ h8 hcop hy hη hP hκ hJ
  set N := ⌊Z⌋₊ with hN
  have hc0 : ∀ n, 0 ≤ cN y n := cN_nonneg y hy
  have hcpp : ∀ n, cN y n ≠ 0 → IsPrimePow n := cN_primePow y
  have hexp := meansq_expand P (Icc 1 N) (cN y) hc0 κ hκ
    (fun n q => jacobiSym (n : ℤ) q)
  have hpair : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      |∑ q ∈ P,
        ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
        |∑ q ∈ P, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
    intro n hn n' hn'
    rw [Finset.mem_Icc] at hn hn'
    refine abs_pair_sum_eq P m₀ a₀ n n' h8 hcop (by omega) (by omega) ?_
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hP q hq
    refine ⟨h1, h2, lt_of_le_of_lt ?_ h3⟩
    rw [pow_two]
    exact Nat.mul_le_mul hn.2 hn'.2
  have hno2 : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      soutPart m₀ (n * n') ≠ 2 := by
    intro n hn n' hn'
    have hodd : Odd (soutPart m₀ (n * n')) :=
      soutPart_odd m₀ _ (dvd_trans (by norm_num) h8)
    omega
  have hsplit := b2_meansq_split_without_exception (Icc 1 N)
    (cN y) hc0 (fun n n' => soutPart m₀ (n * n'))
    (fun n n' => |∑ q ∈ P,
      ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|)
    (P.card : ℝ) η (by positivity) hη hno2
    (by
      intro n hn n' hn'
      rw [hpair n hn n' hn']
      exact abs_sum_jacobi_le P _)
    (by
      intro n hn n' hn' hr1
      rw [hpair n hn n' hn']
      rw [Finset.mem_Icc] at hn hn'
      have hpos := soutPart_pos m₀ (n * n')
      have hnn : 0 < n * n' := Nat.mul_pos (by omega) (by omega)
      have hle : soutPart m₀ (n * n') ≤ N ^ 2 := by
        refine (soutPart_le m₀ _ hnn).trans ?_
        rw [pow_two]
        exact Nat.mul_le_mul hn.2 hn'.2
      exact hJ _ (by omega) (soutPart_odd m₀ _ (dvd_trans (by norm_num) h8))
        (soutPart_squarefree m₀ _)
        (soutPart_coprime m₀ _) hle)
  beta_reduce at hsplit
  have h1 := pairs_one (cN y) hc0 hcpp m₀ N
  refine hexp.trans (hsplit.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_meanSq_abs_without_exception

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
