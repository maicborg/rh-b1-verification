import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistA

/-!
B2 general Jacobi cancellation for odd squarefree s.
Direction: Maicol Borghetti. Lean implementation: GPT-6.
Uses Alpoge previously proved existence of nonresidue and sum permutation,
but not twistK or its proof.
-/
open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_jacobi_cls_sum_zero
    (m s a : ℕ) (hm : 0 < m) (hs : 1 < s)
    (hodd : Odd s) (hsquare : Squarefree s)
    (hcop : s.Coprime m) :
    (∑ b ∈ clsB m s a, (jacobiSym (b : ℤ) s : ℝ)) = 0 := by
  classical
  obtain ⟨u, hu, hneg⟩ :=
    exists_jacobi_neg_one m s hodd hsquare hs hcop
  haveI : NeZero s := ⟨by omega⟩
  have huc : u.Coprime s := by
    by_contra hnc
    have heq : jacobiSym (u : ℤ) s = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hnc
    rw [hneg] at heq
    norm_num at heq
  have hum : u.Coprime m := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hu]
    simp
  have huM : u.Coprime (m * s) := Nat.Coprime.mul_right hum huc
  let R := clsB m s a
  have hS : ∀ b ∈ R, b < m * s := by
    intro b hb
    exact Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hmap : ∀ b ∈ R, (u * b) % (m * s) ∈ R := by
    intro b hb
    obtain ⟨hbRange, hbmod, hbc⟩ :
        b < m * s ∧ b % m = a % m ∧ b.Coprime s := by
      simpa [R, clsB] using hb
    have hmod : (u * b) % m = b % m := by
      calc
        (u * b) % m = (u % m * (b % m)) % m := Nat.mul_mod u b m
        _ = (1 % m * (b % m)) % m := by rw [hu]
        _ = b % m := by simp
    have hcop' : (u * b).Coprime s := Nat.Coprime.mul_left huc hbc
    have hr : (u * b) % (m * s) < m * s :=
      Nat.mod_lt _ (Nat.mul_pos hm (by omega))
    simp only [R, clsB, Finset.mem_filter, Finset.mem_range]
    refine ⟨hr, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m s), hmod]
      exact hbmod
    · have h := (Nat.ModEq.of_dvd (dvd_mul_left s m)
        (Nat.mod_modEq (u * b) (m * s))).gcd_eq
      rw [Nat.Coprime, h]
      exact hcop'
  have hsum : (∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) =
      ∑ b ∈ R, (jacobiSym (((u * b) % (m * s) : ℕ) : ℤ) s : ℝ) :=
    sum_perm (m * s) u huM R R hS hmap (le_refl _) _
  have hflip : ∀ b ∈ R,
      (jacobiSym (((u * b) % (m * s) : ℕ) : ℤ) s : ℝ) =
      -(jacobiSym (b : ℤ) s : ℝ) := by
    intro b hb
    have hmod : jacobiSym ((u * b : ℕ) : ℤ) s =
        jacobiSym (((u * b) % (m * s) : ℕ) : ℤ) s := by
      apply jacobi_congr
      exact Nat.ModEq.of_dvd (dvd_mul_left s m)
        (Nat.mod_modEq (u * b) (m * s)).symm
    have hmul : jacobiSym ((u * b : ℕ) : ℤ) s =
        -jacobiSym (b : ℤ) s := by
      rw [Nat.cast_mul, jacobiSym.mul_left, hneg]
      ring
    exact_mod_cast hmod.symm.trans hmul
  have hflip_sum :
      (∑ b ∈ R, (jacobiSym (((u * b) % (m * s) : ℕ) : ℤ) s : ℝ)) =
      -(∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) := by
    calc
      _ = ∑ b ∈ R, -(jacobiSym (b : ℤ) s : ℝ) :=
        Finset.sum_congr rfl hflip
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hzero : (∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) =
      -(∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) :=
    hsum.trans hflip_sum
  simp only [R] at hzero ⊢
  linarith

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_jacobi_cls_sum_zero
/--
Exact one-endpoint conversion of a UNIFORM per-residue AP estimate
to a bound for the original Alpoge PPset Jacobi sum.

The analytic AP estimate hAP is EXPLICITLY AN ASSUMPTION here:
the paper's quantitative 11/12 corollary is NOT imported as a Lean theorem.
All other facts are proved using Alpoge's own exact sum decomposition,
small prime count, CRT residue class size and the cancellation above.
-/
theorem b2_jacobi_bound_of_uniform_AP
    (m s a : ℕ) (hm : 0 < m) (hs : 1 < s)
    (hodd : Odd s) (hsquare : Squarefree s)
    (hcop : s.Coprime m) (U main E : ℝ)
    (hU : 0 ≤ U) (hE : 0 ≤ E)
    (hAP : ∀ b ∈ clsB m s a,
        |(piAP U (m * s) b : ℝ) - main| ≤ E) :
    |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (s.totient : ℝ) * E + U ^ (1 / 2 : ℝ) := by
  classical
  let R := clsB m s a
  let σ : ℕ → ℝ := fun b => (jacobiSym (b : ℤ) s : ℝ)
  let N : ℕ → ℝ := fun b =>
    (((PPset m a U).filter (fun q => q % (m * s) = b)).card : ℝ)
  let H : ℕ → ℝ := fun b => (piAP U (m * s) b : ℝ)
  let T : ℕ → ℝ := fun b => (smallCnt U (m * s) b : ℝ)
  have hC : (∑ b ∈ R, σ b) = 0 := by
    simpa [R, σ] using b2_jacobi_cls_sum_zero m s a hm hs hodd hsquare hcop
  have hσ : ∀ b ∈ R, |σ b| ≤ 1 := by
    intro b hb
    simpa [σ] using abs_jac_le (b : ℤ) s
  have hAP' : ∀ b ∈ R, |H b - main| ≤ E := by
    intro b hb
    exact hAP b (by simpa [R] using hb)
  have hCount : ∀ b ∈ R, N b = H b - T b := by
    intro b hb
    have ht := cnt_add_small m s a U b (by simpa [R] using hb)
    have htr : N b + T b = H b := by
      dsimp [N, H, T]
      exact_mod_cast ht
    linarith
  have hSum : (∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)) =
      ∑ b ∈ R, σ b * (H b - T b) := by
    calc
      _ = ∑ b ∈ R, σ b * N b := by
        simpa [R, σ, N] using
          (sum_jacobiSym_eq_sum_residueClass m s a U hm (by omega))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hCount b hb]
  have hTop : |∑ b ∈ R, σ b * H b| ≤ (R.card : ℝ) * E := by
    have heq : (∑ b ∈ R, σ b * H b) =
        ∑ b ∈ R, σ b * (H b - main) := by
      calc
        _ = (∑ b ∈ R, σ b * (H b - main)) +
            main * (∑ b ∈ R, σ b) := by
              rw [mul_comm main (∑ b ∈ R, σ b), Finset.sum_mul]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = _ := by simp [hC]
    rw [heq]
    calc
      |∑ b ∈ R, σ b * (H b - main)| ≤
          ∑ b ∈ R, |σ b * (H b - main)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ R, E := by
          apply Finset.sum_le_sum
          intro b hb
          rw [abs_mul]
          calc
            |σ b| * |H b - main| ≤ 1 * E := by
              exact mul_le_mul (hσ b hb) (hAP' b hb)
                (abs_nonneg _) (by norm_num)
            _ = E := by ring
      _ = (R.card : ℝ) * E := by simp
  have hT0 : ∀ b : ℕ, 0 ≤ T b := by
    intro b
    dsimp [T]
    positivity
  have hLow : |∑ b ∈ R, σ b * T b| ≤ U ^ (1 / 2 : ℝ) := by
    calc
      |∑ b ∈ R, σ b * T b| ≤
          ∑ b ∈ R, |σ b * T b| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ R, T b := by
          apply Finset.sum_le_sum
          intro b hb
          rw [abs_mul, abs_of_nonneg (hT0 b)]
          nlinarith [hσ b hb, hT0 b]
      _ ≤ U ^ (1 / 2 : ℝ) := by
          simpa [R, T] using sum_small_le m s a U hU
  have hSub : (∑ b ∈ R, σ b * (H b - T b)) =
      (∑ b ∈ R, σ b * H b) -
      (∑ b ∈ R, σ b * T b) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hCard : R.card = s.totient := by
    exact card_cls m s a hcop.symm hm.ne' (by omega)
  calc
    |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| =
        |∑ b ∈ R, σ b * (H b - T b)| := by rw [hSum]
    _ = |(∑ b ∈ R, σ b * H b) -
          (∑ b ∈ R, σ b * T b)| := by rw [hSub]
    _ ≤ |∑ b ∈ R, σ b * H b| +
          |∑ b ∈ R, σ b * T b| := by
            simpa using (abs_sub_le (∑ b ∈ R, σ b * H b)
              0 (∑ b ∈ R, σ b * T b))
    _ ≤ (R.card : ℝ) * E + U ^ (1 / 2 : ℝ) :=
          add_le_add hTop hLow
    _ = (s.totient : ℝ) * E + U ^ (1 / 2 : ℝ) := by rw [hCard]

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_jacobi_bound_of_uniform_AP


end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
