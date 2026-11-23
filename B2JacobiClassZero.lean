import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistA

/-!
B2 general Jacobi cancellation for odd squarefree s.
Direction: Maicol Borghetti. Lean implementation: GPT-6.
Uses Alpoge previously proved existence of nonresidue and sum permutation,
but not twistK or its proof.
-/
open Finset Classical
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
    exact (Finset.mem_filter.mp hb).1
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
  have hzero : (∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) =
      -(∑ b ∈ R, (jacobiSym (b : ℤ) s : ℝ)) := by
    rw [hsum]
    calc
      _ = ∑ b ∈ R, -(jacobiSym (b : ℤ) s : ℝ) :=
        Finset.sum_congr rfl hflip
      _ = _ := by rw [Finset.sum_neg_distrib]
  simp only [R] at hzero ⊢
  linarith

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_jacobi_cls_sum_zero
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
