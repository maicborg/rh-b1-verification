import Development.AutomorphicArithmetic.MeanSquareBounds.B2IntervalPrimepowersBudgetV1

/-!
B2.2 -- LOCAL diagonal prime-power energy, not just global O(x log x).
For any finite interval/window I of integers, a nonnegative weight
supported on I and on prime powers has a diagonal second moment bounded
by (sup_p sP) times the total weight on I. In particular a pointwise
bound L yields a factor card(I)*L, rather than a global factor x.

Uses the exact Alpoge sP function and the unique minimal prime factor.
Direction: Maicol Borghetti. Lean formalization: GPT-6.
-/

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section

namespace QH

/-- Prime-power mass is partitioned by the unique base prime. -/
theorem b2_sP_partition_primepowers (c : ℕ → ℝ) (N : ℕ)
    (hsupp : ∀ n, c n ≠ 0 → IsPrimePow n) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p) =
      ∑ n ∈ Icc 1 N, c n := by
  classical
  calc
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p) =
        ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          ∑ n ∈ Icc 1 N,
            if IsPrimePow n ∧ n.minFac = p then c n else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [sP, Finset.sum_filter]
    _ = ∑ n ∈ Icc 1 N,
          ∑ p ∈ (Icc 1 N).filter Nat.Prime,
            if IsPrimePow n ∧ n.minFac = p then c n else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ Icc 1 N, c n := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hpp : IsPrimePow n
          · have hpr : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
            have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
            have hmn : n.minFac ≤ N :=
              (Nat.minFac_le hpp.ne_one).trans hnN
            have hmem : n.minFac ∈ (Icc 1 N).filter Nat.Prime :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
                ⟨hpr.one_lt.le, hmn⟩, hpr⟩
            simp [hpp, hmem]
          · have hzero : c n = 0 := by
              by_contra hne
              exact hpp (hsupp n hne)
            simp [hpp, hzero]

/-- The diagonal has no hidden exceptional-prime correction:
    every square is bounded by W times its nonnegative mass. -/
theorem b2_local_energy_primes (c : ℕ → ℝ) (N : ℕ) (W : ℝ)
    (hc : ∀ n, 0 ≤ c n)
    (hW : ∀ p, sP c N p ≤ W) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
      W * (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p) := by
  calc
    _ ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, W * sP c N p := by
      apply Finset.sum_le_sum
      intro p hp
      have hsp : 0 ≤ sP c N p :=
        Finset.sum_nonneg (fun n _ => hc n)
      have hmax := hW p
      nlinarith [mul_nonneg hsp (sub_nonneg.mpr hmax)]
    _ = W * (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p) := by
      rw [Finset.mul_sum]

/-- The desired LOCAL inequality: it depends on the mass in the
    selected window I rather than on the global parameter x. -/
theorem b2_interval_local_energy
    (c : ℕ → ℝ) (N : ℕ) (I : Finset ℕ) (W L : ℝ)
    (hc : ∀ n, 0 ≤ c n)
    (hsupp : ∀ n, c n ≠ 0 → IsPrimePow n)
    (hI : I ⊆ Icc 1 N)
    (hout : ∀ n ∈ Icc 1 N, n ∉ I → c n = 0)
    (hL : ∀ n ∈ I, c n ≤ L)
    (hW0 : 0 ≤ W)
    (hW : ∀ p, sP c N p ≤ W) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
      W * L * (I.card : ℝ) := by
  have hsum : (∑ n ∈ Icc 1 N, c n) = ∑ n ∈ I, c n := by
    symm
    apply Finset.sum_subset hI
    intro n hn hnI
    exact hout n hn hnI
  have hmass : (∑ n ∈ I, c n) ≤ (I.card : ℝ) * L := by
    calc
      _ ≤ ∑ _n ∈ I, L := Finset.sum_le_sum (fun n hn => hL n hn)
      _ = (I.card : ℝ) * L := by simp [mul_comm]
  calc
    _ ≤ W * (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p) :=
      b2_local_energy_primes c N W hc hW
    _ = W * (∑ n ∈ Icc 1 N, c n) := by
      rw [b2_sP_partition_primepowers c N hsupp]
    _ = W * (∑ n ∈ I, c n) := by rw [hsum]
    _ ≤ W * ((I.card : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hmass hW0
    _ = W * L * (I.card : ℝ) := by ring

/-- Instantiation with the actual certified prime-power logarithmic
    bound from B2IntervalPrimepowersBudgetV1. -/
theorem b2_interval_local_energy_801
    (x : ℝ) (hx : Real.exp 1 ≤ x)
    (N : ℕ) (hN : N ≤ ⌊x ^ 400⌋₊)
    (I : Finset ℕ) (L : ℝ)
    (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n)
    (hdom : ∀ n, c n ≤ cN x n)
    (hI : I ⊆ Icc 1 N)
    (hout : ∀ n ∈ Icc 1 N, n ∉ I → c n = 0)
    (hL : ∀ n ∈ I, c n ≤ L) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
      801 * Real.log x * L * (I.card : ℝ) := by
  have hsupp := b2_dominated_primepower_support x c hc hdom
  have hW : ∀ p, sP c N p ≤ 801 * Real.log x :=
    fun p => b2_sP_upper_log x hx N p hN c hdom
  have hW0 : 0 ≤ 801 * Real.log x := by
    have hx1 : (1 : ℝ) ≤ x := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg hx1)
  exact b2_interval_local_energy c N I (801 * Real.log x) L
    hc hsupp hI hout hL hW0 hW

#print axioms QH.b2_sP_partition_primepowers
#print axioms QH.b2_local_energy_primes
#print axioms QH.b2_interval_local_energy
#print axioms QH.b2_interval_local_energy_801
end QH
