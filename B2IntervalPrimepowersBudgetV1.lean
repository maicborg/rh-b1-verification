import Development.AutomorphicArithmetic.MeanSquareBounds.B2IntervalSecondMomentV1
import Development.AutomorphicArithmetic.MeanSquareBounds.SPsqLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA

/-!
B2.2 - quantitative diagonal budget for any interval-supported
prime-power weight dominated by cN x n = Lambda(n) * min(1,x/n).

The key insight is to reuse Alpoge's *proven* global prime-power
bound sPsq_le and to exploit positivity. Restricting the weights to
an interval cannot increase the diagonal energy. Restriction to odd
prime powers with bases not dividing m makes RR identically zero.

This is a substantive bridge, not a reproof of sPsq_le. Its input
domination is satisfied by weights Lambda(n) * 1_{n in I} for n<=x.
Director: Maicol Borghetti. Formalization: GPT-6.
-/

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem b2_dominated_primepower_support
    (x : ℝ) (c : ℕ → ℝ)
    (hc0 : ∀ n, 0 ≤ c n)
    (hdom : ∀ n, c n ≤ cN x n) :
    ∀ n, c n ≠ 0 → IsPrimePow n := by
  intro n hne
  apply cN_primePow x n
  intro hcn
  have h := hdom n
  rw [hcn] at h
  exact hne (le_antisymm h (hc0 n))

theorem b2_RR_zero_of_odd_primepowers
    (c : ℕ → ℝ) (m N : ℕ)
    (hodd : ∀ n, IsPrimePow n →
      (Even (n.factorization n.minFac) ∨ n.minFac ∣ m) → c n = 0) :
    RR c m N = 0 := by
  unfold RR
  apply Finset.sum_eq_zero
  intro n hn
  exact hodd n (Finset.mem_filter.mp hn).2.1
    (Finset.mem_filter.mp hn).2.2

theorem b2_sP_dominated (x : ℝ) (N p : ℕ) (c : ℕ → ℝ)
    (hdom : ∀ n, c n ≤ cN x n) :
    sP c N p ≤ sP (cN x) N p := by
  unfold sP
  exact Finset.sum_le_sum (fun n _ => hdom n)

theorem b2_sP_upper_log (x : ℝ) (hx : Real.exp 1 ≤ x)
    (N p : ℕ) (hN : N ≤ ⌊x ^ 400⌋₊)
    (c : ℕ → ℝ) (hdom : ∀ n, c n ≤ cN x n) :
    sP c N p ≤ 801 * Real.log x := by
  have hsubset :
      (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
        (Icc 1 ⌊x ^ 400⌋₊).filter
          (fun n => IsPrimePow n ∧ n.minFac = p) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hI, hcond⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hI).1,
        (Finset.mem_Icc.mp hI).2.trans hN⟩, hcond⟩
  have hcn : ∀ n, 0 ≤ cN x n := cN_nonneg x (by
    have h := Real.exp_pos (1 : ℝ)
    linarith)
  have hmon :
      sP (cN x) N p ≤ sP (cN x) ⌊x ^ 400⌋₊ p := by
    unfold sP
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n _ _ => hcn n)
  exact (b2_sP_dominated x N p c hdom).trans
    (hmon.trans (primePowerSum_le_mul_log x hx p))

theorem b2_sPsq_dominated (x : ℝ) (N : ℕ)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n)
    (hdom : ∀ n, c n ≤ cN x n) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN x) N p ^ 2 := by
  apply Finset.sum_le_sum
  intro p hp
  have hsp0 : 0 ≤ sP c N p := by
    unfold sP
    exact Finset.sum_nonneg (fun n _ => hc0 n)
  exact pow_le_pow_left₀ hsp0 (b2_sP_dominated x N p c hdom) 2

/-- Full numeric interval budget, including the diagonal correction
    2 W^2 and RR, with W=801 log x. It is independent of the
    position and length of the selected interval. -/
theorem b2_interval_primepowers_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ℝ) (N m : ℕ) (c : ℕ → ℝ),
        3 ≤ x → Real.exp 1 ≤ x →
        N ≤ ⌊x ^ 400⌋₊ →
        (∀ n, 0 ≤ c n) →
        (∀ n, c n ≤ cN x n) →
        (∀ n, IsPrimePow n →
          (Even (n.factorization n.minFac) ∨ n.minFac ∣ m) → c n = 0) →
        (∀ p, sP c N p ≤ 801 * Real.log x) ∧
        RR c m N = 0 ∧
        ((∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
          RR c m N ^ 2 +
          (2 * (801 * Real.log x) ^ 2 +
            2 * (801 * Real.log x) * RR c m N)) ≤
          C * (x * Real.log x) := by
  obtain ⟨C0, hC0, hsq⟩ := sPsq_le
  refine ⟨C0 + 2 * (801 : ℝ) ^ 2, by positivity, ?_⟩
  intro x N m c hx hxexp hN hc0 hdom hodd
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog_le : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlogSq : Real.log x ^ 2 ≤ x * Real.log x := by
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog_le)]
  have hRR : RR c m N = 0 := b2_RR_zero_of_odd_primepowers c m N hodd
  have hdiag :
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) ≤
        C0 * x * Real.log x := by
    exact (b2_sPsq_dominated x N c hc0 hdom).trans (hsq x hx N)
  have hW : ∀ p, sP c N p ≤ 801 * Real.log x :=
    fun p => b2_sP_upper_log x hxexp N p hN c hdom
  refine ⟨hW, hRR, ?_⟩
  have hWsq : 2 * (801 * Real.log x) ^ 2 ≤
      2 * (801 : ℝ) ^ 2 * (x * Real.log x) := by
    nlinarith [hlogSq]
  calc
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
        RR c m N ^ 2 +
        (2 * (801 * Real.log x) ^ 2 +
          2 * (801 * Real.log x) * RR c m N)
        = (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) +
          2 * (801 * Real.log x) ^ 2 := by rw [hRR]; ring
    _ ≤ C0 * x * Real.log x +
          2 * (801 : ℝ) ^ 2 * (x * Real.log x) :=
      add_le_add hdiag hWsq
    _ = (C0 + 2 * (801 : ℝ) ^ 2) * (x * Real.log x) := by ring

#print axioms QH.b2_dominated_primepower_support
#print axioms QH.b2_RR_zero_of_odd_primepowers
#print axioms QH.b2_sP_dominated
#print axioms QH.b2_sP_upper_log
#print axioms QH.b2_sPsq_dominated
#print axioms QH.b2_interval_primepowers_budget

end QH
