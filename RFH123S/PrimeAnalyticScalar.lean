import Mathlib

open Real Finset
namespace RFH123S

/-- Uniform modulus bound for the actual power used in the auxiliary
prime construction, with N fixed and s at most 32 u. -/
lemma prime_modulus_exp_bound (N s : ℕ) (u : ℝ)
    (hN : 0 < N) (hu : 1 ≤ u) (hs : (s : ℝ) ≤ 32*u) :
    ((N^((s+6)*2) : ℕ) : ℝ) ≤ exp (76*log (N : ℝ)*u) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg hn1
  push_cast
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  push_cast
  have hs' : ((s : ℝ)+6)*2 ≤ 76*u := by linarith
  calc
    _ ≤ (76*u)*log (N : ℝ) := mul_le_mul_of_nonneg_right hs' hlog
    _ = _ := by ring

/-- A power-saving error, even with exponential loss in u, is less
than the main term uniformly for U >= u^2. -/
lemma prime_window_positive (A B u U q mass : ℝ)
    (hu : 1 ≤ u) (hlarge : 16*(A+B)+1 ≤ u) (hU : u^2 ≤ U)
    (hq : 0 < q) (hqB : q ≤ exp (B*u))
    (herr : |mass-(exp (U+1)-exp U)/q| ≤ exp (A*u+(15/16:ℝ)*U)) :
    0 < mass := by
  have hup : 0 < u := by linarith
  have hmul := mul_le_mul_of_nonneg_right hlarge hup.le
  have hgap : A*u+(15/16:ℝ)*U+B*u < U := by nlinarith
  have hE : exp (A*u+(15/16:ℝ)*U) < exp U/q := by
    apply (lt_div_iff₀ hq).2
    calc
      _ ≤ exp (A*u+(15/16:ℝ)*U)*exp (B*u) :=
        mul_le_mul_of_nonneg_left hqB (Real.exp_pos _).le
      _ = exp (A*u+(15/16:ℝ)*U+B*u) := (Real.exp_add _ _).symm
      _ < exp U := Real.exp_lt_exp.mpr hgap
  have h2 : (2 : ℝ) ≤ exp 1 := by
    simpa using Real.add_one_le_exp (1 : ℝ)
  have hmain : exp U/q ≤ (exp (U+1)-exp U)/q := by
    apply div_le_div_of_nonneg_right _ hq.le
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos U).le]
  have hneg := (abs_le.mp herr).1
  linarith

/-- Actual weighted mass of primes in the logarithmic window [U,U+1].
This is a finite sum; no prime-existence assumption is built in. -/
noncomputable def primeWindowMass (q : ℕ) (U : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊exp (U+1)⌋₊+1)).filter
      (fun p => p.Prime ∧ p ≡ 1 [MOD q] ∧ log (p : ℝ) ∈ Set.Icc U (U+1)),
    log (p : ℝ)

/-- Positive weighted mass supplies the required genuine prime. -/
lemma prime_of_positive_window_mass (q : ℕ) (U L : ℝ)
    (hL : 1 ≤ sqrt L) (h : 0 < primeWindowMass q U) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ log (p : ℝ) ∈ Set.Icc U (U+sqrt L) := by
  classical
  by_contra hn
  have hz : primeWindowMass q U = 0 := by
    unfold primeWindowMass
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨_,hp',hm,hmem⟩ := Finset.mem_filter.mp hp
    exact (hn ⟨p,hp',hm, hmem.1, hmem.2.trans (by linarith)⟩).elim
  linarith

#print axioms prime_modulus_exp_bound
#print axioms prime_window_positive
#print axioms prime_of_positive_window_mass
end RFH123S
