import RFH123S.TentKernel
import Mathlib.NumberTheory.Chebyshev
open Real Finset Nat
namespace RFH123S

/-- Uniform error in the three weighted sums yields the positive tent main term. -/
lemma tent_main_lower (x q k e A B C : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hA : |A - log x/q - k| ≤ e)
    (hB : |B - log (3*x/2)/q - k| ≤ e)
    (hC : |C - log (2*x)/q - k| ≤ e) :
    log (32/27 : ℝ)/q - 6*e ≤ A - 3*B + 2*C := by
  have ha := (abs_le.mp hA).1
  have hb := (abs_le.mp hB).2
  have hc := (abs_le.mp hC).1
  have hm := congrArg (fun t : ℝ ↦ t / q) (tent_log_main x hx)
  simp only [sub_div, add_div, mul_div_assoc] at hm
  linarith

/-- Generic support extraction from a nonnegative tent.  The nonprime mass
can be bounded with Chebyshev.psi_sub_theta_le_mul_sqrt. -/
lemma exists_prime_of_mass {S : Finset ℕ} (a : ℕ → ℝ) (q : ℕ)
    (hzero : ∀ n ∈ S, ¬ n ≡ 1 [MOD q] → a n = 0)
    (hbig : ∑ n ∈ S with ¬ n.Prime, a n < ∑ n ∈ S, a n) :
    ∃ n ∈ S, n.Prime ∧ n ≡ 1 [MOD q] := by
  by_contra! h
  have hz : ∑ n ∈ S with n.Prime, a n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hnS, hnp⟩ := Finset.mem_filter.mp hn
    exact hzero n hnS (h n hnS hnp)
  have he := Finset.sum_filter_add_sum_filter_not S Nat.Prime a
  linarith

/-- Reuse the already proved prime-power estimate, rather than a new counting argument. -/
theorem nonprime_mangoldt_sqrt :
    ∃ C : ℝ, ∀ x : ℝ,
      (∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime,
        ArithmeticFunction.vonMangoldt n) ≤ C * sqrt x := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  exact ⟨C, fun x ↦ by rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]; exact hC x⟩

#print axioms tent_main_lower
#print axioms exists_prime_of_mass
#print axioms nonprime_mangoldt_sqrt
end RFH123S
