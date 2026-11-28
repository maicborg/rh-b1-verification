import New.Endgame.PrimeError

/-! Extract the exact transform from the proof of isPolar_primeError.
Source: lsernau/grh-lean, 72fead102f663d5c7a407964a13dc0cf9d977207,
grh-compact/src/New/Endgame/PrimeError.lean.
The algebra and finite-series calculation below are retained from that proof.
No arbitrary IsPolar witness is identified with this explicit transform. -/
noncomputable section
open ArithmeticFunction DirichletCharacter Complex Finset Filter MeasureTheory Nat Real vonMangoldt
namespace RFH123S
variable {d M : ℕ} [Fact d.Prime] [NeZero M]

theorem primeError_laplace_explicit (hd : d % 8 = 7) (h : M.Coprime d) (s : ℂ) (u : 2 < s.re) :
    (logDerivMean d M s / s - (logDerivMean d M 1).re) / (s - 1) =
      ∫ v in Set.Ioi (0 : ℝ), (primeError d M (Real.exp v) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ)) := by
  let κ := (logDerivMean d M 1).re
  have L := @laplace_pow (s - 1) (by simp [u.trans'])
  have e r : (s + r - 1) * ∫ v in _, lambdaSum d M r (rexp v) * (v - s * v).exp = _ := .trans (by
    congr 1; convert integral_comp_exp_Ioi _ 0 <;> simp [lambdaSum, field, cpow_add, cpow_neg,
      le_of_lt,
    Complex.exp_sub, cpow_def _ s, Complex.log_exp, mul_comm s, pi_pos]) ((@LSeries_eq_mul_integral'
    _ (1 + r) (by bound) _ (by simp; bound) (.of_bound 2 (.mono (Ioi_mem_atTop 0) fun n _ ↦ by
    simpa [lambdaSum, *, div_le_iff₀, abs_div, rpow_add, field, lambdaClass_nonneg_and_abs_le,
      Real.exp_log, abs_of_nonneg] using abs_lambdaSum_exp_le d M r (.log n)))).symm.trans
    (((LSeriesHasSum.sum (S := ⊤) fun ξ _ ↦ (@LSeriesHasSum_mul_vonMangoldt M ξ _ s (by bound)).sub
    (LSeriesHasSum_mul_vonMangoldt (quadTwist ξ d) (by bound))).div_const (φ M)).congr_fun
    fun n ↦ by by_cases n = 0 <;> simp [*, cpow_sub, field, cpow_add, lambdaClass,
    chiK_eq_legendreSym, residueClass_apply, mod_cast (quadTwist_apply · d n), ← sum_mul]).tsum_eq)
  obtain := L 0, L 1, Integrable.of_integral_ne_zero ((L 0).trans_ne (by aesop)),
    Integrable.of_integral_ne_zero ((L 1).trans_ne (by aesop)),
    fun r ↦ integrableOn_laplace_of_abs_le
    (by fun_prop [lambdaSum]) (fun v _ ↦ abs_lambdaSum_exp_le d M r _) u
  simp [primeError, κ, IntegrableOn, sub_mul, div_eq_inv_mul, logDerivMean, mul_assoc,
    quadTwist_ne_one _ d (by lia) h] at *
  simp (disch := fun_prop) [integral_sub, *]
  linear_combination (norm := field (disch := grind [zero_re, one_re])) e 1 / s - e 0 / (s - 1)
  grind [ofReal_one]
  
theorem logDerivMean_real_at_one (hd : d % 8 = 7) (h : M.Coprime d) :
    logDerivMean d M 1 = ((logDerivMean d M 1).re : ℂ) := by
  let κ := (logDerivMean d M 1).re
  have A : AnalyticOnNhd ℂ (fun s ↦ logDerivMean d M s / s - κ) {s | 1 ≤ s.re} := fun _ _ ↦ by
    fun_prop (disch := grind [entireL_ne_zero, zero_re]) [logDerivMean, logDeriv]
  have hzero : logDerivMean d M 1 / 1 - κ = 0 := by
    exact @ext _ 0 (by simp [κ]) ((A.mono (by aesop)
      ).im_ofReal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ici (by simp) (.mono
      (lt_mem_nhds (lt_add_one _)) fun x u ↦
        congr(im $((div_eq_iff (by aesop)).1 (primeError_laplace_explicit hd h x u))).trans
        (by norm_cast)) (le_refl (1 : ℝ)))
  exact sub_eq_zero.mp (by simpa [κ] using hzero)

lemma primeError_at_one : primeError d M 1 = -(logDerivMean d M 1).re := by
  simp [primeError, lambdaSum]

#print axioms primeError_laplace_explicit
#print axioms logDerivMean_real_at_one
#print axioms primeError_at_one
end RFH123S
