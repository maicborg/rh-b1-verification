import Development.AutomorphicArithmetic.MeanSquareBounds.B2CountRelativeActualV3
import Development.AutomorphicArithmetic.MeanSquareBounds.B2UniformPNTFromAdmittedV4
import Development.AutomorphicArithmetic.MeanSquareBounds.B2ExponentFromAdmittedV4
import Development.AutomorphicArithmetic.MeanSquareBounds.B2LowEndpointDecayV2
import Development.AutomorphicArithmetic.MeanSquareBounds.B2AdmittedLogModulusV3
import Development.AutomorphicArithmetic.MeanSquareBounds.B2RealPNT

/-!
An attempted COMPLETE alternate QH.twistK proof conditional ONLY on
the PUBLISHED OpenAI 7/8 zero-free theorem h78.
Inputs: Alpoge's original pnt_progressions_relative_weak_holds, count_a,
admitted, CRT Jacobi; no import of original QH.twistK.
The exceptional integer is fixed as nstar=2, vacuous for odd s.
All quantitative thresholds are DISCHARGED via admitted, not assumed.
The h78 theorem itself is still a parameter until imported into this
pinned Lean 4.33.1 toolchain (OpenAI uses 4.34.1).
Direction Maicol Borghetti; formalization GPT-6.
-/
open Finset
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section

namespace QH

set_option maxHeartbeats 2000000 in
theorem b2_twistK_no_exception_of_seven_eighths_v5
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a : ℕ),
        admitted ε Y U m a →
        ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
          s.Coprime m → (s : ℝ) ≤ Y ^ A → s ≠ nstar →
          |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
            Y ^ (-B) * ((PPset m a U).card : ℝ) := by
  classical
  intro ε A B hε hA hB
  obtain ⟨cJ, AJ, CJ, cP, AP, CP, Y1, hcJ, hcP, hbridge⟩ :=
    b2_actual_count_and_jacobi_small_error_v3 h78 ε hε
  obtain ⟨YTJ, hTJ⟩ :=
    BorghettiRH.b2_pnt_two_thresholds_from_admitted_v4 ε A CJ hε hA
  obtain ⟨YTP, hTP⟩ :=
    BorghettiRH.b2_pnt_two_thresholds_from_admitted_v4 ε A CP hε hA
  obtain ⟨YBudget, hBudget⟩ :=
    BorghettiRH.b2_admitted_log_modulus_budget_v3 ε A hε hA
  obtain ⟨YEJ, hEJ⟩ :=
    BorghettiRH.b2_exp_error_from_admitted_log_budget_v4
      ε B cJ AJ hε hB hcJ
  obtain ⟨YEP, hEP⟩ :=
    BorghettiRH.b2_exp_error_from_admitted_log_budget_v4
      ε 1 cP AP hε (by norm_num) hcP
  obtain ⟨Yd, hD⟩ :=
    BorghettiRH.b2_low_endpoint_uniform_decay_v2 ε B hε hB
  refine ⟨max Y1 (max YTJ (max YTP (max YBudget
      (max YEJ (max YEP (max Yd (Real.exp 2))))))), ?_⟩
  intro Y hY U m a hAd
  simp only [max_le_iff] at hY
  rcases hY with ⟨hY1, hYTJ, hYTP, hYBudget, hYEJ, hYEP, hYd, hYexp⟩
  have hYone : (1 : ℝ) ≤ Y := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hYpos : 0 < Y := by linarith
  have hLogY : 0 ≤ Real.log Y := Real.log_nonneg hYone
  refine ⟨2, ?_⟩
  intro s hs hodd hsq hcop hsBound hne
  by_cases hUpos : 0 < U
  · have hLogU : (1 : ℝ) ≤ Real.log U := by
      have hp : 1 ≤ Y ^ (ε / 6) := Real.one_le_rpow hYone (by positivity)
      exact hp.trans hAd.lo
    have hU2 : 2 ≤ U := by
      have he : Real.exp (1 : ℝ) ≤ U :=
        (Real.le_log_iff_exp_le hUpos).mp hLogU
      have hExp1 := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hm8 : 8 ≤ m := Nat.le_of_dvd hAd.pos hAd.eight
    have hms8 : 8 ≤ m * s :=
      hm8.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < s))
    have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
      have hl2 : (0.6931471803 : ℝ) < Real.log 2 :=
        Real.log_two_gt_d9
      have he : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      linarith
    have hLmM : 2 ≤ Real.log (m : ℝ) :=
      hlog8.trans (Real.log_le_log (by norm_num)
        (by exact_mod_cast hm8))
    have hLmMS : 2 ≤ Real.log ((m * s : ℕ) : ℝ) :=
      hlog8.trans (Real.log_le_log (by norm_num)
        (by exact_mod_cast hms8))
    have hbudgetM : Real.log Y ^ 2 * Real.log (m : ℝ) ≤
        8 * Real.log U := by
      nlinarith [hAd.log_m, hLogU]
    have hbudgetMS : Real.log Y ^ 2 *
        Real.log ((m * s : ℕ) : ℝ) ≤ 8 * Real.log U := by
      simpa only [Nat.cast_mul] using
        (hBudget Y U m a s hYBudget hAd hs hsBound)
    have hTJ0 := hTJ Y U m a s hYTJ hAd hs hsBound
    have hTP0 := hTP Y U m a s hYTP hAd hs hsBound
    have hthJ :
        CJ * Real.log (m * s) * Real.log (Real.log (m * s) + 2) ≤ Real.log U :=
      hTJ0.2
    have hthP :
        CP * Real.log m * Real.log (Real.log m + 2) ≤ Real.log U :=
      hTP0.1
    have hEJ0 := hEJ Y U (Real.log ((m * s : ℕ) : ℝ)) m a
      hYEJ hAd hLmMS hbudgetMS
    have hYpow0 : 0 ≤ Y ^ (-B) := Real.rpow_nonneg hYpos.le _
    have hEJsmall :
        2 * |AJ| * (Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
          Real.exp (-Real.sqrt (cJ * Real.log U))) ≤ Y ^ (-B) / 2 := by
      have hEJcast : 2 * |AJ| *
          (Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
            Real.exp (-Real.sqrt (cJ * Real.log U))) ≤ Y ^ (-B) / 8 := by
        simpa only [Nat.cast_mul] using hEJ0
      nlinarith [hEJcast, hYpow0]
    have hEP0 := hEP Y U (Real.log (m : ℝ)) m a
      hYEP hAd hLmM hbudgetM
    have hYinv : Y ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_def_of_pos hYpos]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hLogY])
    have hEPsmall :
        |AP| * (Real.exp (-(cP * Real.log U / Real.log m)) +
          Real.exp (-Real.sqrt (cP * Real.log U))) ≤ 1 / 8 := by
      nlinarith [hEP0, hYinv]
    have hDsmall : Real.exp (-(2 / 5 * Real.log U)) ≤
        Y ^ (-B) / 4 := hD Y U m a hYd hAd
    have hTau : Y ^ (-B) ≤ 1 := by
      rw [Real.rpow_def_of_pos hYpos]
      have hBL := mul_nonneg hB.le hLogY
      exact Real.exp_le_one_iff.mpr (by nlinarith [hBL])
    exact hbridge Y U B m s a hY1 hYone hAd hB hs hodd hsq
      hcop hU2 hthJ hthP hEPsmall hEJsmall hDsmall hTau
  · have hUle : U ≤ 0 := le_of_not_gt hUpos
    have hEmpty : PPset m a U = ∅ := by
      unfold PPset
      rw [Nat.floor_of_nonpos hUle]
      simp
    simp [hEmpty]

#print axioms QH.b2_twistK_no_exception_of_seven_eighths_v5

/-! Original-signature replacement, independently instantiated from the real
    pinned OAI 7/8 theorem. Do not import the original Alpoge twistK module. -/
set_option maxHeartbeats 2000000 in
theorem twistK :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ),
        admitted ε Y U m₀ a₀ →
        ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s →
          s.Coprime m₀ → (s : ℝ) ≤ Y ^ A → s ≠ nstar →
          |∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)| ≤
            Y ^ (-B) * ((PPset m₀ a₀ U).card : ℝ) := by
  exact b2_twistK_no_exception_of_seven_eighths_v5
    BorghettiRH.b2_actual_h78

#print axioms QH.twistK
end QH
