import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC

/-!
Full uniform low-endpoint rate from the ORIGINAL QH.admitted,
independent of QH.twistK, for any eps,B>0.
Mathematical technique: Alpoge-Claude. Formal proof adaptation GPT-6.
Program director Maicol Borghetti.
-/
noncomputable section
namespace BorghettiRH

theorem b2_low_endpoint_uniform_decay
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ Y₀ : ℝ, ∀ (Y U : ℝ) (m a : ℕ),
      Y₀ ≤ Y → QH.admitted ε Y U m a →
      Real.exp (-(2 / 5 * Real.log U)) ≤ Y ^ (-B) / 4 := by
  obtain ⟨x₀, hx₀⟩ :=
    Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.eventually_log_cube
      (5 * (B + 1)) (ε / 6) (by positivity) (by positivity)
  refine ⟨max x₀ (Real.exp 2), ?_⟩
  intro Y U m a hY hAd
  have hx₀ : x₀ ≤ Y := le_trans (le_max_left _ _) hY
  have hYexp : Real.exp 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hYexp
  have hL2 : 2 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hYpos]
    exact hYexp
  have hL0 : 0 ≤ Real.log Y := by linarith
  have hUhuge : 5 * (B + 1) * Real.log Y ^ 3 ≤ Real.log U :=
    (hx₀ Y hx₀).trans hAd.lo
  have hlog4 : Real.log 4 ≤ 2 := by
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_lt_d9
    linarith
  have h4L : 4 * Real.log Y ≤ Real.log Y ^ 3 := by
    have hh : (4 : ℝ) ≤ Real.log Y ^ 2 := by nlinarith
    have hr := mul_le_mul_of_nonneg_right hh hL0
    nlinarith [hr]
  have h5L := mul_le_mul_of_nonneg_left h4L (by linarith : 0 ≤ B + 1)
  have hCmp : B * Real.log Y + Real.log 4 ≤
      (2 / 5 : ℝ) * Real.log U := by
    nlinarith [h5L, hUhuge, hlog4]
  calc
    Real.exp (-(2 / 5 * Real.log U)) ≤
        Real.exp (-(B * Real.log Y) - Real.log 4) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(B * Real.log Y)) / 4 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]
    _ = Y ^ (-B) / 4 := by
      rw [Real.rpow_def_of_pos hYpos]
      congr 1
      ring

#print axioms BorghettiRH.b2_low_endpoint_uniform_decay
end BorghettiRH
