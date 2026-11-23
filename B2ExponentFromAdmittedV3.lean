import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiEnvelopeV3
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC

/-!
Turn the independent exponential envelope into a UNIFORM quantitative
Y0, using ORIGINAL QH.admitted.lo and Alpoge eventually_log_cube.
Valid for ANY logarithmic modulus r with L^2*r <= 8*logU.
Does not import original QH.twistK and does not use h78.
Mathematical method Alpoge-Claude; proof adaptation GPT-6.
Program director Maicol Borghetti.
-/
noncomputable section
namespace BorghettiRH

theorem b2_exp_error_from_admitted_log_budget_v3
    (ε B c A₀ : ℝ) (hε : 0 < ε) (hB : 0 < B) (hc : 0 < c) :
    ∃ Y₀ : ℝ, ∀ (Y U lm : ℝ) (m a : ℕ),
      Y₀ ≤ Y → QH.admitted ε Y U m a →
      2 ≤ lm →
      Real.log Y ^ 2 * lm ≤ 8 * Real.log U →
      2 * |A₀| *
        (Real.exp (-(c * Real.log U / lm)) +
          Real.exp (-Real.sqrt (c * Real.log U))) ≤
        Y ^ (-B) / 8 := by
  obtain ⟨x₀, hx₀⟩ :=
    Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.eventually_log_cube
      ((B + 1) ^ 2 / c) (ε / 6)
      (by positivity) (by positivity)
  let L₀ : ℝ := max (max 2
    (8 * (B + Real.log (32 * (|A₀| + 1))) / c))
    (Real.log (32 * (|A₀| + 1)))
  refine ⟨max x₀ (Real.exp L₀), ?_⟩
  intro Y U lm m a hY hAd hlm hBudget
  have hX0le : x₀ ≤ Y := le_trans (le_max_left _ _) hY
  have hYexp : Real.exp L₀ ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hYexp
  have hYlog : L₀ ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hYpos]
    exact hYexp
  have hL : 2 ≤ Real.log Y :=
    (le_max_left _ _).trans (le_max_left _ _).trans hYlog
  have hCl : 8 * (B + Real.log (32 * (|A₀| + 1))) / c ≤ Real.log Y :=
    (le_max_right _ _).trans (le_max_left _ _).trans hYlog
  have hlogQ : Real.log (32 * (|A₀| + 1)) ≤ Real.log Y :=
    (le_max_right _ _).trans hYlog
  have hhuge : ((B + 1) ^ 2 / c) * Real.log Y ^ 3 ≤ Real.log U :=
    (hx₀ Y hX0le).trans hAd.lo
  have hmain :=
    b2_jacobi_exp_envelope_v3 c A₀ B
      (Real.log Y) (Real.log U) lm
      hc hB hL hlm hCl hlogQ hBudget hhuge
  calc
    2 * |A₀| * (Real.exp (-(c * Real.log U / lm)) +
      Real.exp (-Real.sqrt (c * Real.log U))) ≤
        Real.exp (-(B * Real.log Y)) / 8 := hmain
    _ = Y ^ (-B) / 8 := by
      rw [Real.rpow_def_of_pos hYpos]
      congr 1
      ring

#print axioms BorghettiRH.b2_exp_error_from_admitted_log_budget_v3
end BorghettiRH
