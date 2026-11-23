import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.B2AdmittedLogModulus
import Development.AutomorphicArithmetic.MeanSquareBounds.B2PNTThresholdFromBudget

/-!
Uniform BOTH modulus thresholds from the ORIGINAL QH.admitted,
no imported or assumed QH.twistK, no h78 required.
Uses Alpoge's eventually_log_cube and the independently
compiled PNT logarithmic-budget inequality.
Director Maicol Borghetti. Formalization GPT-6.
-/
noncomputable section
namespace BorghettiRH

theorem b2_pnt_two_thresholds_from_admitted
    (ε A C₀ : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ Y₀ : ℝ, ∀ (Y U : ℝ) (m a s : ℕ),
      Y₀ ≤ Y → QH.admitted ε Y U m a →
      1 < s → (s : ℝ) ≤ Y ^ A →
      C₀ * Real.log m * Real.log (Real.log m + 2) ≤ Real.log U ∧
      C₀ * Real.log (m * s) *
        Real.log (Real.log (m * s) + 2) ≤ Real.log U := by
  obtain ⟨x₀, hx₀⟩ := b2_admitted_log_modulus_budget ε A hε hA
  let L₀ : ℝ := max 2
    (8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1))
  refine ⟨max x₀ (Real.exp L₀), ?_⟩
  intro Y U m a s hY hAd hs hsBound
  have hx₀ : x₀ ≤ Y := le_trans (le_max_left _ _) hY
  have hYL : Real.exp L₀ ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hYL
  have hLbound : L₀ ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hYpos]
    exact hYL
  have hL : 2 ≤ Real.log Y := (le_max_left _ _).trans hLbound
  have hLC : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ Real.log Y :=
    (le_max_right _ _).trans hLbound
  have hL0 : 0 ≤ Real.log Y := by linarith
  have hL2 : 0 < Real.log Y ^ 2 := by positivity
  have hm8 : 8 ≤ m := Nat.le_of_dvd hAd.pos hAd.eight
  have hm8r : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
  have hms8 : (8 : ℝ) ≤ ((m * s : ℕ) : ℝ) := by
    have hspos : 0 < s := by omega
    have : m ≤ m * s := Nat.le_mul_of_pos_right _ hspos
    exact_mod_cast hm8.trans this
  have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 :=
      Real.log_two_gt_d9
    have he : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlm : 2 ≤ Real.log (m : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) hm8r)
  have hlms : 2 ≤ Real.log ((m * s : ℕ) : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) hms8)
  have hYm : Y ^ (ε / 5) =
      Real.exp (ε / 5 * Real.log Y) := by
    rw [Real.rpow_def_of_pos hYpos, mul_comm]
  have hmul := hAd.log_m.trans hAd.hi
  rw [hYm] at hmul
  have hmu : Real.log (m : ℝ) / 4 * Real.log Y ^ 2 ≤
      Real.exp (ε / 5 * Real.log Y) * Real.log Y ^ 2 := by
    nlinarith [hmul]
  have hmu' := le_of_mul_le_mul_right hmu hL2
  have hmUpper : Real.log (m : ℝ) ≤
      4 * Real.exp (ε / 5 * Real.log Y) := by nlinarith [hmu']
  have hYlogBound : Real.log ((m * s : ℕ) : ℝ) ≤
      Real.log (m : ℝ) + A * Real.log Y := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hAd.pos
    have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hslog : Real.log (s : ℝ) ≤ A * Real.log Y := by
      calc
        Real.log (s : ℝ) ≤ Real.log (Y ^ A) :=
          Real.log_le_log hspos hsBound
        _ = A * Real.log Y := Real.log_rpow hYpos
    rw [Nat.cast_mul, Real.log_mul hmpos.ne' hspos.ne']
    linarith
  have ht0 : 0 ≤ Real.log U :=
    (Real.rpow_nonneg hYpos.le _).trans hAd.lo
  have hbudgetM : Real.log Y ^ 2 * Real.log (m : ℝ) ≤
      8 * Real.log U := by nlinarith [hAd.log_m, ht0]
  have hbudgetMS : Real.log Y ^ 2 * Real.log ((m * s : ℕ) : ℝ) ≤
      8 * Real.log U :=
    hx₀ Y U m a s hx₀ hAd hs hsBound
  constructor
  · apply b2_pnt_threshold_of_log_budget A ε C₀
      (Real.log Y) (Real.log U) (Real.log (m : ℝ))
      (Real.log (m : ℝ)) hA hε hL hLC hlm
    · nlinarith [mul_nonneg hA.le hL0]
    · exact hmUpper
    · exact hbudgetM
  · exact b2_pnt_threshold_of_log_budget A ε C₀
      (Real.log Y) (Real.log U) (Real.log ((m * s : ℕ) : ℝ))
      (Real.log (m : ℝ)) hA hε hL hLC hlms
      hYlogBound hmUpper hbudgetMS

#print axioms BorghettiRH.b2_pnt_two_thresholds_from_admitted
end BorghettiRH
