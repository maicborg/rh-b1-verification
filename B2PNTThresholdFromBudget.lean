import Mathlib

/-!
B2 quantitative PNT threshold, independent of QH.twistK.
Proof pattern follows Alpoge-Claude, original private final_ineqK,
extracted with smaller dependencies and explicit assumptions.
No new zero-free claim.
Director: Maicol Borghetti; Lean adaptation: GPT-6.
-/
namespace BorghettiRH

theorem b2_pnt_threshold_of_log_budget
    (A ε C₀ L t lm lm₀ : ℝ)
    (hA : 0 < A) (hε : 0 < ε)
    (hL : 2 ≤ L)
    (hC : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ L)
    (hlm : 2 ≤ lm) (hlm_upper : lm ≤ lm₀ + A * L)
    (hlm₀_upper : lm₀ ≤ 4 * Real.exp (ε / 5 * L))
    (hbudget : L ^ 2 * lm ≤ 8 * t) :
    C₀ * lm * Real.log (lm + 2) ≤ t := by
  have hL0 : 0 ≤ L := by linarith
  have hlm0 : 0 ≤ lm := by linarith
  have hlog6 : 0 ≤ Real.log (6 + A) :=
    Real.log_nonneg (by linarith)
  have hlog0 : 0 ≤ Real.log (lm + 2) :=
    Real.log_nonneg (by linarith)
  have hE1 : Real.exp (ε / 5 * L) ≤
      Real.exp ((ε / 5 + 1) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hE2 : L ≤ Real.exp ((ε / 5 + 1) * L) := by
    have h := Real.add_one_le_exp L
    have hh : Real.exp L ≤ Real.exp ((ε / 5 + 1) * L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hE3 : 1 ≤ Real.exp ((ε / 5 + 1) * L) :=
    Real.one_le_exp (by positivity)
  have hlmB : lm + 2 ≤
      (6 + A) * Real.exp ((ε / 5 + 1) * L) := by
    nlinarith [hE1,hE2,hE3,hlm_upper,hlm₀_upper]
  have hlogB : Real.log (lm + 2) ≤
      Real.log (6 + A) + (ε / 5 + 1) * L := by
    calc
      Real.log (lm + 2) ≤
        Real.log ((6 + A) * Real.exp ((ε / 5 + 1) * L)) :=
          Real.log_le_log (by linarith) hlmB
      _ = _ := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
          Real.log_exp]
  have hlog6L : Real.log (6 + A) ≤ Real.log (6 + A) * L := by
    nlinarith [hlog6]
  have hh : |C₀| * Real.log (lm + 2) ≤ L ^ 2 / 8 := by
    have a := mul_le_mul_of_nonneg_left hlogB (abs_nonneg C₀)
    have b := mul_le_mul_of_nonneg_right hC hL0
    nlinarith [a,b,hlog6L]
  calc
    C₀ * lm * Real.log (lm + 2) ≤
        |C₀| * lm * Real.log (lm + 2) := by
          apply mul_le_mul_of_nonneg_right _ hlog0
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hlm0
    _ = lm * (|C₀| * Real.log (lm + 2)) := by ring
    _ ≤ lm * (L ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hh hlm0
    _ ≤ t := by nlinarith [hbudget]

#print axioms BorghettiRH.b2_pnt_threshold_of_log_budget
end BorghettiRH
