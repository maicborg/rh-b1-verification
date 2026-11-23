import Mathlib

/-!
B2 independent analytic envelope: formal version of the exponential
absorption step of Alpoge's final_ineqK, isolated from original
QH.twistK, with the intended no-exception output.
Mathematical technique/inequalities: Alpoge-Claude; proof adaptation GPT-6,
research coordination Maicol Borghetti. No assumption of RH.
-/

namespace BorghettiRH

theorem b2_jacobi_exp_envelope_v3
    (c A₀ B L t lm : ℝ)
    (hc : 0 < c) (hB : 0 < B)
    (hL : 2 ≤ L) (hlm : 2 ≤ lm)
    (hCl : 8 * (B + Real.log (32 * (|A₀| + 1))) / c ≤ L)
    (hlogQ : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hbudget : L ^ 2 * lm ≤ 8 * t)
    (hhuge : ((B + 1) ^ 2 / c) * L ^ 3 ≤ t) :
    2 * |A₀| *
      (Real.exp (-(c * t / lm)) + Real.exp (-Real.sqrt (c * t))) ≤
      Real.exp (-(B * L)) / 8 := by
  let Q : ℝ := 32 * (|A₀| + 1)
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQlog : 0 ≤ Real.log Q := Real.log_nonneg (by dsimp [Q]; nlinarith [abs_nonneg A₀])
  have hL0 : 0 < L := by linarith
  have hlmpos : 0 < lm := by linarith
  have htpos : 0 < t := by
    have : 0 < ((B + 1) ^ 2 / c) * L ^ 3 := by positivity
    linarith
  have hratio : L ^ 2 / 8 ≤ t / lm := by
    apply (le_div_iff₀ hlmpos).2
    nlinarith [hbudget]
  have hhead : 8 * (B + Real.log Q) ≤ c * L := by
    have hh : 8 * (B + Real.log Q) / c ≤ L := by
      simpa [Q] using hCl
    have h := (div_le_iff₀ hc).mp hh
    nlinarith [h]
  have hQsmall : Real.log Q ≤ Real.log Q * L := by
    nlinarith [hQlog, hL]
  have ht1 : B * L + Real.log Q ≤ c * t / lm := by
    have hmul := mul_le_mul_of_nonneg_right hhead hL0.le
    have hrat : c * L ^ 2 / 8 ≤ c * t / lm := by
      have hh := mul_le_mul_of_nonneg_left hratio hc.le
      calc
        c * L ^ 2 / 8 = c * (L ^ 2 / 8) := by ring
        _ ≤ c * (t / lm) := hh
        _ = c * t / lm := by ring
    have hSm : B * L + Real.log Q ≤ (B + Real.log Q) * L := by
      nlinarith [hQsmall]
    have hMid : (B + Real.log Q) * L ≤ c * L ^ 2 / 8 := by
      nlinarith [hmul]
    exact hSm.trans (hMid.trans hrat)
  have ht2 : B * L + Real.log Q ≤ Real.sqrt (c * t) := by
    have hroot : (B + 1) * L ≤ Real.sqrt (c * t) := by
      apply Real.le_sqrt_of_sq_le
      have hcube : L ^ 2 ≤ L ^ 3 := by
        nlinarith [sq_nonneg L]
      have hh := mul_le_mul_of_nonneg_left hhuge hc.le
      have heq : c * (((B + 1) ^ 2 / c) * L ^ 3) =
          (B + 1) ^ 2 * L ^ 3 := by field_simp
      nlinarith [hh, hcube, heq, mul_nonneg (sq_nonneg (B + 1)) (sub_nonneg.mpr hcube)]
    linarith [hQsmall]
  have hA : 2 * |A₀| ≤ Q / 16 := by dsimp [Q]; nlinarith [abs_nonneg A₀]
  have key (z : ℝ) (hz : B * L + Real.log Q ≤ z) :
      2 * |A₀| * Real.exp (-z) ≤ Real.exp (-(B * L)) / 16 := by
    calc
      2 * |A₀| * Real.exp (-z) ≤ Q / 16 * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ ≤ Q / 16 * Real.exp (-(B * L) - Real.log Q) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-(B * L)) / 16 := by
        rw [Real.exp_sub, Real.exp_log hQpos]
        field_simp
  have h1 := key (c * t / lm) ht1
  have h2 := key (Real.sqrt (c * t)) ht2
  linarith

#print axioms BorghettiRH.b2_jacobi_exp_envelope_v3
end BorghettiRH
