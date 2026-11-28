import RFH123S.QRHGrowth
import RFH123S.LogDisk

open Complex Metric Set
namespace RFH123S

/-- This disk estimate uses exactly the upstream polynomial growth and
Möbius anchor. The only analytic input is the stated QRH nonvanishing. -/
theorem logDeriv_bound_of_qrh {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hqrh : ∀ z : ℂ, (7/8:ℝ) < z.re → entireL χ z ≠ 0)
    (z : ℂ) (hz1 : (15/16:ℝ) ≤ z.re) (hz2 : z.re ≤ 9/8) :
    ‖logDeriv (entireL χ) z‖ ≤
      320*Real.log (3264*(q:ℝ)*(4+|z.im|)^2) := by
  let a : ℂ := (17/16:ℂ)+(z.im:ℂ)*I
  let B : ℝ := 12*(q:ℝ)*(4+|z.im|)^2
  have ha : a.re = 17/16 := by simp [a,add_re,mul_re]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hB : 1/272 < B := by
    unfold B
    nlinarith [abs_nonneg z.im, sq_nonneg (4+|z.im|),
      mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg (4+|z.im|))]
  have hnorma : ‖a‖ ≤ 17/16+|z.im| := by
    unfold a
    simpa [norm_add_le, norm_mul, Complex.norm_real,Real.norm_eq_abs] using
      norm_add_le (17/16:ℂ) ((z.im:ℂ)*I)
  have hd (w : ℂ) (hw : w ∈ ball a (3*(1/8:ℝ)/2)) :
      (7/8:ℝ) < w.re ∧ ‖w‖ ≤ 2+|z.im| := by
    have hdist : ‖w-a‖ < 3/16 := by simpa [mem_ball,dist_eq_norm] using hw
    have hreal := Complex.abs_re_le_norm (w-a)
    have hn := norm_add_le (w-a) a
    rw [sub_add_cancel] at hn
    simp only [sub_re,ha] at hreal
    constructor
    · linarith [(abs_le.mp hreal).1]
    · linarith
  have hbound (w : ℂ) (hw : w ∈ ball a (3*(1/8:ℝ)/2)) :
      ‖entireL χ w‖ ≤ B := by
    have h := RFH123S.Growth.entireL_growth χ (s := w) (by linarith [(hd w hw).1])
    exact h.trans (by unfold B; gcongr; exact (hd w hw).2)
  have hdz : dist z a ≤ (1/8:ℝ) := by
    have he : z-a = ((z.re-17/16:ℝ):ℂ) := by
      apply Complex.ext <;> simp [a,add_re,mul_re,sub_re,add_im,mul_im,sub_im]
    rw [dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have H := norm_logDeriv_le_small_disk (entireL χ) a z (δ := 1/8) (B := B) (b := 1/272)
    (by norm_num) (by norm_num) hB
    (fun w hw ↦ (analyticAt_entireL χ w).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ hqrh w (hd w hw).1) hbound
    (RFH123S.Growth.entireL_anchor χ z.im) hdz
  convert H using 1
  rw [show B/(1/272:ℝ) = 3264*(q:ℝ)*(4+|z.im|)^2 by unfold B; ring]
  ring

#print axioms logDeriv_bound_of_qrh
end RFH123S
