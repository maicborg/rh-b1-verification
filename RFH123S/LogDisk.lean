import Mathlib

/-!
Generic disk lemmas adapted from subfish-zhou/goldbach-lean,
commit 9d4c3a4010d42aedd9e7231bf94386019cfffccc, research/wu2008/src/MathlibNt/AnalyticNumberTheory/DirichletL/
DirichletLCharacterHolomorphicLog.lean and
DirichletLZeroFreeHalfPlaneLogDerivative.lean.
Apache-2.0; license retained in RFH123S/third_party/GOLDBACH-LICENSE.
Changes: standalone Mathlib import, namespace RFH123S, audit, defensive tactics.
No prime or RH theorem imported.
-/
open Complex Metric Set Filter
open scoped Topology
namespace RFH123S
noncomputable section

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm
on that disk.  This is the disk-specialised, differentiable version of the
continuous lifting theorem for the exponential covering map. -/
theorem exists_holomorphicLog_on_ball
    (g : ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball c R) ∧
      EqOn (fun z ↦ exp (h z)) g (ball c R) := by
  let U : Set ℂ := ball c R
  have hc : c ∈ U := mem_ball_self hR
  have hlogDeriv : DifferentiableOn ℂ (fun z ↦ deriv g z / g z) U :=
    (hg.deriv isOpen_ball).div hg hg0
  obtain ⟨h, hhc, hh'⟩ :=
    hlogDeriv.isExactOn_ball.with_val_at c (log (g c))
  have hh : DifferentiableOn ℂ h U := fun z hz ↦
    (hh' z hz).differentiableAt.differentiableWithinAt
  let F : ℂ → ℂ := fun z ↦ exp (h z) / g z
  have hF : DifferentiableOn ℂ F U := hh.cexp.div hg hg0
  have hFderiv : ∀ z ∈ U, deriv F z = 0 := by
    intro z hz
    have hgd : DifferentiableAt ℂ g z :=
      (hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    have hde : deriv (fun w ↦ exp (h w)) z =
        exp (h z) * (deriv g z / g z) := by
      simpa only [(hh' z hz).deriv] using (hh' z hz).cexp.deriv
    rw [show deriv F z = deriv (fun w ↦ exp (h w) / g w) z by rfl,
      deriv_fun_div (hh' z hz).differentiableAt.cexp hgd (hg0 z hz), hde]
    field_simp [hg0 z hz] <;> ring
  have hFc : F c = 1 := by
    have hgc : g c ≠ 0 := hg0 c hc
    simp [F, hhc, exp_log hgc, hgc]
  have hconst : EqOn F (fun _ : ℂ ↦ 1) U :=
    isOpen_ball.eqOn_of_deriv_eq isPreconnected_ball hF (differentiableOn_const 1)
      (fun z hz ↦ by simp [hFderiv z hz]) hc hFc
  refine ⟨h, hh, ?_⟩
  intro z hz
  have hzconst := hconst hz
  change exp (h z) / g z = 1 at hzconst
  exact (div_eq_one_iff_eq (hg0 z hz)).mp hzconst

/-- Interior derivative bound from a real-part oscillation at a nearby anchor. -/
theorem norm_deriv_le_small_disk
    (h : ℂ → ℂ) (a z : ℂ) {δ A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hh : DifferentiableOn ℂ h (ball a (3 * δ / 2)))
    (hosc : ∀ w ∈ ball a (3 * δ / 2), (h w).re - (h a).re ≤ A)
    (hz : dist z a ≤ δ) : ‖deriv h z‖ ≤ 40 * A / δ := by
  let H : ℂ → ℂ := fun w ↦ h (a + w) - h a
  have hR : 0 < 3 * δ / 2 := by positivity
  have hHd : DifferentiableOn ℂ H (ball 0 (3 * δ / 2)) := by
    intro w hw
    have haw : a + w ∈ ball a (3 * δ / 2) := by
      simpa [mem_ball, dist_comm] using hw
    have hhat := (hh (a + w) haw).differentiableAt (isOpen_ball.mem_nhds haw)
    exact ((hhat.comp w (by fun_prop)).sub
      (differentiableAt_const (h a))).differentiableWithinAt
  have hHre : MapsTo H (ball 0 (3 * δ / 2)) {w : ℂ | w.re ≤ A} := by
    intro w hw
    change (h (a + w) - h a).re ≤ A
    simpa only [sub_re] using hosc (a + w) (by simpa [mem_ball, dist_comm] using hw)
  have hH0 : H 0 = 0 := by simp [H]
  have hBC : ∀ w : ℂ, dist w a ≤ 5 * δ / 4 → ‖h w - h a‖ ≤ 10 * A := by
    intro w hw
    have hn : ‖w - a‖ ≤ 5 * δ / 4 := by simpa only [dist_eq_norm] using hw
    have hmem : w - a ∈ ball 0 (3 * δ / 2) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    have hbc := borelCaratheodory_zero hA hHd hHre hR hmem hH0
    have hden : 0 < 3 * δ / 2 - ‖w - a‖ := by linarith
    have hrat : 2 * ‖w - a‖ / (3 * δ / 2 - ‖w - a‖) * A ≤ 10 * A := by
      apply mul_le_mul_of_nonneg_right _ hA.le
      apply (div_le_iff₀ hden).2
      linarith
    have heval : H (w - a) = h w - h a := by simp [H]
    rw [heval] at hbc
    apply hbc.trans
    calc
      _ = 2 * ‖w - a‖ / (3 * δ / 2 - ‖w - a‖) * A := by ring
      _ ≤ 10 * A := hrat
  have hquarter : 0 < δ / 4 := by positivity
  -- The Cauchy disk stays within the radius controlled by Borel–Carathéodory.
  have hdist : ∀ w ∈ closedBall z (δ / 4), dist w a ≤ 5 * δ / 4 := by
    intro w hw
    calc
      dist w a ≤ dist w z + dist z a := dist_triangle w z a
      _ ≤ δ / 4 + δ := add_le_add (mem_closedBall.mp hw) hz
      _ = 5 * δ / 4 := by ring
  have hsub : closedBall z (δ / 4) ⊆ ball a (3 * δ / 2) := by
    intro w hw
    exact mem_ball.mpr ((hdist w hw).trans_lt (by linarith))
  let F : ℂ → ℂ := fun w ↦ h w - h a
  have hFd : DifferentiableOn ℂ F (ball a (3 * δ / 2)) := hh.sub (differentiableOn_const _)
  have hcont : DiffContOnCl ℂ F (ball z (δ / 4)) := by
    refine ⟨hFd.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z hquarter.ne']
    exact hFd.continuousOn.mono hsub
  have hcircle : ∀ w ∈ sphere z (δ / 4), ‖F w‖ ≤ 10 * A := by
    intro w hw
    exact hBC w (hdist w (mem_closedBall.mpr (mem_sphere.mp hw).le))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hquarter hcont hcircle
  have hd : deriv F z = deriv h z := deriv_sub_const _
  rw [hd] at hc
  convert hc using 1
  field_simp <;> ring

/-- The logarithm and its amplitude are constructed internally from nonvanishing,
a growth bound and a single lower anchor. No logarithm branch is assumed. -/
theorem norm_logDeriv_le_small_disk
    (g : ℂ → ℂ) (a z : ℂ) {δ B b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (hbB : b < B)
    (hg : DifferentiableOn ℂ g (ball a (3 * δ / 2)))
    (hg0 : ∀ w ∈ ball a (3 * δ / 2), g w ≠ 0)
    (hbound : ∀ w ∈ ball a (3 * δ / 2), ‖g w‖ ≤ B)
    (hanchor : b ≤ ‖g a‖) (hz : dist z a ≤ δ) :
    ‖logDeriv g z‖ ≤ 40 * Real.log (B / b) / δ := by
  have hR : 0 < 3 * δ / 2 := by positivity
  have ha : a ∈ ball a (3 * δ / 2) := mem_ball_self hR
  have hzmem : z ∈ ball a (3 * δ / 2) := by rw [mem_ball]; linarith
  obtain ⟨h, hh, hexp⟩ := exists_holomorphicLog_on_ball g a hR hg hg0
  have hre : ∀ w ∈ ball a (3 * δ / 2), (h w).re = Real.log ‖g w‖ := by
    intro w hw
    rw [← hexp hw, Complex.norm_exp, Real.log_exp]
  have hB : 0 < B := hb.trans hbB
  have hosc : ∀ w ∈ ball a (3 * δ / 2), (h w).re - (h a).re ≤ Real.log (B / b) := by
    intro w hw
    rw [hre w hw, hre a ha, Real.log_div hB.ne' hb.ne']
    exact sub_le_sub (Real.log_le_log (norm_pos_iff.mpr (hg0 w hw)) (hbound w hw))
      (Real.log_le_log hb hanchor)
  have hA : 0 < Real.log (B / b) := Real.log_pos ((one_lt_div hb).2 hbB)
  have hd := norm_deriv_le_small_disk h a z hδ hA hh hosc hz
  have hhd := (hh z hzmem).differentiableAt (isOpen_ball.mem_nhds hzmem)
  have hevent : (fun w ↦ exp (h w)) =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_ball.mem_nhds hzmem] with w hw
    exact hexp hw
  have hderiv : deriv g z = g z * deriv h z := by
    rw [← hevent.deriv_eq]
    simpa [hexp hzmem] using hhd.hasDerivAt.cexp.deriv
  rw [logDeriv_apply, hderiv, mul_div_cancel_left₀ _ (hg0 z hzmem)]
  exact hd

#print axioms exists_holomorphicLog_on_ball
#print axioms norm_deriv_le_small_disk
#print axioms norm_logDeriv_le_small_disk
end
end RFH123S
