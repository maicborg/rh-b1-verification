import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight

/-!
Direction: Maicol Borghetti. Assembly V2, 2026-11-24.
Source candidate, NOT kernel checked. No Main or terminal RH/GRH theorem
is imported as a premise. Upstream Alpoge pin:
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
The finite transfer below uses the exact upstream GFiniteSplit, not a
new proof of analytic continuation. The final interface uses the singleton
character family and the existing window criterion.
The geometric/arithmetical upper bound remains OPEN.
-/
noncomputable section

namespace BorghettiRH

open Formalism.HermitianLattices.ZeroFreeRegionGL2

/-- Cancel the same tail at two scales using an existing upstream identity. -/
theorem finite_transfer {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x z : ℝ) (hx : 0 < x) (hxz : x ≤ z) :
    Gchi χ x = ((x : ℂ) / (z : ℂ)) * Gchi χ z -
      (Sz χ x z - ((x : ℂ) / (z : ℂ)) * Sz χ z z) := by
  have hz : 0 < z := hx.trans_le hxz
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 := finite_splitting_of_group N χ x z hx hxz
  have h2 := finite_splitting_of_group N χ z z hz le_rfl
  rw [h1, h2]
  field_simp [hz'] <;> ring

/-- Exact bridge from a controlled finite weighted sum and boundary
value to the actual character observable. -/
theorem finite_transfer_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x z B T : ℝ) (hx : 0 < x) (hxz : x ≤ z)
    (hB : ‖((x : ℂ) / (z : ℂ)) * Gchi χ z‖ ≤ B)
    (hT : ‖Sz χ x z - ((x : ℂ) / (z : ℂ)) * Sz χ z z‖ ≤ T) :
    ‖Gchi χ x‖ ≤ B + T := by
  rw [finite_transfer χ x z hx hxz]
  exact (norm_sub_le _ _).trans (add_le_add hB hT)

/-- A singleton family is enough for the analytic conclusion for zeta. -/
def zetaFamily : Deduction.CharFamily :=
  @Deduction.CharFamily.mk Unit inferInstance
    (fun _ => 1) (fun _ => inferInstance)
    (fun _ => (1 : DirichletCharacter ℂ 1))
    (fun _ => 1) (fun _ => one_pos) (fun _ => Or.inl rfl)

theorem zetaFamily_Gm (y : ℝ) : Deduction.Gm zetaFamily y = Deduction.G y := by
  classical
  have hone : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    intro n
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  change (∑ _ : Unit, (1 : ℝ) *
    (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re) = Deduction.G y
  rw [Fintype.sum_unique, one_mul]
  have he : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) =
      (fun _ : ℕ => (1 : ℂ)) := funext hone
  unfold Deduction.Gchi Deduction.G
  rw [if_pos rfl, he]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]

/-- The final RH interface contains only a bound on the genuine zeta
ramp on arbitrarily late windows. This is a conditional reduction.
The missing proof of the hypothesis is the core scientific objective. -/
theorem rh_of_zeta_windows
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
        Deduction.G y ≤ y ^ θ) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  let θ : ℝ := (1 / 2 + min s.re 1) / 2
  have hm : 1 / 2 < min s.re 1 := lt_min hs (by norm_num)
  have hθ : 1 / 2 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith [min_le_right s.re (1 : ℝ)]
  have hθs : θ < s.re := by dsimp [θ]; linarith [min_le_left s.re (1 : ℝ)]
  have hz := Deduction.zeroFree_of_rpow_window zetaFamily
    (θ := θ) (δ := 1 / 2) (C := 1)
    (by linarith) hθ1 (by norm_num) (by
      intro Y₀
      obtain ⟨Y, hY, hw⟩ := h θ hθ hθ1 Y₀
      refine ⟨Y, hY, fun y hy => ?_⟩
      rw [zetaFamily_Gm, one_mul]
      apply hw y
      simpa only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] using hy)
  have hzero := hz () s hθs
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 at hzero
  rwa [DirichletCharacter.LFunction_modOne_eq] at hzero

#print axioms BorghettiRH.finite_transfer
#print axioms BorghettiRH.finite_transfer_bound
#print axioms BorghettiRH.zetaFamily_Gm
#print axioms BorghettiRH.rh_of_zeta_windows
end BorghettiRH
