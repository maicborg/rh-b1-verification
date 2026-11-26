import RFH123S.Star

/-! Reference control: the original Alpöge data and second-window method.
This is NOT the new polylogarithmic route. It is not imported by Final.lean.
No invocation of the terminal theorem in New.Main. -/
open DirichletCharacter Real Finset Filter Data Parameters ZMod Module
namespace RFH123S

lemma original_filtered_bound (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) := by
  filter_upwards [h.elim (exists_data P), tendsto_log_atTop.const_mul_atTop (r := 1e6) (by bound)
    ((isPolar_primeError PrimeSevenModEight.mod_eight (P.coprime_N₁_d
    0).coprime_mul_right).exists_window_sub_mul_le (isPolar_primeError PrimeSevenModEight.mod_eight
    P.d.coprime_one_left))] with x ⟨D, _, _, l, e, H'⟩ W
  subst x; simp only [log_exp, Set.mem_preimage, ← exp_mul] at *
  obtain := D.hasLogLower_of_le H', D.scale
  obtain ⟨u, ⟨a, b⟩, w⟩ := W (towerDeg D.s / #D.thick) ⟨by bound, D.le_of_hasLogBound⟩
  let D' := {D with logX₁ := u, scale := by grw [b, l] <;> grind}
  have := D'.hasLogLower_of_le H'
  calc primeError P.d P.N₀ D.x = D'.m * D'.remainder / D'.m / D'.a / #D.thick + (primeError P.d P.N₀
      D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) := by simp [remainder_eq, tops,
      card_placeClass_eq, field, HasLogBound.pos D', ne_of_gt]
    _ ≤ D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick + exp
      (-(1e6 * D.logX)) := by grw [star_original, w]
    _ ≤ _ := D'.le_of_hasLogBound (by grind)

/-- Control proof reproducing the upstream final argument, not the new path. -/
lemma original_nonvanishing : DirichletLNonvanishingRightOfHalf := fun q _ χ ρ hρ pole zero ↦ by
  set ε := (ρ.re ⊓ 1 - 2⁻¹) / 51
  have induced : entireL (χ.changeLevel (dvd_mul_left q 18480)) ρ = 0 := by
    rw [entireL]
    grind [LFunction_changeLevel, changeLevel_eq_one_iff]
  refine entireL_ne_zero_of_primeError_le (β := 8 * ε + 2⁻¹) (by grind)
    (.of_mul_eq_one (9240 * q - 1) (by grind [natCast_self (18480 * q)]) :
    IsUnit (9240 * q - 1 : ZMod (_ * q))) (fun d h ↦ ?_) ρ (by grind) _ induced
  let P := mk _ d ⟨q, rfl⟩ d.2 (by
    simp [← natCast_eq_zero_iff, h]; norm_cast; simp [↓natCast_eq_zero_iff, ← mul_assoc,
      mul_dvd_mul_iff_right])
  exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
    original_filtered_bound P (by grind)⟩

lemma original_rh_control : RiemannZetaZerosOnLine := fun s ↦ by
  obtain _ := original_nonvanishing 1 1 s, original_nonvanishing 1 1 (1 - s),
    @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]

#print axioms original_rh_control
end RFH123S
