import RFH123S.Producers

/-! New route: the one-class criterion specialized to q = 1.
The terminal theorem is conditional on the three named new producer properties.
It neither calls the original terminal GRH result nor assumes RH. -/
open DirichletCharacter Real Finset Filter Data Parameters ZMod Module
namespace RFH123S

lemma right_of_half_at_one
    (hbound : ∀ P : Parameters, P.N₀ = 18480 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop, primeError P.d P.N₀ x ≤ x ^ (ε - 1/2))
    (χ : DirichletCharacter ℂ 1) (ρ : ℂ) (hρ : 1 / 2 < ρ.re)
    (pole : χ ≠ 1 ∨ ρ ≠ 1) : DirichletCharacter.LFunction χ ρ ≠ 0 := by
  intro zero
  set ε := (ρ.re ⊓ 1 - 2⁻¹) / 51
  have induced : entireL (χ.changeLevel (dvd_mul_left 1 18480)) ρ = 0 := by
    rw [entireL]
    grind [LFunction_changeLevel, changeLevel_eq_one_iff]
  refine entireL_ne_zero_of_primeError_le (β := 8 * ε + 2⁻¹) (by grind)
    (.of_mul_eq_one (9240 * 1 - 1) (by grind [natCast_self (18480 * 1)]) :
    IsUnit (9240 * 1 - 1 : ZMod (_ * 1))) (fun d h ↦ ?_) ρ (by grind) _ induced
  let P := Parameters.mk _ d ⟨1, rfl⟩ d.2 (by
    simp [← natCast_eq_zero_iff, h]; norm_cast; simp [↓natCast_eq_zero_iff, ← mul_assoc,
      mul_dvd_mul_iff_right])
  refine ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩, ?_⟩
  simpa only [show 8 * ε + (2 : ℝ)⁻¹ - 1 = 8 * ε - 1/2 by ring] using
    hbound P (by rfl) (8 * ε) (by grind)

/-- Conditional terminal theorem, with the three outstanding inputs visible. -/
theorem rh_of_polylog_producers
    (hdata : ∀ P : Parameters, P.N₀ = 18480 → PolylogDataExists P)
    (hcost : ∀ P : Parameters, P.N₀ = 18480 → PolylogCostBridge P)
    (htail : ∀ P : Parameters, P.N₀ = 18480 → PolylogTailBridge P) :
    RiemannZetaZerosOnLine := fun s ↦ by
  have h := right_of_half_at_one (fun P hP =>
    filtered_bound P (hdata P hP) (hcost P hP) (htail P hP))
  obtain _ := h 1 s, h 1 (1 - s), @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]

#print axioms rh_of_polylog_producers
end RFH123S
