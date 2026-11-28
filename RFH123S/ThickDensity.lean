import RFH123S.ThickCongruence
import RFH123S.DensityAssemble

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- Existence of the actual thick places at the optimized density,
not just a scalar bound on a hypothetical cardinality. -/
theorem eventually_thick_density (P : Parameters) :
    ∀ᶠ u : ℝ in atTop, ∀ o : ℕ,
      (2 : ℝ)^(o+1) ∈ Set.Icc (exp (u/2)) (2*exp (u/2)) →
      ((o+1)*22 : ℝ) ≤ 32*u →
      let s := (o+1)*22
      ∃ T : Finset (P.Φ s),
        (0 : ℝ) < #T ∧ (towerDeg s : ℝ) / #T ≤ exp (40*sqrt (u*log u)) ∧
        (∀ {m : ℕ} (d : m ∣ P.N₁ s), m ∣ P.N₀*3^(Nat.log 3 s+5) →
          ∀ σ ∈ T, P.placeClass d σ = -1) ∧
        (∀ i j : ℕ, 0 < i → i < j → j ≤ 324*s →
          ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T,
            (P.placeClass P.two_pow_dvd_N₁ (τ/σ))^j =
              (P.placeClass P.two_pow_dvd_N₁ (ρ/σ))^i →
            P.placeClass P.two_pow_dvd_N₁ (τ/σ) = 1) := by
  filter_upwards [eventually_density_parameters P.N₀] with u hu o hm hsu
  let s := (o+1)*22
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨q,A,hq,hA,hfit,hd⟩ := hu o hm hsu
  obtain ⟨T,hcos,hcard,hthree⟩ := exists_thick_variable P s q A hs hfit
  obtain ⟨hT,hden⟩ := hd (#T : ℝ) hcard
  refine ⟨T,hT,?_,?_,hthree⟩
  · simpa [towerDeg] using hden
  · intro m d h
    exact thick_coset_congruence P s T hcos d h

#print axioms eventually_thick_density
end RFH123S
