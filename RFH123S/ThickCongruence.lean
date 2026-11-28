import RFH123S.ThickOrder

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- Every member of the Behrend coset has the required simultaneous
negative-one congruences, independently of the size of the set. -/
lemma thick_coset_congruence (P : Parameters) (s : ℕ)
    (T : Finset (P.Φ s))
    (hT : ∀ σ ∈ T, ∃ e : ℕ, σ = P.placeOfInt s (-1) *
      (P.placeOfInt s ((P.N₀ * 3 ^ (Nat.log 3 s + 5) : ℕ) + 1)) ^ e)
    {m : ℕ} (d : m ∣ P.N₁ s) (hd : m ∣ P.N₀ * 3 ^ (Nat.log 3 s + 5)) :
    ∀ σ ∈ T, P.placeClass d σ = -1 := by
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  intro σ hσ
  obtain ⟨e, rfl⟩ := hT σ hσ
  have H := @Parameters.placeClass_placeOfInt P s (M + 1)
    (mod_cast by simp [M]) (m := m) (d := d)
  have hz : (M : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff M m).2 hd
  change P.placeClass d (P.placeOfInt s (-1) * (P.placeOfInt s ((M : ℤ) + 1)) ^ e) = -1
  have hp : P.placeClass d (P.placeOfInt s ((M : ℤ) + 1)) = 1 := by
    apply Units.ext
    rw [H]
    simp [hz]
  rw [map_mul, map_pow, hp, one_pow, mul_one]
  apply Units.ext
  simpa using (@Parameters.placeClass_placeOfInt P s (-1)
    isCoprime_one_left.neg_left (m := m) (d := d))

#print axioms thick_coset_congruence
end RFH123S
