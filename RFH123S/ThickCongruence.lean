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
  simp [M, P.placeClass_placeOfInt isCoprime_one_left.neg_left,
    P.placeClass_placeOfInt (show IsCoprime ((M : ℤ) + 1) P.N₀ by
      mod_cast (by simp [M])),
    Units.ext_iff, (ZMod.natCast_eq_zero_iff M m).2 hd]

end RFH123S
