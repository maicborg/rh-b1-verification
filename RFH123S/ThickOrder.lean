import New.Data.DataExist

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- The order bound used in the original construction, extracted without
any of the old scale or prime-window assumptions. -/
lemma thick_order_lower (P : Parameters) (s : ℕ) :
    2 ^ s ≤ (P.N₀ * 3 ^ (Nat.log 3 s + 5) + 2) *
      orderOf (P.placeClass P.two_pow_dvd_N₁
        (P.placeOfInt s ((P.N₀ * 3 ^ (Nat.log 3 s + 5) : ℕ) + 1))) := by
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  have H := @Parameters.placeClass_placeOfInt P s (M + 1) (mod_cast by simp [M])
    (m := 2 ^ (s + 1)) (d := P.two_pow_dvd_N₁)
  let g := P.placeClass P.two_pow_dvd_N₁ (P.placeOfInt s (M + 1))
  have Hg : (g : ZMod (2 ^ (s + 1))) = ((M : ℤ) + 1 : ℤ) := H
  have hp : (g : ZMod (2 ^ (s + 1))) ^ orderOf g = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
    rfl
  have hpow : (((M : ℤ) + 1 : ℤ) : ZMod (2 ^ (s + 1))) ^ orderOf g = 1 := by
    rw [← Hg]
    exact hp
  have h := @two_pow_le_of_pow_eq_one (M + 1) (mod_cast by simp [M]) (orderOf g) s
    (orderOf_pos g) hpow
  have hAbs : ((M : ℤ) + 1).natAbs = M + 1 := by
    exact_mod_cast (Int.natAbs_natCast (M + 1))
  rw [hAbs] at h
  simpa [M, g] using h

/-- Behrend in the actual group of infinite places, with freely chosen
dimension and base instead of the original fixed dimension. -/
lemma exists_thick_variable (P : Parameters) (s n A : ℕ)
    (hs : 0 < s)
    (hfit : (324 * s * A) ^ n * (P.N₀ * 3 ^ (Nat.log 3 s + 5) + 2) ≤ 2 ^ s) :
    ∃ T : Finset (P.Φ s),
      (∀ σ ∈ T, ∃ e : ℕ, σ = P.placeOfInt s (-1) *
        (P.placeOfInt s ((P.N₀ * 3 ^ (Nat.log 3 s + 5) : ℕ) + 1)) ^ e) ∧
      (A ^ n / (n * A ^ 2) : ℝ) ≤ #T ∧
      (∀ i j : ℕ, 0 < i → i < j → j ≤ 324 * s →
        ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T,
          (P.placeClass P.two_pow_dvd_N₁ (τ / σ)) ^ j =
          (P.placeClass P.two_pow_dvd_N₁ (ρ / σ)) ^ i →
          P.placeClass P.two_pow_dvd_N₁ (τ / σ) = 1) := by
  have hb := thick_order_lower P s
  have hp : 0 < P.N₀ * 3 ^ (Nat.log 3 s + 5) + 2 := by omega
  have hle : (324 * s * A) ^ n ≤
      orderOf (P.placeClass P.two_pow_dvd_N₁
        (P.placeOfInt s ((P.N₀ * 3 ^ (Nat.log 3 s + 5) : ℕ) + 1))) := by
    exact Nat.le_of_mul_le_mul_right (hfit.trans (by simpa only [Nat.mul_comm] using hb)) hp
  exact exists_three_term_free (P.placeClass P.two_pow_dvd_N₁)
    (P.placeOfInt s (-1))
    (P.placeOfInt s ((P.N₀ * 3 ^ (Nat.log 3 s + 5) : ℕ) + 1))
    n A (324 * s) (by omega) hle

end RFH123S
