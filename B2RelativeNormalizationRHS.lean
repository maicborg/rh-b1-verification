import Mathlib

/-! RH-S: elementary normalization for the one-endpoint PNT/Jacobi route.
No external OpenAI theorem is assumed or imported. -/
namespace BorghettiRH

theorem b2_relative_normalization
    (P L J δ η τ : ℝ)
    (hP : L ≤ 2 * P)
    (hJ : J ≤ δ * L + η * L)
    (hδ : 2 * (δ + η) ≤ τ)
    (hnonneg : 0 ≤ δ + η)
    (hPnonneg : 0 ≤ P) :
    J ≤ τ * P := by
  calc
    J ≤ (δ + η) * L := by nlinarith [hJ]
    _ ≤ (δ + η) * (2 * P) :=
      mul_le_mul_of_nonneg_left hP hnonneg
    _ = (2 * (δ + η)) * P := by ring
    _ ≤ τ * P := mul_le_mul_of_nonneg_right hδ hPnonneg

#print axioms BorghettiRH.b2_relative_normalization
end BorghettiRH
