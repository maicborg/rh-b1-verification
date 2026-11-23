import Mathlib

/-!
RH-S: one-endpoint normalization for the B2 Jacobi/PNT route.
The analytic AP and prime-count bounds are explicit hypotheses, NOT proved here.
Direction: Maicol Borghetti; formalization: GPT-6.
-/
namespace BorghettiRH

theorem b2_single_endpoint_normalization
    (P pi T J R δm δM η : ℝ)
    (hT : 0 ≤ T)
    (hδM : 0 ≤ δM) (hη : 0 ≤ η)
    (hbudget : δm + η ≤ (1 / 2 : ℝ))
    (hpi : |pi - T| ≤ δm * T)
    (hP : pi - R ≤ P)
    (hR : R ≤ η * T)
    (hJ : J ≤ δM * T + R) :
    T / 2 ≤ P ∧ J ≤ (2 * (δM + η)) * P := by
  have hpiLower : -(δm * T) ≤ pi - T := (abs_le.mp hpi).1
  have hslack : 0 ≤ ((1 / 2 : ℝ) - δm - η) := by linarith
  have hslackT := mul_nonneg hslack hT
  have hPlower : T / 2 ≤ P := by nlinarith
  have hJupper : J ≤ (δM + η) * T := by nlinarith
  have hcoef : 0 ≤ δM + η := add_nonneg hδM hη
  have hmul := mul_le_mul_of_nonneg_left hPlower hcoef
  constructor
  · exact hPlower
  · nlinarith [hmul]

#print axioms BorghettiRH.b2_single_endpoint_normalization

end BorghettiRH
