import Mathlib

/-!
B2 relative error budget: a rigorously checked elementary bridge from
the same prime progression count and the same Jacobi sum to the desired
relative bound. Unlike previous versions, uses the ORIGINAL Alpoge
count_a-type estimate R<=d*P rather than an extra estimate R<=eta*T.
This module contains no analytic assumptions hidden as axioms.
Direction Maicol Borghetti. Formalization GPT-6.
-/

namespace BorghettiRH

theorem b2_small_error_budget
    (P pi T R J d δp δj τ : ℝ)
    (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hd : 0 ≤ d) (hδj : 0 ≤ δj) (hτ : 0 ≤ τ)
    (hdsmall : d ≤ τ / 4)
    (hτsmall : τ ≤ 1)
    (hδpsmall : δp ≤ 1 / 8)
    (hδjsmall : 2 * δj ≤ τ / 2)
    (hpi : |pi - T| ≤ δp * T)
    (hPcount : pi - R ≤ P)
    (hR : R ≤ d * P)
    (hJ : J ≤ δj * T + R) :
    T ≤ 2 * P ∧ J ≤ τ * P := by
  have hPL : -(δp * T) ≤ pi - T := (abs_le.mp hpi).1
  have hδP : δp * T ≤ (1 / 8 : ℝ) * T :=
    mul_le_mul_of_nonneg_right hδpsmall hT
  have hdquarter : d ≤ (1 / 4 : ℝ) := by linarith
  have hdP : d * P ≤ (1 / 4 : ℝ) * P :=
    mul_le_mul_of_nonneg_right hdquarter hP
  have hT2 : T ≤ 2 * P := by nlinarith [hPL, hδP, hdP, hPcount, hR]
  have hδj2 : δj * T ≤ δj * (2 * P) :=
    mul_le_mul_of_nonneg_left hT2 hδj
  have hdτ : d ≤ τ / 4 := hdsmall
  have hdτP : d * P ≤ (τ / 4) * P :=
    mul_le_mul_of_nonneg_right hdτ hP
  constructor
  · exact hT2
  · nlinarith [hJ, hR, hδj2, hdτP, mul_le_mul_of_nonneg_right hδjsmall hP]

#print axioms BorghettiRH.b2_small_error_budget
end BorghettiRH
