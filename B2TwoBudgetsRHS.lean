import Mathlib

/-! RH-S B₂: simultaneous quantitative modulus budgets.
Independent real-algebra lemma. The PNT and OpenAI inputs are NOT asserted. -/

namespace BorghettiRH

/-- The two distinct budgets needed for the single-endpoint PNT argument.
Here L2=(log Y)^2, t=log U, lm=log m, ls=log s, AL=A log Y.
The two restrictions on AL are independent. -/
theorem b2_modulus_two_budgets
    (L2 t lm ls AL : ℝ)
    (hL2 : 512 ≤ L2)
    (hlm : 0 ≤ lm)
    (hls : 0 ≤ ls)
    (hmod : L2 * lm ≤ 4 * t)
    (hs : ls ≤ AL)
    (hlinear : 128 * AL ≤ t)
    (hcubic : L2 * AL ≤ 4 * t) :
    64 * (lm + ls) ≤ t ∧ L2 * (lm + ls) ≤ 8 * t := by
  have hm512 : 512 * lm ≤ L2 * lm :=
    mul_le_mul_of_nonneg_right hL2 hlm
  have hm : 128 * lm ≤ t := by
    nlinarith [hm512]
  have hsm : 128 * ls ≤ t := by
    nlinarith [hs, hlinear]
  have hL2nonneg : 0 ≤ L2 := by linarith
  have hsL2 : L2 * ls ≤ L2 * AL :=
    mul_le_mul_of_nonneg_left hs hL2nonneg
  constructor
  · linarith
  · nlinarith [hsL2]

#print axioms BorghettiRH.b2_modulus_two_budgets
end BorghettiRH
