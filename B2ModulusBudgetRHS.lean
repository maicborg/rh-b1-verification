import Mathlib

/-! B2: independent quantitative modulus-budget lemma.
Director Maicol Borghetti; formalization GPT-6.
No AP theorem, h78, twistK or unproved input is hidden here. -/

namespace BorghettiRH

/-- If L² ≥ 512 and t ≥ 128 A L, the two admitted logarithmic
budgets imply log(m s) ≤ t/64. The factor 128 (not 64) matters. -/
theorem b2_modulus_budget_1_64
    (L2 t lm ls AL : ℝ)
    (hL2 : 512 ≤ L2)
    (hlm : 0 ≤ lm)
    (hls : 0 ≤ ls)
    (ht : 0 ≤ t)
    (hmod : L2 * lm ≤ 4 * t)
    (hs : ls ≤ AL)
    (hAL : 128 * AL ≤ t) :
    64 * (lm + ls) ≤ t := by
  have hscale : 512 * lm ≤ L2 * lm :=
    mul_le_mul_of_nonneg_right hL2 hlm
  have hm : 128 * lm ≤ t := by
    nlinarith [hscale]
  have hsmall : 128 * ls ≤ t := by
    nlinarith [hs, hAL]
  linarith

#print axioms BorghettiRH.b2_modulus_budget_1_64
end BorghettiRH
