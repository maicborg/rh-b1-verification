import RFH123S.Star

open Real Finset Filter Data Parameters
namespace RFH123S

noncomputable def explicitCost {P} (D : Data P) : ℝ :=
  (4 * (D.logB * D.budget) + 4 * D.x ^ 99 +
    10 * log (1 + D.b ^ 2) * D.budget) / D.m / D.a / #D.thick

noncomputable def tail {P} (D : Data P) : ℝ :=
  primeError P.d P.N₀ D.x₁ - (#D.tops : ℝ) / #D.thick * primeError P.d 1 D.x₁

lemma point_bound {P} (D : Data P) (hT : (0 : ℝ) < #D.thick) :
    primeError P.d P.N₀ D.x ≤ explicitCost D + tail D := by
  have hm : (0 : ℝ) < D.m := HasLogBound.pos D
  have ha : (0 : ℝ) < D.a := HasLogBound.pos D
  have he : primeError P.d P.N₀ D.x =
      D.m * D.remainder / D.m / D.a / #D.thick + tail D := by
    rw [D.remainder_eq]
    unfold tail
    field_simp [hm.ne', ha.ne', hT.ne'] <;> ring
  rw [he, explicitCost]
  exact add_le_add_left
    (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (star_explicit (D := D)) hm.le) ha.le) hT.le) _

lemma tail_bound {P} (D : Data P) (E : ℝ) (hE : 0 ≤ E)
    (hT : (0 : ℝ) < #D.thick)
    (hM : |primeError P.d P.N₀ D.x₁| ≤ E)
    (h1 : |primeError P.d 1 D.x₁| ≤ E) :
    tail D ≤ (1 + (#D.tops : ℝ) / #D.thick) * E := by
  have hr : 0 ≤ (#D.tops : ℝ) / #D.thick := by positivity
  unfold tail
  have hM' := (le_abs_self _).trans hM
  have h1' : -primeError P.d 1 D.x₁ ≤ E := (neg_le_abs _).trans h1
  have hp := mul_le_mul_of_nonneg_left h1' hr
  linarith

end RFH123S
