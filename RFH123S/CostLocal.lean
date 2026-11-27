import RFH123S.Point

open Real Finset Data Parameters
namespace RFH123S

/-- Scalar majorant for the actual explicit cost; no asymptotic or prime estimate. -/
lemma explicitCost_majorant {P} (D : Data P) (hT : (0 : ℝ) < #D.thick) :
    explicitCost D ≤ ((P.N₀.totient : ℝ) * ((#D.tops : ℝ) / #D.thick) *
      D.logB ^ 5) / D.m := by
  have hm : (0 : ℝ) < D.m := HasLogBound.pos D
  have ha : (0 : ℝ) < D.a := HasLogBound.pos D
  have hfN : D.f = #D.tops * P.N₀.totient := by
    simp [Data.tops, card_placeClass_eq, card_infinitePlace_E]
  have hf : (D.f : ℝ) = (#D.tops : ℝ) * P.N₀.totient := by exact_mod_cast hfN
  have hnum : 4 * (D.logB * D.budget) + 4 * D.x ^ 99 +
      10 * log (1 + D.b ^ 2) * D.budget ≤ D.logB ^ 2 * D.budget :=
    D.le_of_hasLogBound
  calc
    explicitCost D ≤ D.logB ^ 2 * D.budget / D.m / D.a / #D.thick :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hnum hm.le) ha.le) hT.le
    _ = _ := by
      change D.logB ^ 2 * ((D.f : ℝ) * D.a * D.logB ^ 3) / D.m / D.a / #D.thick = _
      rw [hf]
      field_simp [hm.ne', ha.ne', hT.ne'] <;> ring

end RFH123S
