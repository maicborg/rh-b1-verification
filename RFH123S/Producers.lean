import RFH123S.Point
import RFH123S.Scale

/-! These are the exact outstanding interfaces for the NEW route.
They are propositions, not axioms, and are not asserted as proved. -/
open Real Filter Finset Data Parameters
namespace RFH123S

/-- The new data producer, including optimized Behrend density. -/
def PolylogDataExists (P : Parameters) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∃ D : Data P,
    D.x = x ∧ D.logX₁ = 10^6 * log x ∧ D.logB = (10^6 * log x)^6 ∧
    (0 : ℝ) < #D.thick ∧
    (#D.tops : ℝ) / #D.thick ≤ exp (40 * sqrt (log x * log (log x)))

/-- The explicit formula / QRH 7/8 tail interface for both actual prime errors.
The named exponent is 1/16, obtained on paper by allowing slack in 7/8. -/
def QRHTail (P : Parameters) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : ℝ in atTop,
    |primeError P.d P.N₀ z| ≤ C * z ^ (-(1/16 : ℝ)) ∧
    |primeError P.d 1 z| ≤ C * z ^ (-(1/16 : ℝ))

/-- Quantitative arithmetic bridge for the explicit star budget.
This is not a geometric hypothesis or an RH claim: it is a scalar estimate
on Data at the specified scale. Still to be formalized. -/
def PolylogCostBridge (P : Parameters) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ D : Data P,
    D.x = x → D.logX₁ = 10^6 * log x → D.logB = (10^6 * log x)^6 →
    (0 : ℝ) < #D.thick →
    (#D.tops : ℝ) / #D.thick ≤ exp (40 * sqrt (log x * log (log x))) →
    explicitCost D ≤ x ^ (ε - 1/2) / 2

/-- Remaining scalar tail absorption, separately testable. It uses no geometry.
QRHTail implies this on paper, but that implication is not claimed compiled. -/
def PolylogTailBridge (P : Parameters) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ D : Data P,
    D.x = x → D.logX₁ = 10^6 * log x → D.logB = (10^6 * log x)^6 →
    (0 : ℝ) < #D.thick →
    (#D.tops : ℝ) / #D.thick ≤ exp (40 * sqrt (log x * log (log x))) →
    tail D ≤ x ^ (ε - 1/2) / 2

lemma filtered_bound (P : Parameters) (hd : PolylogDataExists P)
    (hc : PolylogCostBridge P) (ht : PolylogTailBridge P)
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, primeError P.d P.N₀ x ≤ x ^ (ε - 1/2) := by
  filter_upwards [hd, hc ε he, ht ε he] with x hx hcost htail
  obtain ⟨D, hDx, hX1, hB, hT, hden⟩ := hx
  have h := point_bound D hT
  rw [hDx] at h
  have hc' := hcost D hDx hX1 hB hT hden
  have ht' := htail D hDx hX1 hB hT hden
  exact h.trans (by linarith [hc', ht'])

end RFH123S
