import RFH123S.Producers
import RFH123S.CostLocal
import RFH123S.CostAsymptotic

open Real Filter Finset Data Parameters
namespace RFH123S

/-- Production of the cost bridge, from the existing geometry and elementary asymptotics. -/
theorem polylogCostBridge_proved (P : Parameters) : PolylogCostBridge P := by
  intro e he
  have hc : (0 : ℝ) < 2 * ((P.N₀.totient : ℝ) + 1) := by positivity
  have hA := (eventually_cost_exp (2 * ((P.N₀.totient : ℝ) + 1)) e hc he).comp_tendsto
    Real.tendsto_log_atTop
  filter_upwards [hA] with x hx D hDx hX1 hB hT hden
  have hm : exp (D.logX / 2) ≤ (D.m : ℝ) := D.m_mem.1
  have hlog : log x = D.logX := by rw [← hDx]; exact Real.log_exp _
  have hxpos : 0 < x := by rw [← hDx]; exact Real.exp_pos _
  have hB0 : 0 ≤ D.logB := (HasLogBound.pos D : 0 < D.logB).le
  have hden0 : 0 ≤ (#D.tops : ℝ) / #D.thick := by positivity
  have hnum0 : 0 ≤ (P.N₀.totient : ℝ) * ((#D.tops : ℝ) / #D.thick) *
      D.logB ^ 5 := by positivity
  have hpow : D.logB ^ 5 = (10^6 * log x)^30 := by rw [hB, ← pow_mul]; norm_num
  have hn : (P.N₀.totient : ℝ) * ((#D.tops : ℝ) / #D.thick) *
      D.logB ^ 5 ≤ exp (e * log x) / 2 := by
    rw [hpow]
    have h1 : (P.N₀.totient : ℝ) * ((#D.tops : ℝ) / #D.thick) *
        (10^6 * log x)^30 ≤
        ((P.N₀.totient : ℝ) + 1) * (10^6 * log x)^30 *
          exp (40 * sqrt (log x * log (log x))) := by
      calc
        _ ≤ (P.N₀.totient : ℝ) * exp (40 * sqrt (log x * log (log x))) *
            (10^6 * log x)^30 := by gcongr
        _ = (P.N₀.totient : ℝ) * (10^6 * log x)^30 *
            exp (40 * sqrt (log x * log (log x))) := by ring
        _ ≤ _ := by gcongr; linarith
    linarith only [h1, hx]
  calc
    explicitCost D ≤ _ := explicitCost_majorant D hT
    _ ≤ ((P.N₀.totient : ℝ) * ((#D.tops : ℝ) / #D.thick) * D.logB ^ 5) /
        exp (D.logX / 2) := div_le_div_of_nonneg_left hnum0 (Real.exp_pos _) hm
    _ ≤ (exp (e * log x) / 2) / exp (D.logX / 2) :=
      div_le_div_of_nonneg_right hn (Real.exp_pos _).le
    _ = x ^ (e - 1/2) / 2 := by
      rw [← hlog, Real.rpow_def_of_pos hxpos]
      rw [show log x * (e - 1 / 2) = e * log x - log x / 2 by ring, Real.exp_sub]
      ring

#print axioms polylogCostBridge_proved
end RFH123S
