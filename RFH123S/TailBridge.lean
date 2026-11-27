import RFH123S.Producers
import RFH123S.TailScalar

open Real Filter Finset Data Parameters
namespace RFH123S

/-- The QRH tail estimate implies the second missing scalar bridge.
The analytic QRHTail input itself is NOT asserted here. -/
theorem polylogTailBridge_of_qrhTail (P : Parameters) (hqrh : QRHTail P) :
    PolylogTailBridge P := by
  obtain ⟨C, hC, hQ⟩ := hqrh
  intro e he
  have hz : Tendsto (fun x : ℝ => exp (10^6 * log x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop (r := 10^6) (by norm_num))
  have hs := Real.tendsto_log_atTop.eventually (eventually_tail_scalar C e hC he)
  filter_upwards [hz.eventually hQ, hs] with x hQx hS D hDx hX1 hB hT hden
  have hxpos : 0 < x := by rw [← hDx]; exact Real.exp_pos _
  have hZ : D.x₁ = exp (10^6 * log x) := congrArg Real.exp hX1
  have hM : |primeError P.d P.N₀ D.x₁| ≤ C * D.x₁ ^ (-(1/16 : ℝ)) := by
    rw [hZ]
    exact hQx.1
  have h1 : |primeError P.d 1 D.x₁| ≤ C * D.x₁ ^ (-(1/16 : ℝ)) := by
    rw [hZ]
    exact hQx.2
  have hp : D.x₁ ^ (-(1/16 : ℝ)) = exp (-(62500 : ℝ) * log x) := by
    rw [hZ, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1 <;> ring
  calc
    tail D ≤ (1 + (#D.tops : ℝ) / #D.thick) *
        (C * D.x₁ ^ (-(1/16 : ℝ))) :=
      tail_bound D _ (by positivity) hT hM h1
    _ ≤ (1 + exp (40 * sqrt (log x * log (log x)))) *
        (C * exp (-(62500 : ℝ) * log x)) := by
      rw [hp]
      exact mul_le_mul_of_nonneg_right (by linarith only [hden]) (by positivity)
    _ ≤ exp ((e - 1/2) * log x) / 2 := hS
    _ = x ^ (e - 1/2) / 2 := by
      rw [Real.rpow_def_of_pos hxpos]
      congr 2 <;> ring

#print axioms polylogTailBridge_of_qrhTail
end RFH123S
