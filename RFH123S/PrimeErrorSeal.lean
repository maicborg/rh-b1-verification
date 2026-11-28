import RFH123S.AnalyticFrontier
import RFH123S.PrimeErrorTail

namespace RFH123S
/-- Conditional seal for the new route. This is deliberately NOT called RH:
the uniform analytic producer and the window bridge still have to be proved. -/
theorem rh_of_uniformPrimeError_and_windows
    (h : UniformPrimeError)
    (hw : ∀ P : Parameters, P.N₀ = 18480 → PolylogPrimeWindows P) :
    RiemannZetaZerosOnLine :=
  rh_of_polylog_primeWindows_and_qrhTail hw (fun P _ ↦ qrhTail_of_uniformPrimeError h P)

#print axioms rh_of_uniformPrimeError_and_windows
end RFH123S
