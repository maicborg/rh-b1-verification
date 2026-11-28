import RFH123S.ReducedFinal
import RFH123S.DataAssembly

namespace RFH123S
/-- Remaining frontier: two analytic statements, with the entire
geometric construction supplied by the preceding theorem. -/
theorem rh_of_polylog_primeWindows_and_qrhTail
    (hwin : ∀ P : Parameters, P.N₀ = 18480 → PolylogPrimeWindows P)
    (htail : ∀ P : Parameters, P.N₀ = 18480 → QRHTail P) :
    RiemannZetaZerosOnLine :=
  rh_of_polylog_data_and_qrhTail
    (fun P hP => polylogDataExists_of_primeWindows P (hwin P hP)) htail

#print axioms rh_of_polylog_primeWindows_and_qrhTail
end RFH123S
