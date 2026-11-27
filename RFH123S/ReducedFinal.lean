import RFH123S.Final
import RFH123S.CostBridge
import RFH123S.TailBridge

namespace RFH123S

/-- Reduced conditional RFH theorem: the cost bridge has been proved, and
the scalar tail bridge follows from the named analytic tail input.
The remaining data-existence and analytic-tail inputs are explicit. -/
theorem rh_of_polylog_data_and_qrhTail
    (hdata : ∀ P : Parameters, P.N₀ = 18480 → PolylogDataExists P)
    (hqrh : ∀ P : Parameters, P.N₀ = 18480 → QRHTail P) :
    RiemannZetaZerosOnLine :=
  rh_of_polylog_producers hdata
    (fun P _ => polylogCostBridge_proved P)
    (fun P hP => polylogTailBridge_of_qrhTail P (hqrh P hP))

#print axioms rh_of_polylog_data_and_qrhTail
end RFH123S
