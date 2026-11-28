import RFH123S.WindowFromPrimeError
import RFH123S.PrimeErrorSeal

namespace RFH123S
/-- Both original producers are discharged from the SAME analytic input.
This is not an unconditional theorem: UniformPrimeError still needs proof. -/
theorem rh_of_uniformPrimeError (h : UniformPrimeError) :
    RiemannZetaZerosOnLine :=
  rh_of_uniformPrimeError_and_windows h
    (fun P hP ↦ polylogPrimeWindows_of_uniformPrimeError h P)

#print axioms rh_of_uniformPrimeError
end RFH123S
