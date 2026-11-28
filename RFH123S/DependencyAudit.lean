import RFH123S.AnalyticFrontier

open Lean Elab Command
namespace RFH123S

/-- Audit the actual imported environment, not just a list of source names.
The original terminal proof and the diagnostic baseline must be absent. -/
run_cmd do
  let env ← getEnv
  for m in [`New.Main, `RFH123S.Baseline] do
    if env.header.moduleNames.contains m then
      throwError "Unexpected terminal import: {m}"
  if env.contains `RFH123S.original_rh_control then
    throwError "Baseline theorem leaked into the proof environment"
  logInfo "Terminal import exclusion: PASS"

/-- This is deliberately a conditional statement: both remaining
mathematical assumptions must still be discharged. -/
theorem audited_frontier
    (hwin : ∀ P : Parameters, P.N₀ = 18480 → PolylogPrimeWindows P)
    (htail : ∀ P : Parameters, P.N₀ = 18480 → QRHTail P) :
    RiemannZetaZerosOnLine :=
  rh_of_polylog_primeWindows_and_qrhTail hwin htail

#print axioms audited_frontier
#print axioms eventually_thick_density
#print axioms polylogDataExists_of_primeWindows
#print axioms polylogCostBridge_proved
#print axioms polylogTailBridge_of_qrhTail
end RFH123S
