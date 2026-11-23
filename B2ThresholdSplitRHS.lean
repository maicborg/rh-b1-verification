import Mathlib

/-! RH-S: additive modulus log-budget, independent of external QRH.
Apply with t = log U, L = log Y, r = log m, v = log s.
The premise hs still requires the bound on s and a Y-threshold. -/
namespace BorghettiRH

theorem b2_log_budget
    (t L r v : ℝ)
    (hm : L ^ 2 * r ≤ 4 * t)
    (hs : L ^ 2 * v ≤ 4 * t) :
    L ^ 2 * (r + v) ≤ 8 * t := by
  nlinarith

#print axioms BorghettiRH.b2_log_budget
end BorghettiRH
