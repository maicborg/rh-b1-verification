import Mathlib

/-! RH-S: elementary modulus log-budget, independent of external QRH. -/
namespace BorghettiRH

theorem b2_log_budget
    (t L r v : ℝ)
    (hm : L ^ 2 * r ≤ 4 * t)
    (hs : L ^ 2 * v ≤ 4 * t) :
    L ^ 2 * (r + v) ≤ 8 * t := by
  nlinarith

theorem b2_pnt_threshold_from_budget
    (t C logM loglogM : ℝ)
    (hC : 0 ≤ C)
    (hlogM : 0 ≤ logM)
    (hloglogM : 0 ≤ loglogM)
    (hbudget : C * logM * loglogM ≤ t) :
    C * logM * loglogM ≤ t := hbudget

#print axioms BorghettiRH.b2_log_budget
end BorghettiRH
