import Mathlib

/-! B2 elementary modulus barrier, independent of analytic hypotheses.
Direction: Maicol Borghetti; Lean formalization: GPT-6. -/

namespace BorghettiRH

theorem b2_prime_above_modulus_not_dvd
    (q M : ℕ) (hM : 0 < M) (hq : M < q) : ¬ q ∣ M := by
  intro h
  have hle : q ≤ M := Nat.le_of_dvd hM h
  omega

/-- General CRT modulus: if m*s<q then q is coprime to m*s when q is prime. -/
theorem b2_prime_coprime_combined_modulus
    (q m s : ℕ) (hq : q.Prime) (hms : m * s < q) :
    q.Coprime (m * s) := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hdvd
  have hpos : 0 < m * s := Nat.pos_of_dvd_of_pos hdvd hq.pos
  exact (Nat.le_of_dvd hpos hdvd).not_gt hms

#print axioms BorghettiRH.b2_prime_above_modulus_not_dvd
#print axioms BorghettiRH.b2_prime_coprime_combined_modulus

end BorghettiRH
