import Mathlib

/-! B2 auxiliary: primes above the combined CRT modulus cannot divide it.
Direction: Maicol Borghetti; Lean proof: GPT-6.
This is elementary and does not discharge the analytic PNT or OpenAI bridge. -/

namespace BorghettiRH

theorem b2_prime_above_modulus_not_dvd
    (q M : ℕ) (hM : 0 < M) (hq : M < q) : ¬ q ∣ M := by
  intro h
  have hle : q ≤ M := Nat.le_of_dvd hM h
  omega

#print axioms BorghettiRH.b2_prime_above_modulus_not_dvd

end BorghettiRH
