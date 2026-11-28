import Mathlib
namespace RFH123S

/-- The extra discriminant is used only to find auxiliary primes. -/
def auxDiscriminant (d : ℕ) : ℕ := if d = 23 then 31 else 23

lemma auxDiscriminant_prime (d : ℕ) : (auxDiscriminant d).Prime := by
  unfold auxDiscriminant
  split <;> norm_num

lemma auxDiscriminant_mod (d : ℕ) : auxDiscriminant d % 8 = 7 := by
  unfold auxDiscriminant
  split <;> norm_num

lemma auxDiscriminant_le (d : ℕ) : auxDiscriminant d ≤ 31 := by
  unfold auxDiscriminant
  split <;> norm_num

lemma auxDiscriminant_coprime (d s : ℕ) (hd : d.Prime) :
    ((18480 * d) ^ (2 * (s + 6))).Coprime (auxDiscriminant d) := by
  have ha := auxDiscriminant_prime d
  have hne : auxDiscriminant d ≠ d := by
    unfold auxDiscriminant
    split <;> omega
  have h0 : (18480 : ℕ).Coprime (auxDiscriminant d) := by
    unfold auxDiscriminant
    split <;> norm_num
  have h1 : d.Coprime (auxDiscriminant d) := (hd.coprime_iff_not_dvd).2 (by
    intro h
    rcases (Nat.dvd_prime ha).1 h with h | h
    · exact hd.ne_one h
    · exact hne h.symm)
  exact (h0.mul_left h1).pow_left _

lemma modulus_log_bound (d s : ℕ) (u : ℝ) (hd : 0 < d)
    (hu : 1 ≤ u) (hs : (s : ℝ) ≤ 32*u) :
    Real.log (((18480*d) ^ (2*(s+6)) : ℕ) : ℝ) ≤
      (76 * Real.log (18480*(d:ℝ))) * u := by
  push_cast
  rw [Real.log_pow]
  have hp : 0 ≤ Real.log (18480*(d:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)*(s+6) ≤ 76*u by linarith) hp]

#print axioms auxDiscriminant_prime
#print axioms auxDiscriminant_mod
#print axioms auxDiscriminant_coprime
#print axioms modulus_log_bound
end
