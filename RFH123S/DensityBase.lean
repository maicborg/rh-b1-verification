import Mathlib

open Real
namespace RFH123S

/-- A power-of-two base avoids real floors. The two inequalities express
capacity and at most a factor two of rounding loss in each coordinate. -/
lemma exists_behrend_base (W L : ℝ) (q : ℕ) (hq : 0 < q)
    (hL : 1 ≤ L) (hW : (2 * L)^q ≤ W) :
    ∃ A : ℕ, 0 < A ∧ (A : ℝ)^q * L^q ≤ W ∧
      W ≤ (A : ℝ)^q * (2 * L)^q := by
  have hLp : 0 < L^q := by positivity
  have hX : 1 ≤ W / L^q := by
    apply (le_div_iff₀ hLp).2
    simpa [one_mul] using
      (calc L^q ≤ (2 * L)^q := by gcongr; linarith
            _ ≤ W := hW)
  have h2 : (1 : ℝ) < (2 : ℝ)^q := one_lt_pow₀ (by norm_num) hq.ne'
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hX h2
  have hlow := (le_div_iff₀ hLp).mp hk
  have hhigh := (div_lt_iff₀ hLp).mp hk'
  refine ⟨2^k, by positivity, ?_, ?_⟩
  · push_cast
    simpa only [← pow_mul, Nat.mul_comm q k] using hlow
  · push_cast
    apply hhigh.le.trans
    rw [pow_succ, ← pow_mul, mul_pow]
    rw [Nat.mul_comm q k]
    ring_nf <;> exact le_rfl

#print axioms exists_behrend_base
end RFH123S
