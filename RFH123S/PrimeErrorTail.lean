import RFH123S.Producers
open Real Filter
namespace RFH123S

/-- Exact, still open uniform analytic producer. A proposition, not an axiom. -/
def UniformPrimeError : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (d M : ℕ) [Fact d.Prime] [NeZero M],
    d % 8 = 7 → M.Coprime d → ∀ z : ℝ, 1 ≤ z →
    |primeError d M z| ≤ C * log (2*(M:ℝ)*(d:ℝ)) * z ^ (-(1/16:ℝ))

/-- The fixed-modulus tail follows from the uniform producer. -/
theorem qrhTail_of_uniformPrimeError (h : UniformPrimeError)
    (P : Parameters) : QRHTail P := by
  letI : Fact P.d.Prime := ⟨P.d_prime⟩
  obtain ⟨C,hC,h⟩ := h
  have hd : P.d % 8 = 7 := P.instHeegD.2
  have hm : P.N₀.Coprime P.d := (P.coprime_N₁_d 0).coprime_mul_right
  let A := max 0 (max (C * log (2*(P.N₀:ℝ)*(P.d:ℝ))) (C * log (2*(1:ℝ)*(P.d:ℝ))))
  refine ⟨A, le_max_left _ _, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
  have hpow : 0 ≤ z ^ (-(1/16:ℝ)) := Real.rpow_nonneg (by linarith) _
  constructor
  · exact (h P.d P.N₀ hd hm z hz).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hpow)
  · exact (h P.d 1 hd (Nat.coprime_one_left _) z hz).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hpow)

#print axioms qrhTail_of_uniformPrimeError
end RFH123S
