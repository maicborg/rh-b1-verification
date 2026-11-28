import New.Endgame.PrimeError
open Complex Finset DirichletCharacter Nat
namespace RFH123S
variable {d M : ℕ} [Fact d.Prime] [NeZero M]

/-- The totient cancels the number of characters. No growth in the
number of summands is lost in logDerivMean. -/
theorem norm_logDerivMean_le (s : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h1 : ∀ χ : DirichletCharacter ℂ M, ‖logDeriv (entireL χ) s‖ ≤ B)
    (h2 : ∀ χ : DirichletCharacter ℂ M, ‖logDeriv (entireL (quadTwist χ d)) s‖ ≤ B) :
    ‖logDerivMean d M s‖ ≤ 2*B + 1 := by
  have hp : (0:ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos M)
  have hcard : Fintype.card (DirichletCharacter ℂ M) = M.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity
  unfold logDerivMean
  rw [norm_div]
  have hh : ‖(∑ χ : DirichletCharacter ℂ M,
      (logDeriv (entireL (quadTwist χ d)) s - logDeriv (entireL χ) s))‖ ≤
      (M.totient:ℝ)*(2*B) := calc
    _ ≤ ∑ χ : DirichletCharacter ℂ M,
        ‖logDeriv (entireL (quadTwist χ d)) s - logDeriv (entireL χ) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ M, 2*B := Finset.sum_le_sum (by
      intro χ _
      exact (norm_sub_le _ _).trans (by linarith [h1 χ,h2 χ]))
    _ = _ := by simp [hcard, nsmul_eq_mul]
  have ht := norm_sub_le (∑ χ : DirichletCharacter ℂ M,
      (logDeriv (entireL (quadTwist χ d)) s - logDeriv (entireL χ) s)) (1:ℂ)
  rw [Complex.norm_natCast]
  apply (div_le_iff₀ hp).2
  have hp1 : (1:ℝ) ≤ M.totient := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr (NeZero.pos M)))
  simp only [norm_one] at ht
  nlinarith

#print axioms norm_logDerivMean_le
end RFH123S
