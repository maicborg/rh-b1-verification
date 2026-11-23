import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import B2NoExceptional

/-! RH-S: discharge the PNTAPRelW hypothesis using the actual Alpoge theorem.
The OpenAI 7/8 hypothesis h78 remains EXPLICIT until a cross-toolchain
kernel import is achieved. No custom axioms or sorry. -/
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_pnt_relative_from_actual_alpoge
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧
      ∀ (M : ℕ) [NeZero M], 8 ∣ M →
        ∀ (X : ℝ) (b : ℕ),
          2 ≤ X →
          C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X →
          b.Coprime M →
          |(piAP X M b : ℝ) - liX X / (M.totient : ℝ)| ≤
            A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) +
              Real.exp (-Real.sqrt (c₃ * Real.log X))) *
              (liX X / (M.totient : ℝ)) := by
  exact b2_pnt_relative_without_exception h78
    Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_pnt_relative_from_actual_alpoge
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
