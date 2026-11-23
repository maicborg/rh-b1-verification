import OAI.NumberTheory.DirichletL.Nonvanishing
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import Development.AutomorphicArithmetic.MeanSquareBounds.B2NoExceptional

/-!
B2 actual proof-term bridge (NOT a new nonvanishing theorem).
Imports the original, pinned OpenAI proof in the same Lean kernel as Alpoge,
eliminates the explicit h78 parameter, and instantiates Alpoge's proved PNTAPRelW.

This is a verification target: do not claim a certified result unless the
corresponding GitHub Actions run finishes successfully AND its printed axioms
are inspected.
-/

noncomputable section

namespace BorghettiRH

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_actual_h78 (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (β : ℝ)
    (hne : χ ≠ 1) (hβ : (7 / 8 : ℝ) < β) :
    DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  apply OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ
  · simpa using hβ
  · intro hpole
    exact hne hpole.1

theorem b2_actual_no_exception
    {M : ℕ} [NeZero M] (h8 : 8 ∣ M) :
    ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), ¬ IsExcPair χ β :=
  b2_no_exception_of_seven_eighths h8 (b2_actual_h78 M)

theorem b2_actual_PNT_no_exception :
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
  exact b2_pnt_relative_without_exception b2_actual_h78
    Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds

#print axioms BorghettiRH.b2_actual_h78
#print axioms BorghettiRH.b2_actual_no_exception
#print axioms BorghettiRH.b2_actual_PNT_no_exception

end BorghettiRH
