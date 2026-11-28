import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Lib.Analytic.Landau.PolarLandau
namespace RFH123S

/-- Same unconditional producer used by OpenAI's Nonvanishing.lean.
No Foundation umbrella or terminal RH/GRH is required by this wrapper.
Compilation on the target Mathlib pin is the compatibility test. -/
theorem entireL_ne_zero_qrh {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (7/8:ℝ) < s.re) : entireL χ s ≠ 0 := by
  by_cases hc : χ = 1
  · subst χ
    by_cases h1 : s = 1
    · subst s
      exact entireL_ne_zero 1 (by norm_num)
    · have h := OAI.SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
        q (NeZero.ne q) (1 : DirichletCharacter ℂ q) s hs (by simp [h1])
      rw [entireL]
      simpa [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1, h1] using
        mul_ne_zero (sub_ne_zero.mpr h1) h
  · have h := OAI.SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
      q (NeZero.ne q) χ s hs (by simp [hc])
    simpa [entireL, hc] using h

#print axioms entireL_ne_zero_qrh
end RFH123S
