import Development.AutomorphicArithmetic.MeanSquareBounds.B2IntegratedBridge
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal

/-!
B2: one-endpoint Jacobi estimate with exact cancellation of the totient(s)
factor, using the ACTUAL proven Alpoge PNTAPRelW input.
The OpenAI 7/8 theorem remains an EXPLICIT h78 argument.
Director: Maicol Borghetti. Lean formalization: GPT-6.
No assumption of original QH.twistK or meanSqK.
-/

open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_jacobi_relative_actual_pnt
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧
      ∀ (m s a : ℕ) (U : ℝ),
        0 < m → 8 ∣ m → a.Coprime m →
        1 < s → Odd s → Squarefree s → s.Coprime m →
        2 ≤ U →
        C₀ * Real.log (m * s) *
          Real.log (Real.log (m * s) + 2) ≤ Real.log U →
        |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
          |A₀| *
          (Real.exp (-(c₃ * Real.log U / Real.log (m * s))) +
            Real.exp (-Real.sqrt (c₃ * Real.log U))) *
          (liX U / (m.totient : ℝ)) +
          U ^ (1 / 2 : ℝ) := by
  obtain ⟨c₃, A₀, C₀, hc₃, hJ⟩ :=
    b2_jacobi_bound_via_no_exception_pnt h78
      Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds
  refine ⟨c₃, A₀, C₀, hc₃, ?_⟩
  intro m s a U hm h8 ha hs hodd hsq hcop hU hthreshold
  have htot : (m * s).totient = m.totient * s.totient :=
    Nat.totient_mul hcop.symm
  have hmtot : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hm).ne'
  have hstot : (s.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < s)).ne'
  have hratio :
      (s.totient : ℝ) * (liX U / ((m * s).totient : ℝ)) =
        liX U / (m.totient : ℝ) := by
    rw [htot, Nat.cast_mul]
    field_simp
  have hb := hJ m s a U hm h8 ha hs hodd hsq hcop hU hthreshold
  calc
    |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (s.totient : ℝ) * |A₀| *
        (Real.exp (-(c₃ * Real.log U / Real.log (m * s))) +
          Real.exp (-Real.sqrt (c₃ * Real.log U))) *
        (liX U / ((m * s).totient : ℝ)) +
        U ^ (1 / 2 : ℝ) := hb
    _ = |A₀| *
      (Real.exp (-(c₃ * Real.log U / Real.log (m * s))) +
        Real.exp (-Real.sqrt (c₃ * Real.log U))) *
      (liX U / (m.totient : ℝ)) +
      U ^ (1 / 2 : ℝ) := by
        rw [← hratio]
        ring

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_jacobi_relative_actual_pnt
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
