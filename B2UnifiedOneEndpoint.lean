import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiRelativeActual
import Development.AutomorphicArithmetic.MeanSquareBounds.B2PrimeSetOneEndpoint
import Development.AutomorphicArithmetic.MeanSquareBounds.B2SingleEndpointRHS
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal

/-!
B2 unified single-endpoint certificate. The same ORIGINAL Alpoge prime set
and Jacobi observable are bounded from below/above in a single theorem.
The AP input comes from the REAL Alpoge PNTAPRelW proof.
The OpenAI 7/8 nonvanishing remains an EXPLICIT h78 argument.
The quantitative asymptotic thresholds are EXPLICIT conditions, not proved.
Director: Maicol Borghetti; formalization: GPT-6.
-/

open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_unified_one_endpoint_conditional
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    ∃ cJ AJ CJ cP AP CP : ℝ, 0 < cJ ∧ 0 < cP ∧
      ∀ (m s a : ℕ) (U η : ℝ),
        0 < m → 8 ∣ m → a.Coprime m →
        1 < s → Odd s → Squarefree s → s.Coprime m →
        2 ≤ U →
        CJ * Real.log (m * s) *
          Real.log (Real.log (m * s) + 2) ≤ Real.log U →
        CP * Real.log m * Real.log (Real.log m + 2) ≤ Real.log U →
        0 ≤ η →
        U ^ (1 / 2 : ℝ) ≤ η * (liX U / (m.totient : ℝ)) →
        |AP| * (Real.exp (-(cP * Real.log U / Real.log m)) +
          Real.exp (-Real.sqrt (cP * Real.log U))) + η ≤ 1 / 2 →
        (liX U / (m.totient : ℝ)) / 2 ≤
          ((PPset m a U).card : ℝ) ∧
        |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
          (2 * (|AJ| * (
            Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
            Real.exp (-Real.sqrt (cJ * Real.log U))) + η)) *
          ((PPset m a U).card : ℝ) := by
  obtain ⟨cJ, AJ, CJ, hcJ, hJall⟩ := b2_jacobi_relative_actual_pnt h78
  obtain ⟨cP, AP, CP, hcP, hPall⟩ :=
    b2_pnt_relative_without_exception h78
      Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds
  refine ⟨cJ, AJ, CJ, cP, AP, CP, hcJ, hcP, ?_⟩
  intro m s a U η hm h8 ha hs hodd hsq hcop hU hthJ hthP hη hR hbudget
  let T : ℝ := liX U / (m.totient : ℝ)
  let R : ℝ := U ^ (1 / 2 : ℝ)
  let DJ : ℝ :=
    Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
      Real.exp (-Real.sqrt (cJ * Real.log U))
  let DP : ℝ :=
    Real.exp (-(cP * Real.log U / Real.log m)) +
      Real.exp (-Real.sqrt (cP * Real.log U))
  let δJ : ℝ := |AJ| * DJ
  let δP : ℝ := |AP| * DP
  have hT : 0 ≤ T := by
    dsimp [T]
    apply div_nonneg (liX_nonneg hU)
    exact_mod_cast (Nat.totient_pos.mpr hm).le
  have hDP : 0 ≤ DP := by
    dsimp [DP]
    positivity
  have hδJ : 0 ≤ δJ := by
    dsimp [δJ]
    positivity
  have hpi0 := hPall m h8 U a hU hthP ha
  have hpi : |(piAP U m a : ℝ) - T| ≤ δP * T := by
    have he : |(piAP U m a : ℝ) - T| ≤ AP * DP * T := by
      simpa [T, DP] using hpi0
    have hh : AP * (DP * T) ≤ |AP| * (DP * T) :=
      mul_le_mul_of_nonneg_right (le_abs_self AP)
        (mul_nonneg hDP hT)
    dsimp [δP]
    nlinarith [he, hh]
  have hcount : (piAP U m a : ℝ) - R ≤
      ((PPset m a U).card : ℝ) := by
    simpa [R] using b2_ppset_lower_one_endpoint m a U hm (by linarith)
  have hJ0 := hJall m s a U hm h8 ha hs hodd hsq hcop hU hthJ
  have hJ :
      |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
        δJ * T + R := by
    simpa [δJ, DJ, T, R, mul_assoc] using hJ0
  have hn := BorghettiRH.b2_single_endpoint_normalization
      ((PPset m a U).card : ℝ) (piAP U m a : ℝ) T
      |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)|
      R δP δJ η hT hδJ hη
      (by simpa [δP, DP] using hbudget)
      hpi hcount (by simpa [T, R] using hR) hJ
  simpa [T, δJ, DJ] using hn

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_unified_one_endpoint_conditional

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
