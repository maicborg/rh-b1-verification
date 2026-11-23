import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiRelativeActual
import Development.AutomorphicArithmetic.MeanSquareBounds.B2PrimeSetOneEndpoint
import Development.AutomorphicArithmetic.MeanSquareBounds.B2SmallErrorBudget
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

/-!
The original Alpoge theorem count_a supplies sqrt(U) <= d * |PPset|
with d=exp(-(2/5)*log U). Combine that ACTUAL theorem,
the ACTUAL PNTAPRelW, the Jacobi CRT bound and the elementary
relative budget on the SAME ORIGINAL Alpoge PPset and Jacobi sum.

Assumptions remain: OpenAI h78 and explicit PNT thresholds + tiny errors.
Crucially, we do NOT import QH.twistK or assume its conclusion.
Direction: Maicol Borghetti; Lean formalization: GPT-6.
-/

open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_actual_count_and_jacobi_small_error
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cJ AJ CJ cP AP CP Y₁ : ℝ,
      0 < cJ ∧ 0 < cP ∧
      ∀ (Y U B : ℝ) (m s a : ℕ),
        Y₁ ≤ Y →
        QH.admitted ε Y U m a →
        0 < B →
        1 < s → Odd s → Squarefree s → s.Coprime m →
        2 ≤ U →
        CJ * Real.log (m * s) *
          Real.log (Real.log (m * s) + 2) ≤ Real.log U →
        CP * Real.log m * Real.log (Real.log m + 2) ≤ Real.log U →
        |AP| * (Real.exp (-(cP * Real.log U / Real.log m)) +
          Real.exp (-Real.sqrt (cP * Real.log U))) ≤ 1 / 8 →
        2 * |AJ| * (Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
          Real.exp (-Real.sqrt (cJ * Real.log U))) ≤ Y ^ (-B) / 2 →
        Real.exp (-(2 / 5 * Real.log U)) ≤ Y ^ (-B) / 4 →
        Y ^ (-B) ≤ 1 →
        |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
          Y ^ (-B) * ((PPset m a U).card : ℝ) := by
  obtain ⟨cJ, AJ, CJ, hcJ, hJall⟩ := b2_jacobi_relative_actual_pnt h78
  obtain ⟨cP, AP, CP, hcP, hPall⟩ :=
    b2_pnt_relative_without_exception h78
      Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds
  obtain ⟨Y₁, hCount⟩ :=
    count_a Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds
      Formalism.ZeroFreeDirichlet.excBound ε hε
  refine ⟨cJ, AJ, CJ, cP, AP, CP, Y₁, hcJ, hcP, ?_⟩
  intro Y U B m s a hY hAd hB hs hodd hsq hcop hU hthJ hthP hEP hEJ hd hTau
  let T : ℝ := liX U / (m.totient : ℝ)
  let R : ℝ := U ^ (1 / 2 : ℝ)
  let d : ℝ := Real.exp (-(2 / 5 * Real.log U))
  let δJ : ℝ := |AJ| * (Real.exp (-(cJ * Real.log U / Real.log (m * s))) +
    Real.exp (-Real.sqrt (cJ * Real.log U)))
  let δP : ℝ := |AP| * (Real.exp (-(cP * Real.log U / Real.log m)) +
    Real.exp (-Real.sqrt (cP * Real.log U)))
  let τ : ℝ := Y ^ (-B)
  have hUpos : 0 < U := by linarith
  letI : NeZero m := ⟨hAd.pos.ne'⟩
  have hT : 0 ≤ T := by
    dsimp [T]
    apply div_nonneg (liX_nonneg hU)
    exact_mod_cast (Nat.totient_pos.mpr hAd.pos).le
  have hP : 0 ≤ (((PPset m a U).card : ℝ)) := Nat.cast_nonneg _
  have hδJ : 0 ≤ δJ := by dsimp [δJ]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hτ0 : 0 ≤ τ := by dsimp [τ]; positivity
  have hCard : U ^ (9 / 10 : ℝ) ≤ ((PPset m a U).card : ℝ) :=
    hCount Y U m a hY hAd.pos hAd.eight hAd.coprime
      hAd.log_m hAd.lo hAd.hi
  have hR : R ≤ d * ((PPset m a U).card : ℝ) := by
    have hfactor : U ^ (1 / 2 : ℝ) =
        U ^ (-(2 / 5) : ℝ) * U ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hUpos]
      norm_num
    have hddef : U ^ (-(2 / 5) : ℝ) = d := by
      rw [Real.rpow_def_of_pos hUpos]
      dsimp [d]
      congr 1
      ring
    rw [hfactor, hddef]
    exact mul_le_mul_of_nonneg_left hCard hd0
  have hPcount : (piAP U m a : ℝ) - R ≤ ((PPset m a U).card : ℝ) := by
    simpa [R] using b2_ppset_lower_one_endpoint m a U hAd.pos (by linarith)
  have hpi0 := hPall m hAd.eight U a hU hthP hAd.coprime
  have hpi : |(piAP U m a : ℝ) - T| ≤ δP * T := by
    let E : ℝ := Real.exp (-(cP * Real.log U / Real.log m)) +
      Real.exp (-Real.sqrt (cP * Real.log U))
    have hEn : 0 ≤ E := by dsimp [E]; positivity
    have he : |(piAP U m a : ℝ) - T| ≤ AP * E * T := by
      simpa [T, E] using hpi0
    have hh : AP * (E * T) ≤ |AP| * (E * T) :=
      mul_le_mul_of_nonneg_right (le_abs_self AP) (mul_nonneg hEn hT)
    dsimp [δP]
    nlinarith [he, hh]
  have hJ0 := hJall m s a U hAd.pos hAd.eight hAd.coprime
    hs hodd hsq hcop hU hthJ
  have hJ :
      |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤ δJ * T + R := by
    simpa [δJ, T, R, mul_assoc] using hJ0
  have hresult := BorghettiRH.b2_small_error_budget
    ((PPset m a U).card : ℝ) (piAP U m a : ℝ) T R
    |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)|
    d δP δJ τ hP hT hd0 hδJ hτ0
    (by simpa [d, τ] using hd) (by simpa [τ] using hTau)
    (by simpa [δP] using hEP) (by simpa [δJ, τ] using hEJ)
    hpi hPcount hR hJ
  exact hresult.2

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_actual_count_and_jacobi_small_error
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
