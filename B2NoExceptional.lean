import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

/-!
B2: No exceptional real zero with modulus divisible by 8,
conditional on the published OpenAI 7/8 nonvanishing theorem.

Director: Maicol Borghetti. Lean engineering: GPT-6.
Source: IsExcPair in Alpoge MeanSquareHypWIff.lean at pinned SHA
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.

The h78 parameter is EXPLICIT here. This file does not yet import
OpenAI's theorem across distinct Lean toolchains.
-/
noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/-- For any modulus 8|M, the exceptional real zero region
    1-1/(8 log M)<beta<1 lies strictly inside Re(s)>7/8.
    So OpenAI's 7/8 theorem eliminates ALL IsExcPair. -/
theorem b2_no_exception_of_seven_eighths
    {M : ℕ} [NeZero M] (h8 : 8 ∣ M)
    (h78 : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), ¬ IsExcPair χ β := by
  intro χ β he
  rcases he with ⟨_, hne, hzero, hlo, _⟩
  have hM8n : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8 : (8 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM8n
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
    have h : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlog : (2 : ℝ) ≤ Real.log (M : ℝ) := by
    exact hlog8.trans (Real.log_le_log (by norm_num) hM8)
  have hden : (0 : ℝ) < 8 * Real.log (M : ℝ) := by positivity
  have hf : (1 : ℝ) / (8 * Real.log (M : ℝ)) ≤ 1 / 8 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hβ : (7 / 8 : ℝ) < β := by linarith
  exact (h78 χ β hne hβ) hzero

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_no_exception_of_seven_eighths

/-- Absence of an exceptional pair forces any PNTAPRelW witness
    to choose e=none, hence its published *relative* AP error is
    already centered at Li(x)/phi(M) with no Siegel-zero term.

    This is conditional ONLY on the zero-free theorem h78 and the
    already-proved original PNTAPRelW input hP.
-/
theorem b2_pnt_relative_without_exception
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0)
    (hP : PNTAPRelW) :
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
  obtain ⟨c₃, A₀, C₀, hc₃, hbound⟩ := hP
  refine ⟨c₃, A₀, C₀, hc₃, ?_⟩
  intro M _ h8 X b hX hthreshold hb
  obtain ⟨e, he, _, hAP⟩ := hbound M h8
  have hnone : e = none := by
    cases e with
    | none => rfl
    | some p =>
      have hex : IsExcPair p.1 p.2 := he p rfl
      exact False.elim ((b2_no_exception_of_seven_eighths h8
        (h78 M)) p.1 p.2 hex)
  have h := hAP X b hX hthreshold hb
  simpa [hnone, mainAP] using h

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_pnt_relative_without_exception

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
