import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC

/-!
B2: a uniform logarithmic modulus budget directly from the ORIGINAL
admitted structure, for all odd squarefree s<=Y^A (in fact all s>1).
Uses Alpoge's original kernel-proved eventually_log_cube.
Independent of QH.twistK and of zero-free assumptions.
Direction Maicol Borghetti. Proof adaptation GPT-6.
-/

noncomputable section
namespace BorghettiRH

theorem b2_admitted_log_modulus_budget_v2
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ Y₀ : ℝ, ∀ (Y U : ℝ) (m a s : ℕ),
      Y₀ ≤ Y → QH.admitted ε Y U m a →
      1 < s → (s : ℝ) ≤ Y ^ A →
      Real.log Y ^ 2 * Real.log (m * s) ≤ 8 * Real.log U := by
  obtain ⟨x₀, hx₀⟩ :=
    Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.eventually_log_cube
      (A / 4) (ε / 6) (by positivity) (by positivity)
  refine ⟨max x₀ 3, ?_⟩
  intro Y U m a s hY hAd hs hsBound
  have hX0le : x₀ ≤ Y := le_trans (le_max_left _ _) hY
  have hY3 : (3 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := by linarith
  have hL0 : 0 ≤ Real.log Y :=
    Real.log_nonneg (by linarith)
  have hms0 : 0 < m := hAd.pos
  have hs0 : 0 < s := by omega
  have hmspos : (0 : ℝ) < m := by exact_mod_cast hms0
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs0
  have hsl : Real.log (s : ℝ) ≤ A * Real.log Y := by
    calc
      Real.log (s : ℝ) ≤ Real.log (Y ^ A) :=
        Real.log_le_log hspos hsBound
      _ = A * Real.log Y := Real.log_rpow hYpos A
  have hml : Real.log ((m * s : ℕ) : ℝ) ≤ Real.log (m : ℝ) + A * Real.log Y := by
    rw [Nat.cast_mul, Real.log_mul hmspos.ne' hspos.ne']
    linarith
  have hh := mul_le_mul_of_nonneg_left hml (sq_nonneg (Real.log Y))
  have hlogm := hAd.log_m
  have hloghuge := (hx₀ Y hX0le).trans hAd.lo
  nlinarith [hh, hlogm, hloghuge]

#print axioms BorghettiRH.b2_admitted_log_modulus_budget_v2
end BorghettiRH
