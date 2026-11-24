import Development.AutomorphicArithmetic.MeanSquareBounds.B2RealPNT
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount

/-!
Replaces the Siegel/ExcBound call in MSqCount.count_a with the actual
OpenAI 7/8 no-zero theorem, without importing/using ZeroFreeDirichlet.excBound.

This proof deliberately reuses Alpoge's quantitative count_pos lemma.
It does NOT claim the PNTAPRelW dependency is free of Siegel ingredients.
Director: Maicol Borghetti. Proof engineering: GPT-6.
-/

open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

set_option maxHeartbeats 2000000 in
theorem b2_count_a_no_exception_from_OAI
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
      x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
      (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X →
      x ^ (ε / 6) ≤ Real.log X →
      Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
      X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨c₃, A₀, C₀, hc₃, hAP⟩ :=
    BorghettiRH.b2_actual_PNT_no_exception
  refine ⟨Real.exp (320 + 4 * |C₀| * (5 + ε / 5) +
    |4 * Real.log (4 * (|A₀| + 1)) / c₃| +
    |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| +
    |Real.log (320 / (1 / 8 : ℝ))|), ?_⟩
  intro x X m₀ a₀ hx hm0 h8 hcop h1 h6 h3
  letI : NeZero m₀ := ⟨hm0.ne'⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx :
      320 + 4 * |C₀| * (5 + ε / 5) +
        |4 * Real.log (4 * (|A₀| + 1)) / c₃| +
        |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| +
        |Real.log (320 / (1 / 8 : ℝ))| ≤ Real.log x := by
    rw [← Real.exp_le_exp, Real.exp_log hxpos]
    exact hx
  have hC0 : 0 ≤ 4 * |C₀| * (5 + ε / 5) :=
    mul_nonneg (by positivity) (by linarith)
  have a1 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) / c₃)
  have a2 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)
  have a3 := abs_nonneg (Real.log (320 / (1 / 8 : ℝ)))
  have hl320 : 320 ≤ Real.log x := by linarith
  have hx1 : 1 ≤ x := by
    have h := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at h
    linarith
  have hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x := by linarith
  have hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) / c₃)]
  have hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)]
  have hlc : |Real.log (320 / (1 / 8 : ℝ))| ≤ Real.log x := by
    linarith
  have he1 : ∀ p : DirichletCharacter ℂ m₀ × ℝ,
      (none : Option (DirichletCharacter ℂ m₀ × ℝ)) = some p →
      IsExcPair p.1 p.2 := by
    intro p hp
    cases hp
  have he3 :
      ∀ (T : ℝ) (b : ℕ),
        2 ≤ T →
        C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log T →
        b.Coprime m₀ →
        |(piAP T m₀ b : ℝ) -
            mainAP (none : Option (DirichletCharacter ℂ m₀ × ℝ)) b T| ≤
          A₀ * (Real.exp (-(c₃ * Real.log T / Real.log m₀)) +
            Real.exp (-Real.sqrt (c₃ * Real.log T))) *
          mainAP (none : Option (DirichletCharacter ℂ m₀ × ℝ)) b T := by
    intro T b hT hth hb
    simpa [mainAP] using hAP m₀ h8 T b hT hth hb
  have hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ),
      χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      β ≤ 1 - (1 / 8 : ℝ) * (m₀ : ℝ) ^ (-1 : ℝ) := by
    intro χ β _ hne hz
    have hβ : β ≤ (7 / 8 : ℝ) :=
      le_of_not_gt (fun hh => (BorghettiRH.b2_actual_h78 m₀ χ β hne hh) hz)
    have hm8 : (8 : ℝ) ≤ (m₀ : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hm0 h8
    have hmpos : (0 : ℝ) < (m₀ : ℝ) := by linarith
    have hinv : (m₀ : ℝ) ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one, ← one_div]
      exact (div_le_iff₀ hmpos).2 (by linarith)
    nlinarith
  by_cases hpos : 0 < X
  · exact count_pos hc₃ (by norm_num : 0 < (1 / 8 : ℝ))
      (by norm_num : (1 / 8 : ℝ) ≤ 1) hε h8 a₀ hcop
      (none : Option (DirichletCharacter ℂ m₀ × ℝ))
      he1 he3 hcb x X hx1 hl320 hlC hlK1 hlK2 hlc h1 h3 hpos
  · have hXle : X ≤ 0 := not_lt.mp hpos
    rcases hXle.lt_or_eq with hneg | hzero
    · have hcard : (0 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) :=
        Nat.cast_nonneg _
      rw [Real.rpow_def_of_neg hneg]
      have hcos : Real.cos (9 / 10 * Real.pi) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      nlinarith [Real.exp_pos (Real.log X * (9 / 10))]
    · subst hzero
      rw [Real.zero_rpow (by norm_num)]
      exact Nat.cast_nonneg _

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_count_a_no_exception_from_OAI

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
