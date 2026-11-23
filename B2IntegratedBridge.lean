import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiClassZero
import Development.AutomorphicArithmetic.MeanSquareBounds.B2NoExceptional

/-!
B2 integrated bridge: OpenAI QRH7/8 (explicit h78)
 + Alpoge unconditional PNTAPRelW (hP)
 => fully unexceptional Jacobi prime sum bound.

Program director: Maicol Borghetti.
Formal proof engineering: GPT-6.
NO sorry and NO use of Alpoge's original twistK theorem.
The theorem is conditional on h78 and hP as clearly shown.
-/
open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_jacobi_bound_via_no_exception_pnt
    (h78 : ∀ (M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ ≠ 1 → (7 / 8 : ℝ) < β →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0)
    (hP : PNTAPRelW) :
    ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧
      ∀ (m s a : ℕ) (U : ℝ),
        0 < m → 8 ∣ m → a.Coprime m →
        1 < s → Odd s → Squarefree s → s.Coprime m →
        2 ≤ U →
        C₀ * Real.log (m * s) *
          Real.log (Real.log (m * s) + 2) ≤ Real.log U →
        |∑ q ∈ PPset m a U, (jacobiSym (q : ℤ) s : ℝ)| ≤
          (s.totient : ℝ) * |A₀| *
            (Real.exp (-(c₃ * Real.log U / Real.log (m * s))) +
              Real.exp (-Real.sqrt (c₃ * Real.log U))) *
            (liX U / ((m * s).totient : ℝ)) +
          U ^ (1 / 2 : ℝ) := by
  obtain ⟨c₃, A₀, C₀, hc₃, hAP⟩ :=
    b2_pnt_relative_without_exception h78 hP
  refine ⟨c₃, A₀, C₀, hc₃, ?_⟩
  intro m s a U hm h8 ha hs hodd hsquare hcop hU hlog
  haveI : NeZero (m * s) := ⟨(Nat.mul_pos hm (by omega)).ne'⟩
  have h8ms : 8 ∣ m * s := dvd_mul_of_dvd_left h8 _
  have hLi : 0 ≤ liX U := liX_nonneg hU
  have htot : 0 < ((m * s).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hm (by omega))
  let main : ℝ := liX U / ((m * s).totient : ℝ)
  let D : ℝ :=
    Real.exp (-(c₃ * Real.log U / Real.log (m * s))) +
    Real.exp (-Real.sqrt (c₃ * Real.log U))
  let E : ℝ := |A₀| * D * main
  have hmain : 0 ≤ main := by
    dsimp [main]
    exact div_nonneg hLi htot.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hError : ∀ b ∈ clsB m s a,
      |(piAP U (m * s) b : ℝ) - main| ≤ E := by
    intro b hb
    have hm0 : b % m = a % m := (Finset.mem_filter.mp hb).2.1
    have hbs : b.Coprime s := (Finset.mem_filter.mp hb).2.2
    have hbm : b.Coprime m := by
      unfold Nat.Coprime
      rw [Nat.ModEq.gcd_eq (show b ≡ a [MOD m] from hm0)]
      exact ha
    have hbM : b.Coprime (m * s) := Nat.Coprime.mul_right hbm hbs
    have hlog' : C₀ * Real.log ((m * s : ℕ) : ℝ) *
        Real.log (Real.log ((m * s : ℕ) : ℝ) + 2) ≤ Real.log U := by
      simpa only [Nat.cast_mul] using hlog
    have h := hAP (m * s) h8ms U b hU hlog' hbM
    calc
      |(piAP U (m * s) b : ℝ) - main| ≤
        A₀ * D * main := by simpa [main, D] using h
      _ ≤ E := by
        dsimp [E]
        have hA : A₀ ≤ |A₀| := le_abs_self A₀
        nlinarith [mul_nonneg hD hmain]
  have hbound := b2_jacobi_bound_of_uniform_AP m s a hm hs hodd
    hsquare hcop U main E (by linarith) hE hError
  simpa [E, D, main, mul_assoc] using hbound

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_jacobi_bound_via_no_exception_pnt

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
