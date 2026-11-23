import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistA

/-!
B2 prime-set cardinal lower bound from a SINGLE AP count at U.
No analytic PNT hypothesis is used: this is a finite combinatorial lemma.
The lower endpoint sqrt(U) is removed by an elementary cardinal bound.
Program director: Maicol Borghetti; Lean formalization: GPT-6.
-/
open Finset Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem b2_ppset_lower_one_endpoint
    (m a : ℕ) (U : ℝ) (hm : 0 < m) (hU : 0 ≤ U) :
    (piAP U m a : ℝ) - U ^ (1 / 2 : ℝ) ≤
       ((PPset m a U).card : ℝ) := by
  let b : ℕ := a % m
  have hb : b ∈ clsB m 1 a := by
    simp only [clsB, Finset.mem_filter, Finset.mem_range, Nat.mul_one]
    refine ⟨Nat.mod_lt _ hm, ?_, ?_⟩
    · simp [b, Nat.mod_mod]
    · simp
  have hcard :
      ((PPset m a U).filter (fun q => q % (m * 1) = b)).card =
      (PPset m a U).card := by
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, by
        have hmod := (Finset.mem_filter.mp h).2.2.1
        simpa [b] using hmod⟩
  have hpi : piAP U (m * 1) b = piAP U m a := by
    simp [piAP, b, Nat.mod_mod]
  have hsmall : (smallCnt U m b : ℝ) ≤ U ^ (1 / 2 : ℝ) := by
    have hterm : (smallCnt U (m * 1) b : ℝ) ≤
        ∑ z ∈ clsB m 1 a, (smallCnt U (m * 1) z : ℝ) := by
      exact Finset.single_le_sum
        (f := fun z : ℕ => (smallCnt U (m * 1) z : ℝ))
        (s := clsB m 1 a)
        (fun z hz => Nat.cast_nonneg _) hb
    have hsum := sum_small_le m 1 a U hU
    simpa only [Nat.mul_one] using hterm.trans hsum
  have hcnt : ((PPset m a U).card : ℝ) + (smallCnt U m b : ℝ) =
      (piAP U m a : ℝ) := by
    have h := cnt_add_small m 1 a U b hb
    rw [hcard, hpi, Nat.mul_one] at h
    exact_mod_cast h
  linarith

#print axioms Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.b2_ppset_lower_one_endpoint
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
