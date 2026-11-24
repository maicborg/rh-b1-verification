import Development.AutomorphicArithmetic.MeanSquareBounds.B2TwistKAllOddV6
import Development.AutomorphicArithmetic.MeanSquareBounds.MeanSqAbs

/-!
B2.2 bridge, step 1: actual Jacobi pair correlations from the
OpenAI 7/8 theorem, using the already-checked squarefree-part
reciprocity lemma of the original Alpoge formalization.

No exceptional modulus is excluded. The argument applies to
arbitrary n,n' in an interval, provided their squarefree part is
nontrivial. This is the first non-tautological input to the
Rademacher-Menshov interval second moment.

Director: Maicol Borghetti. Formalization: GPT-6.
-/
open Finset
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
noncomputable section

namespace QH

set_option maxHeartbeats 2000000 in
theorem b2_jacobi_pair_average_of_twistK_v1 :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a N n n' : ℕ),
      admitted ε Y U m a →
      (∀ q ∈ PPset m a U, q.Prime ∧ q % m = a % m ∧ N ^ 2 < q) →
      1 ≤ n → n ≤ N → 1 ≤ n' → n' ≤ N →
      1 < soutPart m (n * n') →
      (soutPart m (n * n') : ℝ) ≤ Y ^ A →
      |∑ q ∈ PPset m a U,
          ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| ≤
          Y ^ (-B) * ((PPset m a U).card : ℝ) := by
  intro ε A B hε hA hB
  obtain ⟨Y₀, hY₀⟩ := b2_actual_twistK_all_odd ε A B hε hA hB
  refine ⟨Y₀, ?_⟩
  intro Y hY U m a N n n' hAd hq hn1 hnN hn1' hnN' hs1 hsBound
  have hpair :
      |∑ q ∈ PPset m a U,
          ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PPset m a U,
          (jacobiSym (q : ℤ) (soutPart m (n * n')) : ℝ)| := by
    apply abs_pair_sum_eq (PPset m a U) m a n n' hAd.eight hAd.coprime hn1 hn1'
    intro q hqP
    obtain ⟨hqPrime, hqMod, hqBig⟩ := hq q hqP
    have hmul : n * n' ≤ N ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hnN hnN'
    exact ⟨hqPrime, hqMod, lt_of_le_of_lt hmul hqBig⟩
  rw [hpair]
  exact hY₀ Y hY U m a hAd _ hs1
    (soutPart_odd m _ (dvd_trans (by norm_num) hAd.eight))
    (soutPart_squarefree m _)
    (soutPart_coprime m _) hsBound

#print axioms QH.b2_jacobi_pair_average_of_twistK_v1
end QH
