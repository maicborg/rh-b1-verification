import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiPairCorrelationV1

/-!
High moments of prime twists: the checked pair lemma already handles
a whole product of primes by using n = ps.prod and n' = 1.
The squarefree odd part must be nontrivial. For a fixed moment 2k
the product bound N = floor(Z)^(2k) is polynomial in Y, and the
admitted large-modulus condition can accommodate q > N^2.

This is an arithmetic bridge for the high-moment alternative to
MeanSqK/BadShare. The moment expansion/pairing count is still separate.
-/
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

noncomputable section
namespace QH

theorem b2_jacobi_list_product (q : ℕ) (ps : List ℕ) :
    (ps.map (fun p => jacobiSym (p : ℤ) q)).prod =
      jacobiSym (ps.prod : ℤ) q := by
  induction ps with
  | nil => simp [jacobiSym.one_left]
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul,
      jacobiSym.mul_left, ih]

theorem b2_jacobi_product_average :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m a N : ℕ) (ps : List ℕ),
        admitted ε Y U m a →
        (∀ q ∈ PPset m a U, q.Prime ∧ q % m = a % m ∧ N ^ 2 < q) →
        1 ≤ ps.prod → ps.prod ≤ N →
        1 < soutPart m ps.prod →
        (soutPart m ps.prod : ℝ) ≤ Y ^ A →
        |∑ q ∈ PPset m a U,
          ((ps.map (fun p => jacobiSym (p : ℤ) q)).prod : ℝ)| ≤
          Y ^ (-B) * ((PPset m a U).card : ℝ) := by
  intro ε A B hε hA hB
  obtain ⟨Y₀, hY₀⟩ := b2_jacobi_pair_average_of_twistK_v1 ε A B hε hA hB
  refine ⟨Y₀, ?_⟩
  intro Y hY U m a N ps hAd hq hp hpN hs hsY
  have hn : 1 ≤ N := hp.trans hpN
  have h := hY₀ Y hY U m a N ps.prod 1 hAd hq hp hpN
    (by norm_num) hn (by simpa only [Nat.mul_one] using hs)
    (by simpa only [Nat.mul_one] using hsY)
  simp_rw [b2_jacobi_list_product]
  simpa only [Nat.cast_one, jacobiSym.one_left, mul_one] using h

#print axioms QH.b2_jacobi_list_product
#print axioms QH.b2_jacobi_product_average
end QH
