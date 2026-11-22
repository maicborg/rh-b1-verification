import Mathlib

/-!
# B2: exact finite second-moment Gram expansion (real coefficient channel)

Program direction: Maicol Borghetti, @maicborg.
Prepared with GPT-6, 22 November 2026.
No RH, OpenAI, or analytic inputs are assumed here. This is an
algebraic identity, intended as a certified building block for
the Dirichlet/Jacobi mean-square replacement.

For complex coefficients, apply this identity to the real and
imaginary parts separately and add.
-/

namespace BorghettiRH

theorem gram_real_expansion
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (P : Finset κ)
    (b : ι → ℝ) (sign : ι → κ → ℝ) :
    (∑ q ∈ P, (∑ i ∈ I, b i * sign i q) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I,
        b i * b j * (∑ q ∈ P, sign i q * sign j q) := by
  classical
  calc
    (∑ q ∈ P, (∑ i ∈ I, b i * sign i q) ^ 2) =
      ∑ q ∈ P, ∑ i ∈ I, ∑ j ∈ I,
        (b i * sign i q) * (b j * sign j q) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ q ∈ P,
      (b i * sign i q) * (b j * sign j q) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I,
      b i * b j * (∑ q ∈ P, sign i q * sign j q) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring

#print axioms BorghettiRH.gram_real_expansion

end BorghettiRH
