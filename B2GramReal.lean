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


/--
The complex mean square decomposes exactly into two real channels.
No estimates or number-theoretic assumptions are involved.
-/
theorem gram_complex_split
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (P : Finset κ)
    (b : ι → ℂ) (sign : ι → κ → ℝ) :
    (∑ q ∈ P, ‖∑ i ∈ I, b i * (sign i q : ℂ)‖ ^ 2) =
      (∑ q ∈ P, (∑ i ∈ I, (b i).re * sign i q) ^ 2) +
      (∑ q ∈ P, (∑ i ∈ I, (b i).im * sign i q) ^ 2) := by
  classical
  have hre : ∀ (J : Finset ι) (q : κ),
      (∑ i ∈ J, b i * (sign i q : ℂ)).re =
        ∑ i ∈ J, (b i).re * sign i q := by
    intro J q
    induction J using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
        simp only [Finset.sum_insert hi, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ih]
  have him : ∀ (J : Finset ι) (q : κ),
      (∑ i ∈ J, b i * (sign i q : ℂ)).im =
        ∑ i ∈ J, (b i).im * sign i q := by
    intro J q
    induction J using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
        simp only [Finset.sum_insert hi, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, ih]
  calc
    (∑ q ∈ P, ‖∑ i ∈ I, b i * (sign i q : ℂ)‖ ^ 2) =
      ∑ q ∈ P, ((∑ i ∈ I, b i * (sign i q : ℂ)).re ^ 2 +
        (∑ i ∈ I, b i * (sign i q : ℂ)).im ^ 2) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Complex.sq_norm, Complex.normSq_apply]
          ring
    _ = ∑ q ∈ P, ((∑ i ∈ I, (b i).re * sign i q) ^ 2 +
          (∑ i ∈ I, (b i).im * sign i q) ^ 2) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hre I q, him I q]
    _ = _ := Finset.sum_add_distrib

#print axioms BorghettiRH.gram_complex_split

/--
Full complex Gram identity with REAL quadratic signs. This is the exact
algebraic bridge needed before inserting nontrivial prime correlations.
-/
theorem gram_complex_expansion
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (P : Finset κ)
    (b : ι → ℂ) (sign : ι → κ → ℝ) :
    (∑ q ∈ P, ‖∑ i ∈ I, b i * (sign i q : ℂ)‖ ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I,
      ((b i).re * (b j).re + (b i).im * (b j).im) *
        (∑ q ∈ P, sign i q * sign j q) := by
  classical
  rw [gram_complex_split I P b sign,
    gram_real_expansion I P (fun i => (b i).re) sign,
    gram_real_expansion I P (fun i => (b i).im) sign,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms BorghettiRH.gram_complex_expansion

/--
Cauchy-Schwarz for the real Gram coefficient of two complex vectors,
using that this coefficient is the real part of z * conj w.
-/
theorem gram_bilinear_coefficient_le (z w : ℂ) :
    |z.re * w.re + z.im * w.im| ≤ ‖z‖ * ‖w‖ := by
  have hre : z.re * w.re + z.im * w.im =
      (z * Complex.conj w).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  calc
    |z.re * w.re + z.im * w.im| =
        |(z * Complex.conj w).re| := by rw [hre]
    _ ≤ ‖z * Complex.conj w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by simp [norm_mul]

#print axioms BorghettiRH.gram_bilinear_coefficient_le


end BorghettiRH
