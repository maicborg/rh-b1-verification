import New.Endgame.PrimeError
import RFH123S.TentKernel
import Mathlib.NumberTheory.Chebyshev

/-! Exact positive-part formula and weight bounds adapted from
grh/src/New/Reduction/Zeros/PrimeError.lean at upstream pin 72fead102f663d5c7a407964a13dc0cf9d977207.
This module connects the actual compact primeError to the V28 tent. -/
noncomputable section
open ArithmeticFunction DirichletCharacter Complex Finset Filter MeasureTheory Nat Real vonMangoldt
namespace RFH123S
variable (d : ℕ) [Fact d.Prime] (q : ℕ) [NeZero q]

lemma one_sub_chiK_mem_Icc (n : ℕ) : 1 - (chiK d n : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
  obtain h_val | h_val | h_val :
      legendreSym d n = 0 ∨ legendreSym d n = 1 ∨ legendreSym d n = -1 :=
    quadraticChar_isQuadratic (ZMod d) ((n : ℤ) : ZMod d) <;>
    norm_num [chiK_eq_legendreSym, h_val]

lemma lambdaClass_nonneg (n : ℕ) : 0 ≤ lambdaClass d q n :=
  mul_nonneg (residueClass_nonneg 1 n) (one_sub_chiK_mem_Icc d n).1

variable {d q} in
/-- For a prime `d` and any `q : ℕ`, the weight `lambdaClass d q n`, which is
`Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q` and `0` otherwise, is at most `2 Λ(n)`, where
`Λ = vonMangoldt`. -/
lemma lambdaClass_le_two_mul_vonMangoldt (n : ℕ) :
    lambdaClass d q n ≤ 2 * vonMangoldt n := by
  obtain ⟨h_chi_nonneg, h_chi_le⟩ := one_sub_chiK_mem_Icc d n
  rw [lambdaClass, mul_comm 2]
  exact mul_le_mul (residueClass_le 1 n) h_chi_le h_chi_nonneg vonMangoldt_nonneg

lemma primeError_eq_sum_posPart_exact {A : ℕ} {z : ℝ} (hz_pos : 0 < z) (hz_le : ⌊z⌋₊ ≤ A) :
    primeError d q z = ∑ n ∈ Icc 1 A,
      lambdaClass d q n * (1 / n - 1 / z)⁺ - z.log / φ q -
      re (logDerivMean d q 1) := by
  simp only [primeError, lambdaSum, sum_div, ← sum_sub_distrib, sub_left_inj]
  -- The positive part of `1 / n - 1 / z` vanishes for `z < n` and is the number itself for `n ≤ z`.
  refine sum_subset_zero_on_sdiff (Icc_subset_Icc_right hz_le) (fun n hn ↦ ?_) fun n hn ↦ ?_
  · have hz_lt : z < n := Nat.lt_of_floor_lt (by grind)
    rw [posPart_of_nonpos (sub_nonpos.2 (by gcongr)), mul_zero]
  · have hn_le : (n : ℝ) ≤ z := (Nat.le_floor_iff hz_pos.le).1 (mem_Icc.1 hn).2
    have hn_pos : 0 < n := (mem_Icc.1 hn).1
    rw [posPart_of_nonneg (sub_nonneg.2 (by gcongr))]
    field



def tentMass (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊2*x⌋₊, lambdaClass d q n * tentWeight (1/(n:ℝ)) (1/x)

theorem tentMass_eq (x : ℝ) (hx : 0 < x) :
    tentMass d q x = primeError d q x - 3*primeError d q (3*x/2) +
      2*primeError d q (2*x) + log (32/27:ℝ)/q.totient := by
  have h1 : ⌊x⌋₊ ≤ ⌊2*x⌋₊ := Nat.floor_mono (by linarith)
  have h2 : ⌊3*x/2⌋₊ ≤ ⌊2*x⌋₊ := Nat.floor_mono (by linarith)
  rw [primeError_eq_sum_posPart_exact d q hx h1,
    primeError_eq_sum_posPart_exact d q (by linarith) h2,
    primeError_eq_sum_posPart_exact d q (by positivity) (le_refl ⌊2*x⌋₊)]
  have he2 : 1/(3*x/2) = 2*(1/x)/3 := by field_simp
  have he3 : 1/(2*x) = (1/x)/2 := by field_simp
  have hs : tentMass d q x =
      (∑ n ∈ Icc 1 ⌊2*x⌋₊, lambdaClass d q n * (1/(n:ℝ)-1/x)⁺) -
      3*(∑ n ∈ Icc 1 ⌊2*x⌋₊, lambdaClass d q n * (1/(n:ℝ)-1/(3*x/2))⁺) +
      2*(∑ n ∈ Icc 1 ⌊2*x⌋₊, lambdaClass d q n * (1/(n:ℝ)-1/(2*x))⁺) := by
    simp only [tentMass,tentWeight,posPart_def,he2,he3,mul_sub,mul_add,
      Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
    ring_nf
  rw [hs]
  have hm := congrArg (fun t : ℝ ↦ t / (q.totient:ℝ)) (tent_log_main x hx)
  simp only [sub_div,add_div,mul_div_assoc] at hm
  linarith

lemma lambdaClass_zero_of_not_modEq (n : ℕ) (h : ¬ n ≡ 1 [MOD q]) :
    lambdaClass d q n = 0 := by
  have hz : (n : ZMod q) ≠ 1 := by
    intro he
    exact h (by simpa using (ZMod.natCast_eq_natCast_iff n 1 q).mp (by simpa using he))
  simp [lambdaClass,residueClass,Set.indicator,hz]

/-- If no prime lies in the wanted open interval and class, all mass
is bounded by the prime-power error. -/
theorem tentMass_le_nonprime (x : ℝ) (hx : 0 < x)
    (hnop : ¬ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ x < (p:ℝ) ∧ (p:ℝ) < 2*x) :
    tentMass d q x ≤ (2/(3*x)) * (Chebyshev.psi (2*x) - Chebyshev.theta (2*x)) := by
  let S := Icc 1 ⌊2*x⌋₊
  let w (n : ℕ) := lambdaClass d q n * tentWeight (1/(n:ℝ)) (1/x)
  have hprime (n : ℕ) (hn : n ∈ S) (hp : n.Prime) : w n = 0 := by
    by_cases hm : n ≡ 1 [MOD q]
    · have hbad : (n:ℝ) ≤ x ∨ 2*x ≤ n := by
        by_contra! h
        exact hnop ⟨n,hp,hm,h.1,h.2⟩
      have hnp : (0:ℝ) < n := by exact_mod_cast hp.pos
      rcases hbad with h | h
      · unfold w
        rw [tent_weight_outside_right _ _ (by positivity) (by gcongr),mul_zero]
      · unfold w
        rw [tent_weight_outside_left _ _ (by positivity) (by
          rw [show (1/x:ℝ)/2 = 1/(2*x) by field_simp]
          gcongr),mul_zero]
    · simp [w,lambdaClass_zero_of_not_modEq d q n hm]
  have he : tentMass d q x = ∑ n ∈ S with ¬n.Prime, w n := by
    unfold tentMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [hp,hprime n hn hp,w]
    · simp [hp,w]
  rw [he,Chebyshev.psi_sub_theta_eq_sum_not_prime]
  have hS : S = Ioc 0 ⌊2*x⌋₊ := by ext n; simp [S]; omega
  rw [← hS,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hλ := lambdaClass_le_two_mul_vonMangoldt (d := d) (q := q) n
  have hw := tent_weight_bounds (1/(n:ℝ)) (1/x) (by positivity : 0 ≤ 1/x)
  calc
    w n ≤ (2*vonMangoldt n)*((1/x)/3) :=
      mul_le_mul hλ hw.2 hw.1 (by positivity)
    _ = _ := by ring

#print axioms lambdaClass_le_two_mul_vonMangoldt
#print axioms primeError_eq_sum_posPart_exact
#print axioms tentMass_eq
#print axioms tentMass_le_nonprime
end RFH123S
