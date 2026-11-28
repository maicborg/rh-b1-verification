import RFH123S.TentExact
import RFH123S.PrimeErrorTail
import RFH123S.PrimeErrorAux
import RFH123S.DataAssembly

open Real Filter Finset Nat
namespace RFH123S

/-- All analytic information needed to select one prime is the uniform
primeError bound. The prime-power term is the existing Chebyshev estimate. -/
theorem exists_prime_window_of_error
    (h : UniformPrimeError) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (d q : ℕ) [Fact d.Prime] [NeZero q],
      d % 8 = 7 → q.Coprime d → ∀ x : ℝ, 1 ≤ x →
      6*C*log (2*(q:ℝ)*(d:ℝ))*x^(-(1/16:ℝ)) +
        (2/(3*x))*K*sqrt (2*x) < log (32/27:ℝ)/q.totient →
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ x < (p:ℝ) ∧ (p:ℝ) < 2*x := by
  obtain ⟨C,hC,h⟩ := h
  obtain ⟨K,hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C,max K 0,hC,le_max_right _ _,?_⟩
  intro d q _ _ hd hcop x hx hsmall
  let E := C*log (2*(q:ℝ)*(d:ℝ))*x^(-(1/16:ℝ))
  have hE (z : ℝ) (hz : x ≤ z) : |primeError d q z| ≤ E := by
    have hn : 0 ≤ C*log (2*(q:ℝ)*(d:ℝ)) := by
      apply mul_nonneg hC
      apply Real.log_nonneg
      have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      have hd' : (1:ℝ) ≤ d := by exact_mod_cast (Fact.out : d.Prime).pos
      nlinarith
    exact (h d q hd hcop z (hx.trans hz)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hz (by norm_num)) hn)
  have hmass : log (32/27:ℝ)/q.totient - 6*E ≤ tentMass d q x := by
    rw [tentMass_eq d q x (by linarith)]
    linarith [(abs_le.mp (hE x le_rfl)).1,
      (abs_le.mp (hE (3*x/2) (by linarith))).2,
      (abs_le.mp (hE (2*x) (by linarith))).1]
  by_contra! hno
  have hu := tentMass_le_nonprime d q x (by linarith) (by
    rintro ⟨p,hp,hm,h1,h2⟩
    exact hno p hp hm h1 h2)
  have hk : Chebyshev.psi (2*x)-Chebyshev.theta (2*x) ≤ max K 0 * sqrt (2*x) :=
    (hK (2*x)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sqrt_nonneg _))
  have hb := hu.trans (mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2/(3*x)))
  dsimp [E] at hmass
  linarith

/-- Abstract absorption with polynomial-in-q losses and a square-root
prime-power term. The variable U can range above u² without upper restriction. -/
theorem window_scalar_absorption (C K B : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∀ᶠ u : ℝ in atTop, ∀ U q d : ℝ, u^2 ≤ U → 1 ≤ q → q ≤ exp (B*u) →
    1 ≤ d → d ≤ 31 → ∀ phi : ℝ, 0 < phi → phi ≤ q →
      6*C*log (2*q*d)*(exp U)^(-(1/16:ℝ)) +
        (2/(3*exp U))*K*sqrt (2*exp U) < log (32/27:ℝ)/phi := by
  let k := log (32/27:ℝ)
  let A := 372*C+2*K
  have hk : 0 < k := tent_log_positive
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (64*B),
    eventually_ge_atTop (32*(A/k+1))] with u hu huB huA
  intro U q d hU hq hqexp hd hd31 phi hphi hpq
  have hgap : 2*B*u ≤ U/32 := by nlinarith [mul_le_mul_of_nonneg_right huB (by linarith : 0 ≤ u)]
  have hlog : log (2*q*d) ≤ 62*q := by
    exact (Real.log_le_self (by positivity)).trans (by nlinarith)
  have hlog0 : 0 ≤ log (2*q*d) := by apply Real.log_nonneg; nlinarith
  have he1 : phi*(6*C*log (2*q*d)*(exp U)^(-(1/16:ℝ))) ≤ 372*C*exp (-U/32) := by
    rw [← Real.exp_mul]
    calc
      _ ≤ 372*C*q^2*exp (-U/16) := by
        have h1 := mul_le_mul hpq hlog hlog0 (by linarith : 0 ≤ q)
        nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ 6*C*exp (-U/16) by positivity)]
      _ ≤ 372*C*(exp (B*u))^2*exp (-U/16) := by gcongr
      _ = 372*C*exp (2*B*u-U/16) := by rw [← Real.exp_nat_mul, ← mul_assoc, mul_assoc (372*C), ← Real.exp_add]; ring
      _ ≤ _ := by gcongr; linarith
  have hs : sqrt (2*exp U) ≤ 2*exp (U/2) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [mul_pow,← Real.exp_nat_mul]
      simp only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(U/2) = U by ring]
      nlinarith [Real.exp_pos U]
  have he2 : phi*((2/(3*exp U))*K*sqrt (2*exp U)) ≤ 2*K*exp (-U/32) := by
    calc
      _ ≤ exp (B*u)*((2/(3*exp U))*K*(2*exp (U/2))) := by gcongr; exact hpq.trans hqexp
      _ = (4/3)*K*exp (B*u-U/2) := by
        rw [Real.exp_sub,Real.exp_sub]
        field_simp [Real.exp_ne_zero]
        rw [← Real.exp_nat_mul]
        ring_nf
      _ ≤ 2*K*exp (-U/32) := by
        gcongr <;> linarith
  have hdec : A*exp (-U/32) < k := by
    have hU32 : A/k+1 ≤ U/32 := by nlinarith
    have hex : A/k < exp (U/32) := by linarith [Real.add_one_le_exp (U/32)]
    rw [show -U/32 = -(U/32) by ring,Real.exp_neg]
    apply (mul_inv_lt_iff₀ (Real.exp_pos _)).2
    exact (div_lt_iff₀ hk).1 hex
  apply (lt_div_iff₀ hphi).2
  dsimp [A,k] at hdec
  nlinarith

/-- Candidate actual window producer, retaining every original quantifier. -/
theorem polylogPrimeWindows_of_uniformPrimeError (h : UniformPrimeError)
    (P : Parameters) (hP : P.N₀ = 18480) : PolylogPrimeWindows P := by
  obtain ⟨C,K,hC,hK,hselect⟩ := exists_prime_window_of_error h
  let B : ℝ := 76*log (18480*(P.d:ℝ))
  have hB : 0 ≤ B := by
    unfold B
    have hd : (1:ℝ) ≤ P.d := by exact_mod_cast P.d_prime.pos
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  unfold PolylogPrimeWindows
  filter_upwards [window_scalar_absorption C K B hC hK hB, eventually_ge_atTop (2:ℝ)] with u hsmall hu o hm hs
  let s := (o+1)*22
  let L : ℝ := (10^6*u)^6
  let q := P.Mω s ^ 2
  let d := auxDiscriminant P.d
  letI : Fact d.Prime := ⟨auxDiscriminant_prime P.d⟩
  have hq : q = (18480*P.d)^(2*(s+6)) := by
    simp [q,Parameters.Mω,hP,pow_mul,Nat.mul_comm]
  have hcop : q.Coprime d := by rw [hq]; exact auxDiscriminant_coprime P.d s P.d_prime
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqB : (q:ℝ) ≤ exp (B*u) := by
    apply (Real.log_le_iff_le_exp (by positivity)).1
    rw [hq]
    exact modulus_log_bound P.d s u P.d_prime.pos (by linarith) (by simpa [s] using hs)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (auxDiscriminant_prime P.d).pos
  have hd31 : (d:ℝ) ≤ 31 := by exact_mod_cast auxDiscriminant_le P.d
  change WidePrimeWindows P s L
  intro U hU
  have hLu : u^2 ≤ L := by
    have hu1 : 1 ≤ 10^6*u := by linarith
    unfold L
    calc
      u^2 ≤ (10^6*u)^2 := by gcongr <;> linarith
      _ ≤ (10^6*u)^6 := by exact pow_le_pow_right₀ hu1 (by norm_num)
  have hU2 : u^2 ≤ U := by nlinarith [hU.1]
  have hx : 1 ≤ exp U := Real.one_le_exp (by nlinarith)
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hpq : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  obtain ⟨p,hp,hmod,hlo,hhi⟩ := hselect d q (auxDiscriminant_mod P.d) hcop (exp U) hx
    (hsmall U q d hU2 hq1 hqB hd1 hd31 q.totient hphi hpq)
  have hpp : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlo' := Real.log_lt_log (Real.exp_pos U) hlo
  have hhi' := Real.log_lt_log hpp hhi
  rw [Real.log_exp] at hlo'
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _),Real.log_exp] at hhi'
  have hL4 : 4 ≤ L := by nlinarith
  have hsqrt : 2 ≤ sqrt L := by
    rw [← Real.sqrt_sq_eq_abs (2:ℝ)]
    simpa using Real.sqrt_le_sqrt hL4
  refine ⟨p,hp,hmod, hlo'.le, ?_⟩
  linarith [Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)]

#print axioms exists_prime_window_of_error
#print axioms window_scalar_absorption
#print axioms polylogPrimeWindows_of_uniformPrimeError
end RFH123S
