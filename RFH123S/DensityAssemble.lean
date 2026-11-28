import RFH123S.DensityRank
import RFH123S.DensityDimension
import RFH123S.DensityCapacity
import RFH123S.DensityLogScales
import RFH123S.DensityBase
import RFH123S.DensityBudget
import RFH123S.DensityAlgebra

open Real Filter
namespace RFH123S

/-- Complete scalar producer at the actual tower rank. It selects the
integer dimension and base, proves capacity in natural numbers, and
proves the target density for any set with Behrend's cardinality bound.
Only the existence of that set is left to the geometric theorem. -/
theorem eventually_density_parameters (N : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∀ o : ℕ,
      (2 : ℝ)^(o+1) ∈ Set.Icc (exp (u/2)) (2*exp (u/2)) →
      ((o+1)*22 : ℝ) ≤ 32*u →
      let s := (o+1)*22
      let M := N*3^(Nat.log 3 s+5)
      ∃ q A : ℕ, 0 < q ∧ 0 < A ∧
        (324*s*A)^q*(M+2) ≤ 2^s ∧
        ∀ T : ℝ, (A : ℝ)^q / ((q : ℝ)*(A : ℝ)^2) ≤ T →
          0 < T ∧ ((3 : ℝ)^(Nat.log 3 s+5)*2^s)/T ≤
            exp (40*sqrt (u*log u)) := by
  let C : ℝ := 10^10*((N : ℝ)+1)
  have hC : 1 ≤ C := by
    have hN : 0 ≤ (N : ℝ) := by positivity
    dsimp [C]
    norm_num
    linarith
  filter_upwards [eventually_density_log_scales C hC,
    eventually_ge_atTop (max 4 (exp 1))] with u hu hU o hm hsu
  have hu4 : 4 ≤ u := (le_max_left _ _).trans hU
  have hup : 0 < u := by linarith
  have hv : 1 ≤ log u := (Real.le_log_iff_exp_le hup).2 ((le_max_right _ _).trans hU)
  have hvu : log u ≤ u := Real.log_le_self hup.le
  let s := (o+1)*22
  let K : ℝ := (3 : ℝ)^(Nat.log 3 s+5)
  let H : ℝ := K*2^s
  let W : ℝ := 2^s/((N : ℝ)*K+2)
  let L : ℝ := 324*s
  have hs : 0 < s := by dsimp [s]; positivity
  have hsu' : (s : ℝ) ≤ 32*u := by simpa [s] using hsu
  obtain ⟨hlo,hhi⟩ := rank_power_bounds u o hm
  obtain ⟨hH,hW,hL,hratio,hLup,hWlo,hWup⟩ :=
    density_rank_overhead N s u (by linarith) hs hsu' hlo hhi
  obtain ⟨hlogH,hlogL,hlogWlo,hlogWup⟩ :=
    hu H W L hH hW hL hratio hLup hWlo hWup
  obtain ⟨q,hq,hqlo,hqhi,hn⟩ := exists_density_dimension u (log u) hu4 hv hvu le_rfl
  have hcap := density_capacity u (log u) W L q hup (by linarith) hvu
    hW hL hq hqhi hlogL hlogWlo
  obtain ⟨A,hA,hfit,hround⟩ := exists_behrend_base W L q hq hL hcap
  have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hlogA := density_base_log u W L A q hW hL hAr hq hfit hlogWup
  have hbudget := density_budget u (log u) q H W A L hup (by linarith) hvu
    hqlo hqhi hlogA hlogL hlogH hn
  have hnat : (324*s*A)^q*(N*3^(Nat.log 3 s+5)+2) ≤ 2^s := by
    have hD : 0 < (N : ℝ)*K+2 := by positivity
    have hf := (le_div_iff₀ hD).mp (show (A : ℝ)^q*L^q ≤ (2 : ℝ)^s/((N : ℝ)*K+2) from hfit)
    have hreal : ((324 : ℝ)*s*A)^q*((N : ℝ)*K+2) ≤ (2 : ℝ)^s := by
      rw [mul_pow]
      simpa only [L, mul_comm, mul_left_comm, mul_assoc, mul_pow] using hf
    exact_mod_cast (show ((324 : ℝ)*s*A)^q*((N : ℝ)*(3 : ℝ)^(Nat.log 3 s+5)+2) ≤ (2 : ℝ)^s from hreal)
  refine ⟨q,A,hq,hA,hnat,?_⟩
  intro T hcard
  have hT : 0 < T := lt_of_lt_of_le (by positivity : 0 < (A : ℝ)^q / ((q : ℝ)*(A : ℝ)^2)) hcard
  exact ⟨hT,behrend_density_log H W A L q T (40*sqrt (u*log u)) q
    hH hW hAr (by linarith) hqr hT hcard hround hbudget⟩

#print axioms eventually_density_parameters
end RFH123S
