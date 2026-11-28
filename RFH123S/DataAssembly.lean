import RFH123S.ThickDensity
import RFH123S.PrimeWindows
import RFH123S.PrimeRoom
import RFH123S.ScaleEventually
import RFH123S.RankScale
import RFH123S.Producers

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- The outstanding uniform prime-window input, with all quantifiers
explicit. This proposition is not asserted as proved. -/
def PolylogPrimeWindows (P : Parameters) : Prop :=
  ∀ᶠ u : ℝ in atTop, ∀ o : ℕ,
    (2 : ℝ)^(o+1) ∈ Set.Icc (exp (u/2)) (2*exp (u/2)) →
    ((o+1)*22 : ℝ) ≤ 32*u →
    WidePrimeWindows P ((o+1)*22) ((10^6*u)^6)

/-- Produce actual admissible Data, with the new scales and density,
from the sole remaining prime-window input. -/
theorem polylogDataExists_of_primeWindows (P : Parameters)
    (hprime : PolylogPrimeWindows P) : PolylogDataExists P := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  unfold PolylogDataExists
  filter_upwards [hlog.eventually (eventually_polylog_scale P.c),
    hlog.eventually (eventually_thick_density P),
    hlog.eventually (eventually_prime_room (classNumber P.K)),
    hlog.eventually hprime,
    hlog.eventually (eventually_ge_atTop (10000 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with x hscale hthick hroom hwin hu hx
  let u := log x
  let L : ℝ := (10^6*u)^6
  obtain ⟨o,e,hm,hr,hsu⟩ := rank_scale u hu
  let s := (o+1)*22
  have hsr : (s : ℝ) ≤ 32*u := by simpa [s] using hsu
  obtain ⟨T,hT,hden,hcong,hthree⟩ := hthick o hm hsu
  have hw : WidePrimeWindows P s L := hwin o hm hsu
  obtain ⟨hL,hroom',hLexp⟩ := hroom
  have hV : 11*L ≤ (2 : ℝ)^s := hLexp.trans (rank_power_bounds u o hm).1
  obtain ⟨p,hpinj,hp⟩ := prime_family_from_windows P s L hL hroom' hV hw
  obtain ⟨g,α,hginj,hg,hgsource,hnorm⟩ := prime_pair_of_family P s p
    (fun i => (hp i).1) (fun i => (hp i).2.1) hpinj
  have hgmem (i : Fin 2) : (g i : ℝ) ∈ Set.Icc (exp L ^ 10) (exp L ^ 11) := by
    obtain ⟨j,hj⟩ := hgsource i
    have hmem : log (g i : ℝ) ∈ Set.Icc (10*L) (11*L) := by rw [hj]; exact (hp j).2.2
    have hpos : 0 < (g i : ℝ) := by exact_mod_cast (hg i).1.pos
    constructor
    · calc
        exp L ^ 10 = exp (10*L) := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ exp (log (g i : ℝ)) := Real.exp_le_exp.mpr hmem.1
        _ = _ := Real.exp_log hpos
    · calc
        (g i : ℝ) = exp (log (g i : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ exp (11*L) := Real.exp_le_exp.mpr hmem.2
        _ = exp L ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  let D : Data P :=
    { logX := u
      logB := L
      logX₁ := 10^6*u
      s := s
      m := 2^(o+1)
      r := 3^(e+1)
      s_le := hsr
      thick := T
      g := g
      piG := α
      scale := by simpa [u,L] using hscale
      m_mem := by exact_mod_cast hm
      r_mem := by exact_mod_cast hr
      m_pow := ⟨o,rfl,rfl⟩
      r_pow := ⟨e,rfl⟩
      thick_eq_neg_one_mod := fun d h => hcong d h
      three_term := hthree
      g_prime := fun i => (hg i).1
      g_modEq_one := fun i => (hg i).2.1
      dvd_g_sub_one := fun i => (hg i).2.2
      g_injective := hginj
      g_mem := hgmem
      norm_piG := hnorm
      exists_prime_window := fun U hU => hw U
        ⟨(show 10*L ≤ 100*L by linarith).trans hU.1,hU.2⟩ }
  have hcard : #D.tops = towerDeg s := by
    simp [Data.tops, D, P.card_placeClass_eq]
  refine ⟨D,?_,rfl,rfl,hT,?_⟩
  · exact Real.exp_log (by linarith : 0 < x)
  · rw [hcard]
    exact hden

#print axioms polylogDataExists_of_primeWindows
end RFH123S
