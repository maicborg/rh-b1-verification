import New.Data.DataExist

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- Uniform prime windows on the full range needed by the two prime uses.
The lower endpoint is 10 logB, not 100 logB. This is an OPEN analytic
input, not the weaker old Siegel-Walfisz lemma. -/
def WidePrimeWindows (P : Parameters) (s : ℕ) (L : ℝ) : Prop :=
  ∀ U ∈ Set.Icc (10 * L) (2 ^ s), ∃ p : ℕ,
    p.Prime ∧ p ≡ 1 [MOD P.Mω s ^ 2] ∧
    log p ∈ Set.Icc U (U + sqrt L)

/-- The class-group step needs only an injective family of split primes
in the desired congruence class. Extracted from exists_data. -/
lemma prime_pair_of_family (P : Parameters) (s : ℕ)
    (p : Fin (classNumber P.K + 1) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hm : ∀ i, p i ≡ 1 [MOD P.Mω s ^ 2])
    (hinj : Function.Injective p) :
    ∃ (g : Fin 2 → ℕ) (α : 𝓞 P.K),
      g.Injective ∧
      (∀ i, (g i).Prime ∧ g i ≡ 1 [MOD P.N₁ s * P.d] ∧
        P.Mω s ^ 2 ∣ g i - 1) ∧
      (∀ i, ∃ j, g i = p j) ∧ α * star α = g 0 * g 1 := by
  have hN i := (hm i).of_dvd (P.N₁_mul_d_dvd_M_omega.pow out)
  choose I J nI nJ eJ using fun i ↦ have := Fact.mk (hp i); (FinPlace.exists_natCast_mem P.K
      (p i)).imp fun w h ↦ (prime_inert_or_eq_mul w h).imp fun _ ↦
      (·.2.resolve_left (by simp [(q_eq_iff_legendreSym_ne_neg_one w h).2, sq,
      P.chiK_eq_one_of_modEq_one (hN i), (hp i).ne_one]))
  have ⟨i, j, ne, α, hα⟩ := exists_mul_principal (⟨_, eJ · |>.symm⟩)
  let g : Fin 2 → ℕ := p ∘ ![i, j]
  refine ⟨g, α, hinj.comp (by simpa), ?_, ?_, ?_⟩
  · intro l
    exact ⟨hp (![i,j] l), hN (![i,j] l), (hm (![i,j] l)).symm.dvd'⟩
  · intro l
    exact ⟨![i,j] l, rfl⟩
  · simp [g, ← absNorm_span_eq_mul_star, ← hα, nI, nJ]

end RFH123S
