import RFH123S.PrimePair

open Finset Real Filter NumberField ClassGroup NeZero QuadField
namespace RFH123S

/-- Disjoint logarithmic windows give the h+1 distinct auxiliary primes
needed by the class-group pigeonhole. -/
lemma prime_family_from_windows (P : Parameters) (s : ℕ) (L : ℝ)
    (hL : 0 < L)
    (hroom : (2 * (classNumber P.K : ℝ) + 1) * sqrt L ≤ L)
    (hV : 11 * L ≤ (2 : ℝ)^s)
    (hw : WidePrimeWindows P s L) :
    ∃ p : Fin (classNumber P.K + 1) → ℕ, p.Injective ∧
      (∀ i, (p i).Prime ∧ p i ≡ 1 [MOD P.Mω s ^ 2] ∧
        log (p i) ∈ Set.Icc (10 * L) (11 * L)) := by
  let U (i : Fin (classNumber P.K + 1)) : ℝ := 10 * L + 2 * i.val * sqrt L
  have hU (i : Fin (classNumber P.K + 1)) :
      U i ∈ Set.Icc (10 * L) (2 ^ s) := by
    have hi : (i.val : ℝ) ≤ classNumber P.K := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have h := mul_le_mul_of_nonneg_right (show 2 * (i.val : ℝ) ≤
      2 * (classNumber P.K : ℝ) + 1 by linarith) (Real.sqrt_nonneg L)
    constructor
    · dsimp [U]; positivity
    · exact (show U i ≤ 11 * L by dsimp [U]; linarith).trans hV
  choose p hp hm hl using fun i => hw (U i) (hU i)
  have hmono : StrictMono p := by
    intro i j hij
    have hij' : (i.val : ℝ) + 1 ≤ j.val := by
      exact_mod_cast (show i.val + 1 ≤ j.val from hij)
    have hs : 0 < sqrt L := Real.sqrt_pos.2 hL
    have hsep : U i + sqrt L < U j := by
      dsimp [U]
      nlinarith [mul_le_mul_of_nonneg_right hij' hs.le]
    have hlt : log (p i : ℝ) < log (p j : ℝ) :=
      (hl i).2.trans_lt (hsep.trans_le (hl j).1)
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hp i).pos)
      (by exact_mod_cast (hp j).pos)).mp hlt
  refine ⟨p, hmono.injective, fun i => ⟨hp i, hm i, ?_⟩⟩
  have hi : (i.val : ℝ) ≤ classNumber P.K := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have h := mul_le_mul_of_nonneg_right (show 2 * (i.val : ℝ) + 1 ≤
    2 * (classNumber P.K : ℝ) + 1 by linarith) (Real.sqrt_nonneg L)
  exact ⟨(hU i).1.trans (hl i).1,
    (hl i).2.trans (by dsimp [U]; nlinarith)⟩

end RFH123S
