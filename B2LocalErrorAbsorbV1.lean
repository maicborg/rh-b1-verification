import Mathlib

/-!
B₂.2 -- quantitative absorption of the small off-diagonal term.

Suppose a finite-window second moment satisfies
  E ≤ (2 D + η M²) |P|,
with D ≤ C L² h, M ≤ L h and h ≤ N.
If η L² N ≤ 1 then
  E ≤ (2 C L² + 1) h |P|.

This is the local inequality needed as input to the finite
Rademacher--Menshov maximal lemma: it depends on the WINDOW LENGTH h,
not on the full truncation N. In the RH program the intended values
are h=card(I), L=log Z, N=floor Z and η=Y^(-(400K+2)).
The remaining task is to prove η L² N ≤ 1 with explicit Y₀.
This module does NOT assert that analytic input as an axiom.

Director: Maicol Borghetti. RH0 formalization, 2026-11-24.
-/

open Finset

noncomputable section

namespace BorghettiRH

/-- The error term of a quasi-orthogonal L² estimate is local when
the correlation strength times the total truncation is small. -/
theorem b2_absorb_local_quasiorthogonality
    (D M h N η L C : ℝ)
    (hh : 0 ≤ h)
    (hη : 0 ≤ η)
    (hM0 : 0 ≤ M)
    (hhN : h ≤ N)
    (hM : M ≤ L * h)
    (hD : D ≤ C * L ^ 2 * h)
    (hsmall : η * L ^ 2 * N ≤ 1) :
    2 * D + η * M ^ 2 ≤ (2 * C * L ^ 2 + 1) * h := by
  have hM2 : M ^ 2 ≤ (L * h) ^ 2 :=
    pow_le_pow_left₀ hM0 hM 2
  have hprod : h * h ≤ N * h :=
    mul_le_mul_of_nonneg_right hhN hh
  have hfac : 0 ≤ η * L ^ 2 :=
    mul_nonneg hη (sq_nonneg L)
  have ht1 : η * M ^ 2 ≤ η * (L * h) ^ 2 :=
    mul_le_mul_of_nonneg_left hM2 hη
  have ht2 : (η * L ^ 2) * (h * h) ≤
      (η * L ^ 2) * (N * h) :=
    mul_le_mul_of_nonneg_left hprod hfac
  have ht3 : ((η * L ^ 2) * N) * h ≤ h := by
    calc
      _ ≤ 1 * h := mul_le_mul_of_nonneg_right hsmall hh
      _ = h := one_mul h
  calc
    2 * D + η * M ^ 2 ≤
        2 * (C * L ^ 2 * h) + η * (L * h) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hD (by norm_num)) ht1
    _ = 2 * (C * L ^ 2 * h) + (η * L ^ 2) * (h * h) := by ring
    _ ≤ 2 * (C * L ^ 2 * h) + (η * L ^ 2) * (N * h) :=
      add_le_add (le_refl _) ht2
    _ = 2 * (C * L ^ 2 * h) + ((η * L ^ 2) * N) * h := by ring
    _ ≤ 2 * (C * L ^ 2 * h) + h := add_le_add (le_refl _) ht3
    _ = (2 * C * L ^ 2 + 1) * h := by ring

/-- Applies the quantitative error absorption to a finite family of
complex-valued character sums. No character-sum theorem is postulated:
the input `hSecond` is explicit. -/
theorem b2_local_L2_ready_for_maximal
    (P : Finset ℕ) (f : ℕ → ℂ)
    (D M h N η L C : ℝ)
    (hh : 0 ≤ h) (hη : 0 ≤ η)
    (hM0 : 0 ≤ M) (hhN : h ≤ N)
    (hM : M ≤ L * h)
    (hD : D ≤ C * L ^ 2 * h)
    (hsmall : η * L ^ 2 * N ≤ 1)
    (hSecond :
      (∑ q ∈ P, ‖f q‖ ^ 2) ≤
        (2 * D + η * M ^ 2) * (P.card : ℝ)) :
    (∑ q ∈ P, ‖f q‖ ^ 2) ≤
      ((2 * C * L ^ 2 + 1) * h) * (P.card : ℝ) := by
  exact hSecond.trans <|
    mul_le_mul_of_nonneg_right
      (b2_absorb_local_quasiorthogonality
        D M h N η L C hh hη hM0 hhN hM hD hsmall)
      (Nat.cast_nonneg _)

#print axioms BorghettiRH.b2_absorb_local_quasiorthogonality
#print axioms BorghettiRH.b2_local_L2_ready_for_maximal

end BorghettiRH
