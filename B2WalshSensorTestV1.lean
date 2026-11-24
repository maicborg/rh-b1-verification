import Mathlib

/-!
UNO-DUE-TRE -- an elementary exact caution about the "partial-sums sensor".

The four Walsh character rows of the 4x4 Hadamard matrix are pairwise
orthogonal across q, and the average second moment of row sums is
exactly 4, the square-root cancellation scale. However the untwisted
row has sum 4, and all three nonprincipal rows have sum 0.

Thus cancellation of a FAMILY OF TWISTS cannot, by itself, be used as a
bound for an arbitrary distinguished (untwisted) observation. An
additional coupling/amplification theorem is mathematically necessary
to turn B2.2 into a direct UNO-DUE-TRE contradiction for a hypothetical
off-line zeta zero. This is a finite model, NOT an assertion about the
real Jacobi characters or zeta.

Direction: Maicol Borghetti. Formalization GPT-6, RH0 2026-11-24.
-/

namespace BorghettiRH

def toyWalsh (q n : Fin 4) : ℤ :=
  if q.val = 0 then 1
  else if q.val = 1 then if n.val % 2 = 0 then 1 else -1
  else if q.val = 2 then if n.val < 2 then 1 else -1
  else if n.val = 0 ∨ n.val = 3 then 1 else -1

/-- Complete orthogonality of distinct COLUMN vectors. -/
theorem toyWalsh_columns_orthogonal :
    ∀ n m : Fin 4, n ≠ m →
      (∑ q : Fin 4, toyWalsh q n * toyWalsh q m) = 0 := by
  decide

/-- All nonprincipal rows have complete cancellation. -/
theorem toyWalsh_nonprincipal_cancel :
    ∀ q : Fin 4, q ≠ 0 →
      (∑ n : Fin 4, toyWalsh q n) = 0 := by
  decide

/-- The principal row grows linearly; the family-average grows only
at the square-root scale in second moment. -/
theorem toyWalsh_principal_vs_mean_square :
    (∑ n : Fin 4, (1 : ℤ)) = 4 ∧
    (∑ n : Fin 4, toyWalsh 0 n) = 4 ∧
    (∑ q : Fin 4, (∑ n : Fin 4, toyWalsh q n) ^ 2) = 16 := by
  decide

#print axioms BorghettiRH.toyWalsh_columns_orthogonal
#print axioms BorghettiRH.toyWalsh_nonprincipal_cancel
#print axioms BorghettiRH.toyWalsh_principal_vs_mean_square

end BorghettiRH
