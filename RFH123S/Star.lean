import Statements
import New.Data.DataExist
import New.Endgame.LongForms

/-! The preterminal inequality, retaining the explicit error from Alpöge's New/Main.lean.
Source: lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207.
No import of New.Main, no terminal GRH theorem. -/
open DirichletCharacter Real Finset Filter Data Parameters ZMod Module

namespace RFH123S

lemma star_explicit {P} {D : Data P} : D.m * D.remainder ≤
    4 * (D.logB * D.budget) + 4 * D.x ^ 99 +
      10 * log (1 + D.b ^ 2) * D.budget :=
  D.exists_family_covolumeSq_le.elim fun n ⟨y, i, big, ⟨δ, index, I⟩, short⟩ ↦ by
  have d0 : (0 : ℝ) < D.rowDim := mod_cast D.finrank_rows_ne_zero.pos
  set d := (D.rowDim : ℝ)
  set L := D.logB * D.budget
  set h := D.mainHeight - D.m * D.remainder + L with def_h
  have crude : -h ≤ D.b ^ 2 * D.x ^ 99 := by
    grw [def_h, ← abs_mainHeight_add_remainder_le, ← neg_le_abs, ← le_abs_self,
      ← (HasLogBound.pos D : 0 < L)]
    simp
  have both : d * (D.mainHeight - 3 * L) ≤ d * (D.mainHeight - D.m * D.remainder + L + 4 *
    D.x ^ 99 + 10 * log (1 + D.b ^ 2) * D.budget) := calc
    _ ≤ d * h + (d - n) * -h + 2 * δ := (integral_forms_long i big I short).trans_eq (by ring)
    _ ≤ d * h + 4 / D.b ^ 2 * d * (D.b ^ 2 * D.x ^ 99) + 2 *
      (5 * d * log (1 + D.b ^ 2) * D.budget) := by
      grw [crude, index, show d - n ≤ 4 / D.b ^ 2 * d by linarith]
      exact sub_nonneg.2 (mod_cast Fintype.card_fin n ▸ i.fintype_card_le_finrank : (n : ℝ) ≤
        D.rowDim)
    _ = _ := by rw [def_h]; field [exp_ne_zero]
  linarith [le_of_mul_le_mul_left both d0]

lemma star_original {P} {D : Data P} : D.m * D.remainder ≤ D.logB ^ 2 * D.budget :=
  star_explicit.trans D.le_of_hasLogBound

/-- Interface for the original geometric height comparison, with no terminal RH input. -/
lemma geometric_height {P} (D : Data P) :
    D.heightPerRow ≤ D.mainHeight - D.m * D.remainder + D.budget :=
  D.heightPerRow_le

end RFH123S
