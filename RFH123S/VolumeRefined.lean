import RFH123S.LiftRefined
import New.Endgame.LongForms

/-! Proposed refined lower-volume budget. Separate from the conservative final path. -/
open Module Finset Real LinearMap Submodule LevelPlaces.LevelForm Data
namespace RFH123S

noncomputable def volumeCost {P} (D : Data P) : ℝ :=
  (D.m : ℝ) * liftCost D + (D.m : ℝ)^2 * D.t * D.x^999

lemma heightLe_volume_ratio_refined {P} {D : Data P} {θ} (o : D.IsFitFamily θ) :
    HeightLe (2 * D.rowDim * volumeCost D) fun ι ↦
      D.𝔷 (1 : D.MFoldTwist)^2 / D.𝔷 (θ ι)^2 := by
  choose c const _ vol using D.volume_iota_eq_prod_liftVolume
  have lifts : HeightLe ((D.m : ℝ) * (D.rowDim * liftCost D))
      (∏ j ∈ Icc 1 D.m, fun ι ↦ D.liftVolume 1 j / D.liftVolume (θ ι) j) :=
    (HeightLe.prod fun j hj ↦ heightLe_liftVolume_refined o ⟨j, mem_Icc.1 hj⟩).mono
      (by simp [Nat.card_Icc]) fun _ ↦ le_rfl
  have consts : HeightLe ((D.m : ℝ)^2 * (2 * D.t * D.x^999)) fun ι ↦
      (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹ := by
    simpa [pow_two, Nat.cast_mul] using const θ o
  exact ((lifts.pow 2).mul (consts.pow D.rowDim)).mono
    (by unfold volumeCost; push_cast; ring_nf) fun ι ↦
    (congrArg (‖ι.2 ·‖) (by simp [vol, mul_pow, div_pow, ← pow_mul]; ring)).le

/-- The product formula cancels the leading volume exactly. -/
lemma volume_lower_refined {P} {D : Data P} {n} {y : Fin n → _} {δ V}
    (i : LinearIndependent ℂ y) (hn : (1 - 4 / D.b^2) * D.rowDim ≤ n)
    (I : D.IndexLe y δ) (hV : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ exp V) :
    -(D.rowDim : ℝ) * (volumeCost D + D.b) ≤ V + 2 * δ := by
  obtain ⟨⟨θ, o⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  have formula : 0 ≤ 2 * (V + 2 * δ + D.rowDim * D.b) + 2 * D.rowDim * volumeCost D :=
    ((((heightLe_volume_rows i hn I hV o).pow 2).mul
      (heightLe_volume_ratio_refined o)).mono le_rfl (by simp [field]; simp [(Z _).1])).nonneg
  linarith

end RFH123S
