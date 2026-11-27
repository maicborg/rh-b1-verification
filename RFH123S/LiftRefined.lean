import New.Rows.LiftVolumeHeight

/-! Proposed refinement of the final arithmetic step of the upstream proof.
Original source: New/Rows/LiftVolumeHeight.lean, blob 87938141d4103b485fd5a7125721798f65f973f1.
The comparison forms and Selmer inputs are unchanged. Needs an actual Lean build. -/
open Module ComplexConjugate Finset Function PolyRep IsAlgClosed LinearMap Matrix NumberField
  AuxPair Real Space LevelPlaces.LevelForm Data

namespace RFH123S

noncomputable def liftCost {P} (D : Data P) : ℝ :=
  (3 * (D.r : ℝ) + 6 * (D.k : ℝ)) * D.B₀ + 10 * D.m * D.x ^ 999 - D.k * D.dirCost

lemma heightLe_liftVolume_refined {P} {D : Data P} {θ} (O : D.IsFitFamily θ) (j : D.LiftIndex) :
  HeightLe (D.rowDim * liftCost D) fun ι ↦
    D.liftVolume 1 j / D.liftVolume (θ ι) j := (O.denominator_le j).elim fun β ⟨g, g'⟩ ↦ by
  rw [D.finrank_rows_eq_finrank_goodForms j, liftVolume, show TameChar.pow _ j =
    .one by rw [TameChar.pow]; congr <;> apply one_pow]
  obtain ⟨γ, A, gl, H, ad, sur, tst, int, S⟩ := exists_comparison_forms j
  have d ϑ := finrank_range_of_inj (f := D.goodLift ϑ j) (by simp [auxLift_injective])
  replace tst ϑ y :=
    (A.adjoint.map_smul ..).trans congr($(adjoint_comp_eq_conj_smul (ad ϑ)) y).symm ▸ tst ϑ _
  let u (ϑ : D.Twist) := (compressedGramOp (smallHookNumber j) (D.goodLift ϑ j).range (gl ϑ)).det
  have V ϑ : _ * u ϑ = _ := adjoint_comp_eq_conj_smul (ad ϑ) ▸ d ϑ ▸ det_compressedGramOp _
  have T ϑ := right_ne_zero_of_mul ((V ϑ).trans_ne (by simp [H,
    normDet_eq_zero_iff_ker_ne_bot, ← orthogonal_range, range_eq_top.2 sur]))
  have sep ϑ z (h : (gl ϑ).adjoint z.1 = 0) :=
    ker_eq_bot'.1 (equivOfDetNeZero _ (T ϑ)).ker z (by simp [compressedGramOp, h])
  refine O.heightLe_of_eq_zpow_mul (.mul (y := fun ι ↦ u ((θ ι).powTwist j) / u 1) ⟨_, _,
    (_ : ℕ) * (D.r * β), T 1, d _ ▸ norm_det_compressedGramOp_arch_le (sep 1)
    (fun | ⟨_, y, rfl⟩ => tst 1 y) rfl S, fun ι ↦ ?_, .of_forall
    fun _ ↦ by simp [← mul_sum]; grw [g]; simp⟩ ((heightLe_inv_heckeValueProd_div O j).pow _))
    (by
      rw [← mul_add, ← mul_add]
      gcongr
      simp only [liftCost, mul_sub, add_sub]
      ring_nf <;> exact le_rfl) fun ι
    n ↦ ⟨0, by
    have := div_ne_zero_iff.1 n; simp [← (H _).2, field, div_pow, V 1, *]
    erw [V ((θ ι).powTwist j)]; simp; ring⟩
  exact mul_div_cancel₀ _ (T 1) ▸ d _ ▸ norm_det_compressedGramOp_padic_le (sep _)
    (fun | ⟨_, y, rfl⟩ => tst _ y) ι (int _ · _ · (O.1 ι)) (g' ι).1

end RFH123S
