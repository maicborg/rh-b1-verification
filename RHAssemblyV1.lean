import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Formalism.GammaFactorNonvanishing.RhOfRight
import Development.AutomorphicArithmetic.MeanSquareBounds.B2JacobiPairCorrelationV1

/-!
Assembly V1 — direction Maicol Borghetti.
Base: fb67476a1a9317927a0b5481f88f8ee60d08d78f,
run 45395718013 (19 audited declarations).
Original Alpoge source pin 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
Unified Lean 4.34.1. See lab DOC-20261124-8c4f5c4d7b.
STATUS: SOURCE CANDIDATE, not kernel-checked yet.
Do not import Main, RH, or GRH as a proved conclusion.

The first integration target is the single-character version of
UpperTheory.Top.zeroFreeAll_of_topG.  This avoids supplying all
primitive Dirichlet characters at the final interface.
It does NOT prove FamilyClassConnected, replace its geometric
construction, or establish the B2.5 substitution.
The certified Jacobi module is imported for interface audit only:
the terminal conditional theorem does not yet depend on it.
-/
noncomputable section
namespace BorghettiRH

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX
open UpperTheory.Top

/-- Single-character terminal reduction, derived by restricting the
predicate of the existing window theorem to one primitive character. -/
theorem zero_free_single_of_connected
    (ψ : PChar) {la : ℝ} (hla : 1 < la)
    (h : FamilyClassConnected ((GChi ψ).cls la)) :
    ψ.ZeroFreeAbove (1 / 2) := by
  have key : ZeroFreeOn (fun ξ : PChar => ξ = ψ) :=
    zeroFreeOn_of_tiedWin_cyc
      (Fam := FamP) (core := fun Fm => Fm.toFamCore)
      (Tied := fun Fm => ChainTied Fm) hla
      (fun ξ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _)
      (fun ξ _ => UpperTheory.Comparison₂.formB _) fun ξ hξ => by
        subst ξ
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key ψ rfl

/-- Zeta-only assembly interface. The hypothesis is the remaining
geometric/window supply obligation, not an unconditional theorem. -/
theorem rh_of_zeta_connected
    (h : FamilyClassConnected ((GChi PChar.one).cls (3 / 2))) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  have hz := zero_free_single_of_connected PChar.one
    (la := (3 / 2 : ℝ)) (by norm_num) h s hs
  have he : DirichletCharacter.LFunction PChar.one.χ = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))
  rw [he] at hz
  exact hz

#check QH.b2_jacobi_pair_average_of_twistK_v1
#print axioms QH.b2_jacobi_pair_average_of_twistK_v1
#print axioms BorghettiRH.zero_free_single_of_connected
#print axioms BorghettiRH.rh_of_zeta_connected
end BorghettiRH
