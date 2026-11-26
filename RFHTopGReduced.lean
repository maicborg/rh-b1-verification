import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RFHLiteraturePrelude

namespace BorghettiRH
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc
open UpperTheory.LiteratureTheorems

theorem topG_of_literature (O : OpenLiteratureStatements) : UpperTheory.Top.TopG := by
  let P := published_results_eigen O
  let F := published_results_first O
  have hAM := theta_integrals_agree_and_local_matching_of_literature O
  have hX := (_root_.SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt (_root_.UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O) (_root_.UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O) (_root_.UpperTheory.LiteratureTheorems.poincare_lelong_inv_of_literature O) PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright (_root_.UpperTheory.LiteratureTheorems.fargues_exact_of_literature O) (_root_.UpperTheory.LiteratureTheorems.zarhin_statement O) (_root_.UpperTheory.LiteratureTheorems.nef_rr_of_literature O) (_root_.UpperTheory.LiteratureTheorems.siegel_toroidal_integral_of_literature O) (_root_.UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O) (_root_.UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O) (_root_.UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O) (_root_.UpperTheory.LiteratureTheorems.ar_degree_of_literature O) (_root_.UpperTheory.LiteratureTheorems.published_results_arithmetic O) (_root_.UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O))
  have hL := local_langlands_gl_recT_exists_of_literature O
  have hHyps := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F hAM.1 hAM.2 hX hL
    (fun cDep => UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
      (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
  have hG := GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters
  exact hHyps.elim (fun h => GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
    (UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)

theorem producer_topG : UpperTheory.Top.TopG := by
  have h := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  exact topG_of_literature ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩

#print axioms BorghettiRH.topG_of_literature
#print axioms BorghettiRH.producer_topG
end BorghettiRH
