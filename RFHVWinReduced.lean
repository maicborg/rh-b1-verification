import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

namespace BorghettiRH
open Formalism.BasicNotions Formalism.MainNotions UpperTheory.Top
theorem producer_vwin : VWin := by
  exact UpperTheory.One.vwin_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter

theorem producer_vwin_zeta : VWinAt PChar.one 401 := by
  exact producer_vwin PChar.one

#print axioms BorghettiRH.producer_vwin
#print axioms BorghettiRH.producer_vwin_zeta
end BorghettiRH
