import PrimeNumberTheoremAnd.PerronFormula

/-! Audit source theorem signatures and proof dependencies at the pinned
PNTAnd commit 127b50e33f6033e2147921167a117af96d9ba4ea.
No terminal RH theorem. This is not yet a bridge to RFH. -/
#check Perron.f
#check Perron.formulaLtOne
#check Perron.formulaGtOne
#check Perron.isIntegrable
#check verticalIntegral_eq_verticalIntegral
#check tendsto_truncated_vertical_shift_with_simple_pole
#print axioms Perron.formulaLtOne
#print axioms Perron.formulaGtOne
#print axioms Perron.isIntegrable
#print axioms verticalIntegral_eq_verticalIntegral
#print axioms tendsto_truncated_vertical_shift_with_simple_pole
