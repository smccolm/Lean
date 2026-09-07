import GafniTao.FordExplicitData.GapCoefficients

namespace GafniTao

noncomputable section

theorem fordNumericalGapExplicit_natDegree_le :
    fordNumericalGapExplicit.natDegree ≤ 88 := by
  unfold fordNumericalGapExplicit
  unfold fordNumericalGapValueBlock0 fordNumericalGapValueBlock1
    fordNumericalGapValueBlock2 fordNumericalGapValueBlock3
    fordNumericalGapValueBlock4 fordNumericalGapValueBlock5
    fordNumericalGapValueBlock6 fordNumericalGapValueBlock7
  compute_degree

end

end GafniTao
