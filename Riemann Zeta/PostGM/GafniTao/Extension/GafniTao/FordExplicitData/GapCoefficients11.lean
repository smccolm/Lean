import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

@[simp] theorem fordNumericalGapExplicit_coeff_88 :
    fordNumericalGapExplicit.coeff 88 = (-912034456046446591670769941126967809732389880154759674362919253085466672523897586208912607420113148072606337611541329196453281 / 527088500946928337841013196353524312384965622132848336124081630805348545809541835373105150577524929811196880511473409776177471090101751543542668573766677653360632375701736913113605734400000000000 : ℚ) := by
  simp [fordNumericalGapExplicit,
    fordNumericalGapValueBlock0,
    fordNumericalGapValueBlock1,
    fordNumericalGapValueBlock2,
    fordNumericalGapValueBlock3,
    fordNumericalGapValueBlock4,
    fordNumericalGapValueBlock5,
    fordNumericalGapValueBlock6,
    fordNumericalGapValueBlock7
  ]

end

end GafniTao
