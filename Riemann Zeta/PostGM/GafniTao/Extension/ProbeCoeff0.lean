import GafniTao.FordPositiveIntegralFormula

open GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

example :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 0 =
      fordPositiveAtThreeHalvesValueCoeff0 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [fordPositiveTaylorPower11, Finset.sum_range_succ]

example : fordPositiveAtThreeHalvesExplicit.coeff 0 =
    fordPositiveAtThreeHalvesValueCoeff0 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5]
