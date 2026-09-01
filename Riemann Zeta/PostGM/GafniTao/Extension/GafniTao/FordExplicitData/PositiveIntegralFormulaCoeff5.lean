import GafniTao.FordPositiveIntegralFormula
import GafniTao.FordExplicitData.PositivePower11Coefficients
import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_60 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 60 =
      fordPositiveAtThreeHalvesValueCoeff60 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_60 :
    fordPositiveAtThreeHalvesExplicit.coeff 60 =
      fordPositiveAtThreeHalvesValueCoeff60 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_61 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 61 =
      fordPositiveAtThreeHalvesValueCoeff61 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_61 :
    fordPositiveAtThreeHalvesExplicit.coeff 61 =
      fordPositiveAtThreeHalvesValueCoeff61 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_62 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 62 =
      fordPositiveAtThreeHalvesValueCoeff62 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_62 :
    fordPositiveAtThreeHalvesExplicit.coeff 62 =
      fordPositiveAtThreeHalvesValueCoeff62 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_63 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 63 =
      fordPositiveAtThreeHalvesValueCoeff63 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_63 :
    fordPositiveAtThreeHalvesExplicit.coeff 63 =
      fordPositiveAtThreeHalvesValueCoeff63 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_64 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 64 =
      fordPositiveAtThreeHalvesValueCoeff64 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_64 :
    fordPositiveAtThreeHalvesExplicit.coeff 64 =
      fordPositiveAtThreeHalvesValueCoeff64 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_65 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 65 =
      fordPositiveAtThreeHalvesValueCoeff65 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_65 :
    fordPositiveAtThreeHalvesExplicit.coeff 65 =
      fordPositiveAtThreeHalvesValueCoeff65 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_66 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 66 =
      fordPositiveAtThreeHalvesValueCoeff66 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_66 :
    fordPositiveAtThreeHalvesExplicit.coeff 66 =
      fordPositiveAtThreeHalvesValueCoeff66 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

end

end GafniTao
