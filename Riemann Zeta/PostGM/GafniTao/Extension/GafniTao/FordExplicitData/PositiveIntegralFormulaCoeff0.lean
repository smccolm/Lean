import GafniTao.FordPositiveIntegralFormula
import GafniTao.FordExplicitData.PositivePower11Coefficients
import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_0 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 0 =
      fordPositiveAtThreeHalvesValueCoeff0 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_0 :
    fordPositiveAtThreeHalvesExplicit.coeff 0 =
      fordPositiveAtThreeHalvesValueCoeff0 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_1 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 1 =
      fordPositiveAtThreeHalvesValueCoeff1 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_1 :
    fordPositiveAtThreeHalvesExplicit.coeff 1 =
      fordPositiveAtThreeHalvesValueCoeff1 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_2 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 2 =
      fordPositiveAtThreeHalvesValueCoeff2 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_2 :
    fordPositiveAtThreeHalvesExplicit.coeff 2 =
      fordPositiveAtThreeHalvesValueCoeff2 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_3 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 3 =
      fordPositiveAtThreeHalvesValueCoeff3 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_3 :
    fordPositiveAtThreeHalvesExplicit.coeff 3 =
      fordPositiveAtThreeHalvesValueCoeff3 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_4 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 4 =
      fordPositiveAtThreeHalvesValueCoeff4 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_4 :
    fordPositiveAtThreeHalvesExplicit.coeff 4 =
      fordPositiveAtThreeHalvesValueCoeff4 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_5 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 5 =
      fordPositiveAtThreeHalvesValueCoeff5 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_5 :
    fordPositiveAtThreeHalvesExplicit.coeff 5 =
      fordPositiveAtThreeHalvesValueCoeff5 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_6 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 6 =
      fordPositiveAtThreeHalvesValueCoeff6 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_6 :
    fordPositiveAtThreeHalvesExplicit.coeff 6 =
      fordPositiveAtThreeHalvesValueCoeff6 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_7 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 7 =
      fordPositiveAtThreeHalvesValueCoeff7 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_7 :
    fordPositiveAtThreeHalvesExplicit.coeff 7 =
      fordPositiveAtThreeHalvesValueCoeff7 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_8 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 8 =
      fordPositiveAtThreeHalvesValueCoeff8 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_8 :
    fordPositiveAtThreeHalvesExplicit.coeff 8 =
      fordPositiveAtThreeHalvesValueCoeff8 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_9 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 9 =
      fordPositiveAtThreeHalvesValueCoeff9 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_9 :
    fordPositiveAtThreeHalvesExplicit.coeff 9 =
      fordPositiveAtThreeHalvesValueCoeff9 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_10 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 10 =
      fordPositiveAtThreeHalvesValueCoeff10 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_10 :
    fordPositiveAtThreeHalvesExplicit.coeff 10 =
      fordPositiveAtThreeHalvesValueCoeff10 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_11 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 11 =
      fordPositiveAtThreeHalvesValueCoeff11 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_11 :
    fordPositiveAtThreeHalvesExplicit.coeff 11 =
      fordPositiveAtThreeHalvesValueCoeff11 := by
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
