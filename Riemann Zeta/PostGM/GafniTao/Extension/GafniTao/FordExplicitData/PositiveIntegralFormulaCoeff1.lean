import GafniTao.FordPositiveIntegralFormula
import GafniTao.FordExplicitData.PositivePower11Coefficients
import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_12 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 12 =
      fordPositiveAtThreeHalvesValueCoeff12 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_12 :
    fordPositiveAtThreeHalvesExplicit.coeff 12 =
      fordPositiveAtThreeHalvesValueCoeff12 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_13 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 13 =
      fordPositiveAtThreeHalvesValueCoeff13 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_13 :
    fordPositiveAtThreeHalvesExplicit.coeff 13 =
      fordPositiveAtThreeHalvesValueCoeff13 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_14 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 14 =
      fordPositiveAtThreeHalvesValueCoeff14 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_14 :
    fordPositiveAtThreeHalvesExplicit.coeff 14 =
      fordPositiveAtThreeHalvesValueCoeff14 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_15 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 15 =
      fordPositiveAtThreeHalvesValueCoeff15 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_15 :
    fordPositiveAtThreeHalvesExplicit.coeff 15 =
      fordPositiveAtThreeHalvesValueCoeff15 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_16 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 16 =
      fordPositiveAtThreeHalvesValueCoeff16 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_16 :
    fordPositiveAtThreeHalvesExplicit.coeff 16 =
      fordPositiveAtThreeHalvesValueCoeff16 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_17 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 17 =
      fordPositiveAtThreeHalvesValueCoeff17 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_17 :
    fordPositiveAtThreeHalvesExplicit.coeff 17 =
      fordPositiveAtThreeHalvesValueCoeff17 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_18 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 18 =
      fordPositiveAtThreeHalvesValueCoeff18 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_18 :
    fordPositiveAtThreeHalvesExplicit.coeff 18 =
      fordPositiveAtThreeHalvesValueCoeff18 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_19 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 19 =
      fordPositiveAtThreeHalvesValueCoeff19 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_19 :
    fordPositiveAtThreeHalvesExplicit.coeff 19 =
      fordPositiveAtThreeHalvesValueCoeff19 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_20 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 20 =
      fordPositiveAtThreeHalvesValueCoeff20 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_20 :
    fordPositiveAtThreeHalvesExplicit.coeff 20 =
      fordPositiveAtThreeHalvesValueCoeff20 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_21 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 21 =
      fordPositiveAtThreeHalvesValueCoeff21 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_21 :
    fordPositiveAtThreeHalvesExplicit.coeff 21 =
      fordPositiveAtThreeHalvesValueCoeff21 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_22 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 22 =
      fordPositiveAtThreeHalvesValueCoeff22 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_22 :
    fordPositiveAtThreeHalvesExplicit.coeff 22 =
      fordPositiveAtThreeHalvesValueCoeff22 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_23 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 23 =
      fordPositiveAtThreeHalvesValueCoeff23 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_23 :
    fordPositiveAtThreeHalvesExplicit.coeff 23 =
      fordPositiveAtThreeHalvesValueCoeff23 := by
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
