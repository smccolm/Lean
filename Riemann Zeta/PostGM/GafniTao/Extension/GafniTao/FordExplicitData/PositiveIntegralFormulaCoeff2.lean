import GafniTao.FordPositiveIntegralFormula
import GafniTao.FordExplicitData.PositivePower11Coefficients
import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_24 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 24 =
      fordPositiveAtThreeHalvesValueCoeff24 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_24 :
    fordPositiveAtThreeHalvesExplicit.coeff 24 =
      fordPositiveAtThreeHalvesValueCoeff24 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_25 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 25 =
      fordPositiveAtThreeHalvesValueCoeff25 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_25 :
    fordPositiveAtThreeHalvesExplicit.coeff 25 =
      fordPositiveAtThreeHalvesValueCoeff25 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_26 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 26 =
      fordPositiveAtThreeHalvesValueCoeff26 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_26 :
    fordPositiveAtThreeHalvesExplicit.coeff 26 =
      fordPositiveAtThreeHalvesValueCoeff26 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_27 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 27 =
      fordPositiveAtThreeHalvesValueCoeff27 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_27 :
    fordPositiveAtThreeHalvesExplicit.coeff 27 =
      fordPositiveAtThreeHalvesValueCoeff27 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_28 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 28 =
      fordPositiveAtThreeHalvesValueCoeff28 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_28 :
    fordPositiveAtThreeHalvesExplicit.coeff 28 =
      fordPositiveAtThreeHalvesValueCoeff28 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_29 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 29 =
      fordPositiveAtThreeHalvesValueCoeff29 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_29 :
    fordPositiveAtThreeHalvesExplicit.coeff 29 =
      fordPositiveAtThreeHalvesValueCoeff29 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_30 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 30 =
      fordPositiveAtThreeHalvesValueCoeff30 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_30 :
    fordPositiveAtThreeHalvesExplicit.coeff 30 =
      fordPositiveAtThreeHalvesValueCoeff30 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_31 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 31 =
      fordPositiveAtThreeHalvesValueCoeff31 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_31 :
    fordPositiveAtThreeHalvesExplicit.coeff 31 =
      fordPositiveAtThreeHalvesValueCoeff31 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_32 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 32 =
      fordPositiveAtThreeHalvesValueCoeff32 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_32 :
    fordPositiveAtThreeHalvesExplicit.coeff 32 =
      fordPositiveAtThreeHalvesValueCoeff32 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_33 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 33 =
      fordPositiveAtThreeHalvesValueCoeff33 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_33 :
    fordPositiveAtThreeHalvesExplicit.coeff 33 =
      fordPositiveAtThreeHalvesValueCoeff33 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_34 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 34 =
      fordPositiveAtThreeHalvesValueCoeff34 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_34 :
    fordPositiveAtThreeHalvesExplicit.coeff 34 =
      fordPositiveAtThreeHalvesValueCoeff34 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_35 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 35 =
      fordPositiveAtThreeHalvesValueCoeff35 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_35 :
    fordPositiveAtThreeHalvesExplicit.coeff 35 =
      fordPositiveAtThreeHalvesValueCoeff35 := by
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
