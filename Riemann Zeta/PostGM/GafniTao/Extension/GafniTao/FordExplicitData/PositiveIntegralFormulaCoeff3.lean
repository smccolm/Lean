import GafniTao.FordPositiveIntegralFormula
import GafniTao.FordExplicitData.PositivePower11Coefficients
import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_36 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 36 =
      fordPositiveAtThreeHalvesValueCoeff36 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_36 :
    fordPositiveAtThreeHalvesExplicit.coeff 36 =
      fordPositiveAtThreeHalvesValueCoeff36 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_37 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 37 =
      fordPositiveAtThreeHalvesValueCoeff37 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_37 :
    fordPositiveAtThreeHalvesExplicit.coeff 37 =
      fordPositiveAtThreeHalvesValueCoeff37 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_38 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 38 =
      fordPositiveAtThreeHalvesValueCoeff38 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_38 :
    fordPositiveAtThreeHalvesExplicit.coeff 38 =
      fordPositiveAtThreeHalvesValueCoeff38 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_39 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 39 =
      fordPositiveAtThreeHalvesValueCoeff39 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_39 :
    fordPositiveAtThreeHalvesExplicit.coeff 39 =
      fordPositiveAtThreeHalvesValueCoeff39 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_40 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 40 =
      fordPositiveAtThreeHalvesValueCoeff40 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_40 :
    fordPositiveAtThreeHalvesExplicit.coeff 40 =
      fordPositiveAtThreeHalvesValueCoeff40 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_41 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 41 =
      fordPositiveAtThreeHalvesValueCoeff41 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_41 :
    fordPositiveAtThreeHalvesExplicit.coeff 41 =
      fordPositiveAtThreeHalvesValueCoeff41 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_42 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 42 =
      fordPositiveAtThreeHalvesValueCoeff42 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_42 :
    fordPositiveAtThreeHalvesExplicit.coeff 42 =
      fordPositiveAtThreeHalvesValueCoeff42 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_43 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 43 =
      fordPositiveAtThreeHalvesValueCoeff43 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_43 :
    fordPositiveAtThreeHalvesExplicit.coeff 43 =
      fordPositiveAtThreeHalvesValueCoeff43 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_44 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 44 =
      fordPositiveAtThreeHalvesValueCoeff44 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_44 :
    fordPositiveAtThreeHalvesExplicit.coeff 44 =
      fordPositiveAtThreeHalvesValueCoeff44 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_45 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 45 =
      fordPositiveAtThreeHalvesValueCoeff45 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_45 :
    fordPositiveAtThreeHalvesExplicit.coeff 45 =
      fordPositiveAtThreeHalvesValueCoeff45 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_46 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 46 =
      fordPositiveAtThreeHalvesValueCoeff46 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_46 :
    fordPositiveAtThreeHalvesExplicit.coeff 46 =
      fordPositiveAtThreeHalvesValueCoeff46 := by
  norm_num [fordPositiveAtThreeHalvesExplicit,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5
  ]

@[simp] theorem fordPositiveIntegralPolynomialFormula_coeff_47 :
    (fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11).coeff 47 =
      fordPositiveAtThreeHalvesValueCoeff47 := by
  rw [fordPositiveIntegralPolynomialFormula_coeff]
  norm_num (config := { maxSteps := 10000000 })
    [Finset.sum_range_succ, Nat.choose]

@[simp] theorem fordPositiveAtThreeHalvesExplicit_coeff_47 :
    fordPositiveAtThreeHalvesExplicit.coeff 47 =
      fordPositiveAtThreeHalvesValueCoeff47 := by
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
