import GafniTao.FordPositiveExplicitIdentity

open GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

example : fordNegativePrimitiveExplicit.coeff 1 =
    Polynomial.C (1 / (1 : ℚ)) * fordNegativeUpperExplicit.coeff 0 := by
  simp only [fordNegativePrimitiveExplicit, fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1, fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit, fordNegativeUpperBlock0,
    fordNegativeUpperBlock1, fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

example : fordNegativePrimitiveExplicit.coeff 55 =
    Polynomial.C (1 / (55 : ℚ)) * fordNegativeUpperExplicit.coeff 54 := by
  simp only [fordNegativePrimitiveExplicit, fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1, fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit, fordNegativeUpperBlock0,
    fordNegativeUpperBlock1, fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num
