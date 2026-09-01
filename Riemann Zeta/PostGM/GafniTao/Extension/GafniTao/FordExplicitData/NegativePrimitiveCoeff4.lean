import GafniTao.FordNegativeIntegralFormula

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordNegativePrimitiveExplicit_coeff_49 :
    fordNegativePrimitiveExplicit.coeff 49 =
      Polynomial.C (1 / (49 : ℚ)) *
        fordNegativeUpperExplicit.coeff 48 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_50 :
    fordNegativePrimitiveExplicit.coeff 50 =
      Polynomial.C (1 / (50 : ℚ)) *
        fordNegativeUpperExplicit.coeff 49 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_51 :
    fordNegativePrimitiveExplicit.coeff 51 =
      Polynomial.C (1 / (51 : ℚ)) *
        fordNegativeUpperExplicit.coeff 50 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_52 :
    fordNegativePrimitiveExplicit.coeff 52 =
      Polynomial.C (1 / (52 : ℚ)) *
        fordNegativeUpperExplicit.coeff 51 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_53 :
    fordNegativePrimitiveExplicit.coeff 53 =
      Polynomial.C (1 / (53 : ℚ)) *
        fordNegativeUpperExplicit.coeff 52 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_54 :
    fordNegativePrimitiveExplicit.coeff 54 =
      Polynomial.C (1 / (54 : ℚ)) *
        fordNegativeUpperExplicit.coeff 53 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

@[simp] theorem fordNegativePrimitiveExplicit_coeff_55 :
    fordNegativePrimitiveExplicit.coeff 55 =
      Polynomial.C (1 / (55 : ℚ)) *
        fordNegativeUpperExplicit.coeff 54 := by
  simp only [fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0,
    fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2,
    fordNegativeUpperExplicit,
    fordNegativeUpperBlock0,
    fordNegativeUpperBlock1,
    fordNegativeUpperBlock2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

end

end GafniTao
