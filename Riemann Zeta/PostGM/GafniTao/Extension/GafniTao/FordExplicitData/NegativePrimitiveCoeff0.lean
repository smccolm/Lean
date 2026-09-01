import GafniTao.FordNegativeIntegralFormula

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordNegativePrimitiveExplicit_coeff_1 :
    fordNegativePrimitiveExplicit.coeff 1 =
      Polynomial.C (1 / (1 : ℚ)) *
        fordNegativeUpperExplicit.coeff 0 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_2 :
    fordNegativePrimitiveExplicit.coeff 2 =
      Polynomial.C (1 / (2 : ℚ)) *
        fordNegativeUpperExplicit.coeff 1 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_3 :
    fordNegativePrimitiveExplicit.coeff 3 =
      Polynomial.C (1 / (3 : ℚ)) *
        fordNegativeUpperExplicit.coeff 2 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_4 :
    fordNegativePrimitiveExplicit.coeff 4 =
      Polynomial.C (1 / (4 : ℚ)) *
        fordNegativeUpperExplicit.coeff 3 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_5 :
    fordNegativePrimitiveExplicit.coeff 5 =
      Polynomial.C (1 / (5 : ℚ)) *
        fordNegativeUpperExplicit.coeff 4 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_6 :
    fordNegativePrimitiveExplicit.coeff 6 =
      Polynomial.C (1 / (6 : ℚ)) *
        fordNegativeUpperExplicit.coeff 5 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_7 :
    fordNegativePrimitiveExplicit.coeff 7 =
      Polynomial.C (1 / (7 : ℚ)) *
        fordNegativeUpperExplicit.coeff 6 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_8 :
    fordNegativePrimitiveExplicit.coeff 8 =
      Polynomial.C (1 / (8 : ℚ)) *
        fordNegativeUpperExplicit.coeff 7 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_9 :
    fordNegativePrimitiveExplicit.coeff 9 =
      Polynomial.C (1 / (9 : ℚ)) *
        fordNegativeUpperExplicit.coeff 8 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_10 :
    fordNegativePrimitiveExplicit.coeff 10 =
      Polynomial.C (1 / (10 : ℚ)) *
        fordNegativeUpperExplicit.coeff 9 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_11 :
    fordNegativePrimitiveExplicit.coeff 11 =
      Polynomial.C (1 / (11 : ℚ)) *
        fordNegativeUpperExplicit.coeff 10 := by
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

@[simp] theorem fordNegativePrimitiveExplicit_coeff_12 :
    fordNegativePrimitiveExplicit.coeff 12 =
      Polynomial.C (1 / (12 : ℚ)) *
        fordNegativeUpperExplicit.coeff 11 := by
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
