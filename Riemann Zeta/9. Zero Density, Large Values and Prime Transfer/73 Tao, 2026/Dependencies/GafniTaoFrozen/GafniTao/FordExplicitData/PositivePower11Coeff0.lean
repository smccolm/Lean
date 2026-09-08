import GafniTao.FordExplicitData.PositivePower11

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveTaylorPower11_coeff_0 :
    fordPositiveTaylorPower11.coeff 0 =
      (1 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_1 :
    fordPositiveTaylorPower11.coeff 1 =
      (-1 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_2 :
    fordPositiveTaylorPower11.coeff 2 =
      (1 / 2 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_3 :
    fordPositiveTaylorPower11.coeff 3 =
      (-1 / 6 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_4 :
    fordPositiveTaylorPower11.coeff 4 =
      (1 / 24 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_5 :
    fordPositiveTaylorPower11.coeff 5 =
      (-1 / 120 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_6 :
    fordPositiveTaylorPower11.coeff 6 =
      (966307 / 695740320 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_7 :
    fordPositiveTaylorPower11.coeff 7 =
      (-151849 / 765314352 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_8 :
    fordPositiveTaylorPower11.coeff 8 =
      (835181 / 33673831488 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_9 :
    fordPositiveTaylorPower11.coeff 9 =
      (-3062417 / 1111236439104 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_10 :
    fordPositiveTaylorPower11.coeff 10 =
      (33688187 / 122236008301440 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_11 :
    fordPositiveTaylorPower11.coeff 11 =
      (-370595057 / 14790557004474240 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

end

end GafniTao
