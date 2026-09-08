import GafniTao.FordExplicitData.PositivePower11

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveTaylorPower11_coeff_12 :
    fordPositiveTaylorPower11.coeff 12 =
      (2223750343 / 1064920104322145280 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_13 :
    fordPositiveTaylorPower11.coeff 13 =
      (-209086663 / 1301569016393733120 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_14 :
    fordPositiveTaylorPower11.coeff 14 =
      (54763061 / 4772419726777021440 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_15 :
    fordPositiveTaylorPower11.coeff 15 =
      (-3614203423 / 4724695529509251225600 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_16 :
    fordPositiveTaylorPower11.coeff 16 =
      (9937075933 / 207886603298407053926400 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_17 :
    fordPositiveTaylorPower11.coeff 17 =
      (-584271559 / 207886603298407053926400 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_18 :
    fordPositiveTaylorPower11.coeff 18 =
      (423834832063 / 2716662131903583380710195200 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_19 :
    fordPositiveTaylorPower11.coeff 19 =
      (-3828937571 / 466926303920928393559564800 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_20 :
    fordPositiveTaylorPower11.coeff 20 =
      (168134160937 / 410895147450416986332417024000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_21 :
    fordPositiveTaylorPower11.coeff 21 =
      (-5268916051 / 271190797317275210979395235840 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_22 :
    fordPositiveTaylorPower11.coeff 22 =
      (11545199632951 / 13125634590156120211402729414656000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_23 :
    fordPositiveTaylorPower11.coeff 23 =
      (-124817931833 / 3281408647539030052850682353664000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

end

end GafniTao
