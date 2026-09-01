import GafniTao.FordExplicitData.PositivePower11

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveTaylorPower11_coeff_24 :
    fordPositiveTaylorPower11.coeff 24 =
      (16360523873041 / 10395502595403647207430961696407552000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_25 :
    fordPositiveTaylorPower11.coeff 25 =
      (-178354557929263 / 2858763213736002982043514466512076800000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_26 :
    fordPositiveTaylorPower11.coeff 26 =
      (149220699363391 / 62892790702192065604957318263265689600000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_27 :
    fordPositiveTaylorPower11.coeff 27 =
      (-179852802183979 / 2075462093172338164963591502687767756800000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_28 :
    fordPositiveTaylorPower11.coeff 28 =
      (277857066494707 / 91320332099582879258398026118261781299200000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_29 :
    fordPositiveTaylorPower11.coeff 29 =
      (-103255770313253 / 1004523653095411671842378287300879594291200000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_30 :
    fordPositiveTaylorPower11.coeff 30 =
      (6650427061651073 / 1988956833128915110247909008855741596696576000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_31 :
    fordPositiveTaylorPower11.coeff 31 =
      (-382124746304861 / 3646420860736344368787833182902192927277056000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_32 :
    fordPositiveTaylorPower11.coeff 32 =
      (205244371141 / 64825259746423899889561478807150096484925440000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_33 :
    fordPositiveTaylorPower11.coeff 33 =
      (-1074569193088229 / 11648126797536178451655854319462765086893827686400000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_34 :
    fordPositiveTaylorPower11.coeff 34 =
      (3775776769157 / 1456015849692022306456981789932845635861728460800000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_35 :
    fordPositiveTaylorPower11.coeff 35 =
      (-3605207165423 / 51251757909159185187285759005636166382332841820160000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

end

end GafniTao
