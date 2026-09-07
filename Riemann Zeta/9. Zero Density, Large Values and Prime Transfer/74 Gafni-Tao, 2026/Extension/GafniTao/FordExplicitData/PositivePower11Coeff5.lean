import GafniTao.FordExplicitData.PositivePower11

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordPositiveTaylorPower11_coeff_60 :
    fordPositiveTaylorPower11.coeff 60 =
      (26072935961051 / 313311183296776082971793301592238404309959995084215424996349146013097689528916161803059200000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_61 :
    fordPositiveTaylorPower11.coeff 61 =
      (-2035031577467 / 3446423016264536912689726317514622447409559945926369674959840606144074584818077779833651200000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_62 :
    fordPositiveTaylorPower11.coeff 62 =
      (27689986289 / 7582130635781981207917397898532169384301031881038013284911649333516964086599771115634032640000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_63 :
    fordPositiveTaylorPower11.coeff 63 =
      (-9517686451 / 500420621961610759722548261303123179363868104148508876804168856012119629715584893631846154240000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_64 :
    fordPositiveTaylorPower11.coeff 64 =
      (1735205101 / 22018507366310873427792123497337419892010196582534390579383429664533263707485735319801230786560000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_65 :
    fordPositiveTaylorPower11.coeff 65 =
      (-282475249 / 1211017905147098038528566792353558094060560812039391481866088631549329503911715442589067693260800000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

@[simp] theorem fordPositiveTaylorPower11_coeff_66 :
    fordPositiveTaylorPower11.coeff 66 =
      (1977326743 / 5275193994820759055830436947492099057727802897243589295008682079028879319039432467917978871844044800000000000 : ℚ) := by
  norm_num [fordPositiveTaylorPower11, Polynomial.coeff_one]

end

end GafniTao
