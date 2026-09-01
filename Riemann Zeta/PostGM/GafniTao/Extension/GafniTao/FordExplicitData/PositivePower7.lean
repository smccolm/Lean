import GafniTao.FordExplicitData.PositivePower6

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower7 : Polynomial ℚ :=
  ((((((((((((((((((((((((((((((((((((((((((Polynomial.C (823543 / 1537726165833446673863765314652451901716332965940182293707489280000000 : ℚ) * Polynomial.X + Polynomial.C (-823543 / 3883146883417794630969104329930434095243265065505510842695680000000 : ℚ)) * Polynomial.X + Polynomial.C (1529437 / 32092123003452848189827308511821769382175744343020750766080000000 : ℚ)) * Polynomial.X + Polynomial.C (-12622057 / 1604606150172642409491365425591088469108787217151037538304000000 : ℚ)) * Polynomial.X + Polynomial.C (6393863 / 6078053599138797005649111460572304807230254610420596736000000 : ℚ)) * Polynomial.X + Polynomial.C (-120446851 / 1004636958535338348041175448028480133426488365358776320000000 : ℚ)) * Polynomial.X + Polynomial.C (12058855361 / 1004636958535338348041175448028480133426488365358776320000000 : ℚ)) * Polynomial.X + Polynomial.C (-455376329 / 422827002750563277795107511796498372654245945016320000000 : ℚ)) * Polynomial.X + Polynomial.C (337567181 / 3843881843186938889046431925422712478674963136512000000 : ℚ)) * Polynomial.X + Polynomial.C (-2297478617 / 349443803926085353549675629583882952606814830592000000 : ℚ)) * Polynomial.X + Polynomial.C (964458901 / 2117841235915668809391973512629593652162514124800000 : ℚ)) * Polynomial.X + Polynomial.C (-7064913989 / 240663776808598728339996990071544733200285696000000 : ℚ)) * Polynomial.X + Polynomial.C (77415817241 / 43757050328836132425453998194826315127324672000000 : ℚ)) * Polynomial.X + Polynomial.C (-2210998433 / 22099520368099056780532322320619351074406400000 : ℚ)) * Polynomial.X + Polynomial.C (10694936851 / 2009047306190823343684756574601759188582400000 : ℚ)) * Polynomial.X + Polynomial.C (-12195870211 / 45660166049791439629199013059130890649600000 : ℚ)) * Polynomial.X + Polynomial.C (530755939 / 41928527134794710403304878842177126400000 : ℚ)) * Polynomial.X + Polynomial.C (-3243755333 / 5717526427472005964087028933024153600000 : ℚ)) * Polynomial.X + Polynomial.C (3302231219 / 137220634259328143138088694392579686400 : ℚ)) * Polynomial.X + Polynomial.C (-104663419 / 108286485368787991744072517670912000 : ℚ)) * Polynomial.X + Polynomial.C (23160179 / 630030460327493770147331011903488 : ℚ)) * Polynomial.X + Polynomial.C (-74034647 / 55933101946688012264500267392000 : ℚ)) * Polynomial.X + Polynomial.C (1222948769 / 27119079731727521097939523584000 : ℚ)) * Polynomial.X + Polynomial.C (-89518387 / 61634272117562547949862553600 : ℚ)) * Polynomial.X + Polynomial.C (359952551 / 8149986395710750142130585600 : ℚ)) * Polynomial.X + Polynomial.C (-95531233 / 75462836997321760575283200 : ℚ)) * Polynomial.X + Polynomial.C (234152737 / 6860257908847432779571200 : ℚ)) * Polynomial.X + Polynomial.C (-134617693 / 155914952473805290444800 : ℚ)) * Polynomial.X + Polynomial.C (9651541 / 472469552950925122560 : ℚ)) * Polynomial.X + Polynomial.C (-3868613 / 8590355508198638592 : ℚ)) * Polynomial.X + Polynomial.C (179787433 / 19523535245905996800 : ℚ)) * Polynomial.X + Polynomial.C (-4281949 / 24650928340790400 : ℚ)) * Polynomial.X + Polynomial.C (6728561 / 2240993485526400 : ℚ)) * Polynomial.X + Polynomial.C (-961079 / 20372668050240 : ℚ)) * Polynomial.X + Polynomial.C (45759 / 68594841920 : ℚ)) * Polynomial.X + Polynomial.C (-23531 / 2806152624 : ℚ)) * Polynomial.X + Polynomial.C (705901 / 7653143520 : ℚ)) * Polynomial.X + Polynomial.C (-16807 / 19326120 : ℚ)) * Polynomial.X + Polynomial.C (2401 / 351384 : ℚ)) * Polynomial.X + Polynomial.C (-343 / 7986 : ℚ)) * Polynomial.X + Polynomial.C (49 / 242 : ℚ)) * Polynomial.X + Polynomial.C (-7 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower7_step :
    fordPositiveTaylorPower7 =
      fordPositiveTaylorPower6 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 43 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower7,
        fordPositiveTaylorPower6, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower7.natDegree ≤ 42 := by
      unfold fordPositiveTaylorPower7
      compute_degree
    have hright :
        (fordPositiveTaylorPower6 * fordPositiveTaylorPower1).natDegree ≤ 42 := by
      simp only [fordPositiveTaylorPower6, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
