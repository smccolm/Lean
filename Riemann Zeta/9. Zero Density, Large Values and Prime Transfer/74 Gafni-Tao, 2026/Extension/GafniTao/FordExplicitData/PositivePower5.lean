import GafniTao.FordExplicitData.PositivePower4

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower5 : Polynomial ℚ :=
  ((((((((((((((((((((((((((((((Polynomial.C (16807 / 26254230197301679455272398916895789076394803200000 : ℚ) * Polynomial.X + Polynomial.C (-2401 / 13259712220859434068319393392371610644643840000 : ℚ)) * Polynomial.X + Polynomial.C (36701 / 1205428383714494006210853944761055513149440000 : ℚ)) * Polynomial.X + Polynomial.C (-105497 / 27396099629874863777519407835478534389760000 : ℚ)) * Polynomial.X + Polynomial.C (331751 / 830184837268935265985436601075107102720000 : ℚ)) * Polynomial.X + Polynomial.C (-6709309 / 188678372106576196814871954789797068800000 : ℚ)) * Polynomial.X + Polynomial.C (1911397 / 686103171296640715690443471962898432000 : ℚ)) * Polynomial.X + Polynomial.C (-84679 / 433145941475151966976290070683648000 : ℚ)) * Polynomial.X + Polynomial.C (195847 / 15750761508187344253683275297587200 : ℚ)) * Polynomial.X + Polynomial.C (-646799 / 894929631147008196232004278272000 : ℚ)) * Polynomial.X + Polynomial.C (523661 / 13559539865863760548969761792000 : ℚ)) * Polynomial.X + Polynomial.C (-234833 / 123268544235125095899725107200 : ℚ)) * Polynomial.X + Polynomial.C (3899737 / 44824925176409125781718220800 : ℚ)) * Polynomial.X + Polynomial.C (-69511 / 18865709249330440143820800 : ℚ)) * Polynomial.X + Polynomial.C (124189 / 857532238605929097446400 : ℚ)) * Polynomial.X + Polynomial.C (-411793 / 77957476236902645222400 : ℚ)) * Polynomial.X + Polynomial.C (2813 / 15748985098364170752 : ℚ)) * Polynomial.X + Polynomial.C (-120019 / 21475888770496596480 : ℚ)) * Polynomial.X + Polynomial.C (944923 / 5857060573771799040 : ℚ)) * Polynomial.X + Polynomial.C (-31651 / 7395278502237120 : ℚ)) * Polynomial.X + Polynomial.C (6343 / 61118004150720 : ℚ)) * Polynomial.X + Polynomial.C (-13961 / 6111800415072 : ℚ)) * Polynomial.X + Polynomial.C (8375 / 185206073184 : ℚ)) * Polynomial.X + Polynomial.C (-3349 / 4209228936 : ℚ)) * Polynomial.X + Polynomial.C (18751 / 1530628704 : ℚ)) * Polynomial.X + Polynomial.C (-625 / 3865224 : ℚ)) * Polynomial.X + Polynomial.C (625 / 351384 : ℚ)) * Polynomial.X + Polynomial.C (-125 / 7986 : ℚ)) * Polynomial.X + Polynomial.C (25 / 242 : ℚ)) * Polynomial.X + Polynomial.C (-5 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower5_step :
    fordPositiveTaylorPower5 =
      fordPositiveTaylorPower4 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 31 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower5,
        fordPositiveTaylorPower4, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower5.natDegree ≤ 30 := by
      unfold fordPositiveTaylorPower5
      compute_degree
    have hright :
        (fordPositiveTaylorPower4 * fordPositiveTaylorPower1).natDegree ≤ 30 := by
      simp only [fordPositiveTaylorPower4, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
