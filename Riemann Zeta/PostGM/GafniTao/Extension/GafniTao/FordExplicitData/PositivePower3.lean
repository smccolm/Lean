import GafniTao.FordExplicitData.PositivePower2

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower3 : Polynomial ℚ :=
  ((((((((((((((((((Polynomial.C (343 / 448249251764091257817182208000 : ℚ) * Polynomial.X + Polynomial.C (-49 / 377314184986608802876416000 : ℚ)) * Polynomial.X + Polynomial.C (497 / 34301289544237163897856000 : ℚ)) * Polynomial.X + Polynomial.C (-983 / 779574762369026452224000 : ℚ)) * Polynomial.X + Polynomial.C (43 / 472469552950925122560 : ℚ)) * Polynomial.X + Polynomial.C (-1207 / 214758887704965964800 : ℚ)) * Polynomial.X + Polynomial.C (5911 / 19523535245905996800 : ℚ)) * Polynomial.X + Polynomial.C (-71 / 4930185668158080 : ℚ)) * Polynomial.X + Polynomial.C (1363 / 2240993485526400 : ℚ)) * Polynomial.X + Polynomial.C (-31 / 1358177870016 : ℚ)) * Polynomial.X + Polynomial.C (469 / 617353577280 : ℚ)) * Polynomial.X + Polynomial.C (-313 / 14030763120 : ℚ)) * Polynomial.X + Polynomial.C (1459 / 2551047840 : ℚ)) * Polynomial.X + Polynomial.C (-81 / 6442040 : ℚ)) * Polynomial.X + Polynomial.C (27 / 117128 : ℚ)) * Polynomial.X + Polynomial.C (-9 / 2662 : ℚ)) * Polynomial.X + Polynomial.C (9 / 242 : ℚ)) * Polynomial.X + Polynomial.C (-3 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower3_step :
    fordPositiveTaylorPower3 =
      fordPositiveTaylorPower2 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 19 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower3,
        fordPositiveTaylorPower2, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower3.natDegree ≤ 18 := by
      unfold fordPositiveTaylorPower3
      compute_degree
    have hright :
        (fordPositiveTaylorPower2 * fordPositiveTaylorPower1).natDegree ≤ 18 := by
      simp only [fordPositiveTaylorPower2, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
