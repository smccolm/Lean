import GafniTao.FordExplicitData.PositivePower1

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower2 : Polynomial ℚ :=
  ((((((((((((Polynomial.C (49 / 58570605737717990400 : ℚ) * Polynomial.X + Polynomial.C (-7 / 73952785022371200 : ℚ)) * Polynomial.X + Polynomial.C (53 / 6722980456579200 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 1909937629710 : ℚ)) * Polynomial.X + Polynomial.C (53 / 1852060731840 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 765314352 : ℚ)) * Polynomial.X + Polynomial.C (193 / 3826571760 : ℚ)) * Polynomial.X + Polynomial.C (-4 / 2415765 : ℚ)) * Polynomial.X + Polynomial.C (2 / 43923 : ℚ)) * Polynomial.X + Polynomial.C (-4 / 3993 : ℚ)) * Polynomial.X + Polynomial.C (2 / 121 : ℚ)) * Polynomial.X + Polynomial.C (-2 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower2_step :
    fordPositiveTaylorPower2 =
      fordPositiveTaylorPower1 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 13 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower2,
        fordPositiveTaylorPower1, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower2.natDegree ≤ 12 := by
      unfold fordPositiveTaylorPower2
      compute_degree
    have hright :
        (fordPositiveTaylorPower1 * fordPositiveTaylorPower1).natDegree ≤ 12 := by
      simp only [fordPositiveTaylorPower1, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
