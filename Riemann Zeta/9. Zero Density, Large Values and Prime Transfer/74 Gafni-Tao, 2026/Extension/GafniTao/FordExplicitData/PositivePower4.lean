import GafniTao.FordExplicitData.PositivePower3

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower4 : Polynomial ℚ :=
  ((((((((((((((((((((((((Polynomial.C (2401 / 3430515856483203578452217359814492160000 : ℚ) * Polynomial.X + Polynomial.C (-343 / 2165729707375759834881450353418240000 : ℚ)) * Polynomial.X + Polynomial.C (4361 / 196884518852341803171040941219840000 : ℚ)) * Polynomial.X + Polynomial.C (-5299 / 2237324077867520490580010695680000 : ℚ)) * Polynomial.X + Polynomial.C (56719 / 271190797317275210979395235840000 : ℚ)) * Polynomial.X + Polynomial.C (-19549 / 1232685442351250958997251072000 : ℚ)) * Polynomial.X + Polynomial.C (89 / 84194074335854856840192000 : ℚ)) * Polynomial.X + Polynomial.C (-1483 / 23582136561663050179776000 : ℚ)) * Polynomial.X + Polynomial.C (57833 / 17150644772118581948928000 : ℚ)) * Polynomial.X + Polynomial.C (-31963 / 194893690592256613056000 : ℚ)) * Polynomial.X + Polynomial.C (8579 / 1181173882377312806400 : ℚ)) * Polynomial.X + Polynomial.C (-15757 / 53689721926241491200 : ℚ)) * Polynomial.X + Polynomial.C (105649 / 9761767622952998400 : ℚ)) * Polynomial.X + Polynomial.C (-4483 / 12325464170395200 : ℚ)) * Polynomial.X + Polynomial.C (12443 / 1120496742763200 : ℚ)) * Polynomial.X + Polynomial.C (-1561 / 5093167012560 : ℚ)) * Polynomial.X + Polynomial.C (71 / 9353842080 : ℚ)) * Polynomial.X + Polynomial.C (-1171 / 7015381560 : ℚ)) * Polynomial.X + Polynomial.C (1229 / 382657176 : ℚ)) * Polynomial.X + Polynomial.C (-128 / 2415765 : ℚ)) * Polynomial.X + Polynomial.C (32 / 43923 : ℚ)) * Polynomial.X + Polynomial.C (-32 / 3993 : ℚ)) * Polynomial.X + Polynomial.C (8 / 121 : ℚ)) * Polynomial.X + Polynomial.C (-4 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower4_step :
    fordPositiveTaylorPower4 =
      fordPositiveTaylorPower3 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 25 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower4,
        fordPositiveTaylorPower3, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower4.natDegree ≤ 24 := by
      unfold fordPositiveTaylorPower4
      compute_degree
    have hright :
        (fordPositiveTaylorPower3 * fordPositiveTaylorPower1).natDegree ≤ 24 := by
      simp only [fordPositiveTaylorPower3, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
