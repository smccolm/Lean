import GafniTao.FordExplicitData.PositivePower5

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower6 : Polynomial ℚ :=
  ((((((((((((((((((((((((((((((((((((Polynomial.C (117649 / 200927391707067669608235089605696026685297673071755264000000 : ℚ) * Polynomial.X + Polynomial.C (-16807 / 84565400550112655559021502359299674530849189003264000000 : ℚ)) * Polynomial.X + Polynomial.C (2401 / 61502109490991022224742910806763399658799410184192000 : ℚ)) * Polynomial.X + Polynomial.C (-9947 / 1747219019630426767748378147919414763034074152960000 : ℚ)) * Polynomial.X + Polynomial.C (130291 / 192531021446878982671997592057235786560228556800000 : ℚ)) * Polynomial.X + Polynomial.C (-16552823 / 240663776808598728339996990071544733200285696000000 : ℚ)) * Polynomial.X + Polynomial.C (134562689 / 21878525164418066212726999097413157563662336000000 : ℚ)) * Polynomial.X + Polynomial.C (-170257 / 345305005751547762195817536259677360537600000 : ℚ)) * Polynomial.X + Polynomial.C (36063911 / 1004523653095411671842378287300879594291200000 : ℚ)) * Polynomial.X + Polynomial.C (-1519957 / 634168972913769994849986292487929036800000 : ℚ)) * Polynomial.X + Polynomial.C (51101599 / 345910348862056360827265250447961292800000 : ℚ)) * Polynomial.X + Polynomial.C (-265761409 / 31446395351096032802478659131632844800000 : ℚ)) * Polynomial.X + Polynomial.C (103028581 / 228701057098880238563481157320966144000 : ℚ)) * Polynomial.X + Polynomial.C (-270013 / 12031831707643110193785835296768000 : ℚ)) * Polynomial.X + Polynomial.C (2290363 / 2187605765026020035233788235776000 : ℚ)) * Polynomial.X + Polynomial.C (-911047 / 19887325136600182138488983961600 : ℚ)) * Polynomial.X + Polynomial.C (11338903 / 6026462162606115799542116352000 : ℚ)) * Polynomial.X + Polynomial.C (-5962933 / 82179029490083397266483404800 : ℚ)) * Polynomial.X + Polynomial.C (58874923 / 22412462588204562890859110400 : ℚ)) * Polynomial.X + Polynomial.C (-1683019 / 18865709249330440143820800 : ℚ)) * Polynomial.X + Polynomial.C (885101 / 311829904947610580889600 : ℚ)) * Polynomial.X + Polynomial.C (-3291923 / 38978738118451322611200 : ℚ)) * Polynomial.X + Polynomial.C (553771 / 236234776475462561280 : ℚ)) * Polynomial.X + Polynomial.C (-59063 / 976176762295299840 : ℚ)) * Polynomial.X + Polynomial.C (5647633 / 3904707049181199360 : ℚ)) * Polynomial.X + Polynomial.C (-157087 / 4930185668158080 : ℚ)) * Polynomial.X + Polynomial.C (288097 / 448198697105280 : ℚ)) * Polynomial.X + Polynomial.C (-4001 / 339544467504 : ℚ)) * Polynomial.X + Polynomial.C (24001 / 123470715456 : ℚ)) * Polynomial.X + Polynomial.C (-7999 / 2806152624 : ℚ)) * Polynomial.X + Polynomial.C (46657 / 1275523920 : ℚ)) * Polynomial.X + Polynomial.C (-324 / 805255 : ℚ)) * Polynomial.X + Polynomial.C (54 / 14641 : ℚ)) * Polynomial.X + Polynomial.C (-36 / 1331 : ℚ)) * Polynomial.X + Polynomial.C (18 / 121 : ℚ)) * Polynomial.X + Polynomial.C (-6 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower6_step :
    fordPositiveTaylorPower6 =
      fordPositiveTaylorPower5 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 37 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower6,
        fordPositiveTaylorPower5, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower6.natDegree ≤ 36 := by
      unfold fordPositiveTaylorPower6
      compute_degree
    have hright :
        (fordPositiveTaylorPower5 * fordPositiveTaylorPower1).natDegree ≤ 36 := by
      simp only [fordPositiveTaylorPower5, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
