import GafniTao.FordExplicitData.PositivePower7

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower8 : Polynomial ℚ :=
  ((((((((((((((((((((((((((((((((((((((((((((((((Polynomial.C (5764801 / 11768439041582687811346028880633173323732030516447486828706208358701465600000000 : ℚ) * Polynomial.X + Polynomial.C (-823543 / 3714785051004636304086499015351380468349757107464484478758272840499200000000 : ℚ)) * Polynomial.X + Polynomial.C (18941489 / 337707731909512391280590819577398224395432464314953134432570258227200000000 : ℚ)) * Polynomial.X + Polynomial.C (-39647713 / 3837587862608095355461259313379525277220823458124467436733752934400000000 : ℚ)) * Polynomial.X + Polynomial.C (142674623 / 93032433032923523768757801536473340053838144439381028769303101440000000 : ℚ)) * Polynomial.X + Polynomial.C (-2044281029 / 10571867390104945882813386538235606824299789140838753269238988800000000 : ℚ)) * Polynomial.X + Polynomial.C (1867802041 / 87370804876900379196804847423434767142973463973873993960652800000000 : ℚ)) * Polynomial.X + Polynomial.C (-1283941337 / 606741700534030411088922551551630327381760166485236069171200000000 : ℚ)) * Polynomial.X + Polynomial.C (83987761861 / 441266691297476662610125492037549329004916484716535323033600000000 : ℚ)) * Polynomial.X + Polynomial.C (-286724099 / 18234160797416391016947334381716914421690763831261790208000000 : ℚ)) * Polynomial.X + Polynomial.C (36561380461 / 30390267995693985028245557302861524036151273052102983680000000 : ℚ)) * Polynomial.X + Polynomial.C (-118498995719 / 1381375817986090228556616241039160183461421502368317440000000 : ℚ)) * Polynomial.X + Polynomial.C (287792905003 / 50231847926766917402058772401424006671324418267938816000000 : ℚ)) * Polynomial.X + Polynomial.C (-38038716223 / 105706750687640819448776877949124593163561486254080000000 : ℚ)) * Polynomial.X + Polynomial.C (8196739523 / 384388184318693888904643192542271247867496313651200000 : ℚ)) * Polynomial.X + Polynomial.C (-52211264491 / 43680475490760669193709453697985369075851853824000000 : ℚ)) * Polynomial.X + Polynomial.C (28022366287 / 441216924149097668623327815131165344200523776000000 : ℚ)) * Polynomial.X + Polynomial.C (-192787238057 / 60165944202149682084999247517886183300071424000000 : ℚ)) * Polynomial.X + Polynomial.C (2522050237499 / 16408893873313549659545249323059868172746752000000 : ℚ)) * Polynomial.X + Polynomial.C (-29074620259 / 4143660069018573146349810435116128326451200000 : ℚ)) * Polynomial.X + Polynomial.C (20894785229 / 68490249074687159443798519588696335974400000 : ℚ)) * Polynomial.X + Polynomial.C (-54103460509 / 4280640567167947465237407474293520998400000 : ℚ)) * Polynomial.X + Polynomial.C (64736100997 / 129716380823271135310224468917985484800000 : ℚ)) * Polynomial.X + Polynomial.C (-442943976163 / 23584796513322024601858994348724633600000 : ℚ)) * Polynomial.X + Polynomial.C (231033278719 / 343051585648320357845221735981449216000 : ℚ)) * Polynomial.X + Polynomial.C (-4981473667 / 216572970737575983488145035341824000 : ℚ)) * Polynomial.X + Polynomial.C (14721442453 / 19688451885234180317104094121984000 : ℚ)) * Polynomial.X + Polynomial.C (-1292831527 / 55933101946688012264500267392000 : ℚ)) * Polynomial.X + Polynomial.C (18404420741 / 27119079731727521097939523584000 : ℚ)) * Polynomial.X + Polynomial.C (-2329612171 / 123268544235125095899725107200 : ℚ)) * Polynomial.X + Polynomial.C (27918477061 / 56031156470511407227147776000 : ℚ)) * Polynomial.X + Polynomial.C (-292691389 / 23582136561663050179776000 : ℚ)) * Polynomial.X + Polynomial.C (2498580923 / 8575322386059290974464000 : ℚ)) * Polynomial.X + Polynomial.C (-626326741 / 97446845296128306528000 : ℚ)) * Polynomial.X + Polynomial.C (348493 / 2624830849727361792 : ℚ)) * Polynomial.X + Polynomial.C (-68661019 / 26844860963120745600 : ℚ)) * Polynomial.X + Polynomial.C (669621367 / 14642651434429497600 : ℚ)) * Polynomial.X + Polynomial.C (-2790089 / 3697639251118560 : ℚ)) * Polynomial.X + Polynomial.C (19179761 / 1680745114144800 : ℚ)) * Polynomial.X + Polynomial.C (-239717 / 1527950103768 : ℚ)) * Polynomial.X + Polynomial.C (898853 / 463015182960 : ℚ)) * Polynomial.X + Polynomial.C (-224701 / 10523072340 : ℚ)) * Polynomial.X + Polynomial.C (196609 / 956642940 : ℚ)) * Polynomial.X + Polynomial.C (-4096 / 2415765 : ℚ)) * Polynomial.X + Polynomial.C (512 / 43923 : ℚ)) * Polynomial.X + Polynomial.C (-256 / 3993 : ℚ)) * Polynomial.X + Polynomial.C (32 / 121 : ℚ)) * Polynomial.X + Polynomial.C (-8 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

theorem fordPositiveTaylorPower8_step :
    fordPositiveTaylorPower8 =
      fordPositiveTaylorPower7 * fordPositiveTaylorPower1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 49 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;>
      norm_num [fordPositiveTaylorPower8,
        fordPositiveTaylorPower7, fordPositiveTaylorPower1]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower8.natDegree ≤ 48 := by
      unfold fordPositiveTaylorPower8
      compute_degree
    have hright :
        (fordPositiveTaylorPower7 * fordPositiveTaylorPower1).natDegree ≤ 48 := by
      simp only [fordPositiveTaylorPower7, fordPositiveTaylorPower1]
      compute_degree
    omega

end

end GafniTao
