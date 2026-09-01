import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

abbrev fordNegativeUpperCoeff40 : Polynomial ℚ :=
  ((((((((((((((Polynomial.C (5831 / 36279705600 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-75803 / 68024448000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (71071 / 54419558400 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-983983 / 3673320192000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (3913 / 661197634560 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff41 : Polynomial ℚ :=
  (((((((((((((Polynomial.C (-40817 / 272097792000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (119119 / 204073344000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-71071 / 183666009600 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (89453 / 2203992115200 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-301 / 991796451840 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff42 : Polynomial ℚ :=
  ((((((((((((Polynomial.C (530621 / 4897760256000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-119119 / 489776025600 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (497497 / 5509980288000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-89453 / 19835929036800 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (43 / 5950778711040 : ℚ))

abbrev fordNegativeUpperCoeff43 : Polynomial ℚ :=
  (((((((((((Polynomial.C (-75803 / 1224440064000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (119119 / 1469328076800 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-45227 / 2754990144000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (6881 / 19835929036800 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff44 : Polynomial ℚ :=
  ((((((((((Polynomial.C (833833 / 29386561536000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-119119 / 5509980288000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (45227 / 19835929036800 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-983 / 59507787110400 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff45 : Polynomial ℚ :=
  (((((((((Polynomial.C (-833833 / 79343716147200 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (75803 / 16529940864000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-3479 / 14876946777600 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (983 / 2677850419968000 : ℚ))

abbrev fordNegativeUpperCoeff46 : Polynomial ℚ :=
  ((((((((Polynomial.C (833833 / 264479053824000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-75803 / 99179645184000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (497 / 29753893555200 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff47 : Polynomial ℚ :=
  (((((((Polynomial.C (-75803 / 99179645184000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (5831 / 59507787110400 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-497 / 669462604992000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff48 : Polynomial ℚ :=
  ((((((Polynomial.C (530621 / 3570467226624000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-833 / 89261680665600 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (497 / 32134205039616000 : ℚ))

abbrev fordNegativeUpperCoeff49 : Polynomial ℚ :=
  (((((Polynomial.C (-40817 / 1785233613312000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (833 / 1338925209984000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff50 : Polynomial ℚ :=
  ((((Polynomial.C (5831 / 2142280335974400 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-833 / 32134205039616000 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff51 : Polynomial ℚ :=
  (((Polynomial.C (-5831 / 24100653779712000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (49 / 96402615118848000 : ℚ))

abbrev fordNegativeUpperCoeff52 : Polynomial ℚ :=
  ((Polynomial.C (5831 / 385610460475392000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff53 : Polynomial ℚ :=
  (Polynomial.C (-343 / 578415690713088000 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff54 : Polynomial ℚ :=
  Polynomial.C (343 / 31234447298506752000 : ℚ)

end

end GafniTao
