import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

abbrev fordNegativeUpperCoeff0 : Polynomial ℚ :=
  Polynomial.C (1 : ℚ)

abbrev fordNegativeUpperCoeff1 : Polynomial ℚ :=
  Polynomial.C (0 : ℚ)

abbrev fordNegativeUpperCoeff2 : Polynomial ℚ :=
  (Polynomial.C (-3 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff3 : Polynomial ℚ :=
  Polynomial.C (1 : ℚ)

abbrev fordNegativeUpperCoeff4 : Polynomial ℚ :=
  ((Polynomial.C (9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff5 : Polynomial ℚ :=
  (Polynomial.C (-3 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff6 : Polynomial ℚ :=
  (((Polynomial.C (-9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 2 : ℚ))

abbrev fordNegativeUpperCoeff7 : Polynomial ℚ :=
  ((Polynomial.C (9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff8 : Polynomial ℚ :=
  ((((Polynomial.C (27 / 8 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-3 / 2 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff9 : Polynomial ℚ :=
  (((Polynomial.C (-9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 6 : ℚ))

abbrev fordNegativeUpperCoeff10 : Polynomial ℚ :=
  (((((Polynomial.C (-81 / 40 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (9 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff11 : Polynomial ℚ :=
  ((((Polynomial.C (27 / 8 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 2 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff12 : Polynomial ℚ :=
  ((((((Polynomial.C (1459 / 1440 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-9 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 24 : ℚ))

abbrev fordNegativeUpperCoeff13 : Polynomial ℚ :=
  (((((Polynomial.C (-1459 / 720 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (3 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff14 : Polynomial ℚ :=
  (((((((Polynomial.C (-313 / 720 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1459 / 864 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 8 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff15 : Polynomial ℚ :=
  ((((((Polynomial.C (2191 / 2160 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1459 / 1944 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 120 : ℚ))

abbrev fordNegativeUpperCoeff16 : Polynomial ℚ :=
  ((((((((Polynomial.C (469 / 2880 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-2191 / 2160 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1459 / 7776 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff17 : Polynomial ℚ :=
  (((((((Polynomial.C (-469 / 1080 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (2191 / 3888 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1459 / 58320 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordNegativeUpperCoeff18 : Polynomial ℚ :=
  (((((((((Polynomial.C (-31 / 576 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (3283 / 6480 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-2191 / 11664 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1459 / 1049760 : ℚ))

abbrev fordNegativeUpperCoeff19 : Polynomial ℚ :=
  ((((((((Polynomial.C (31 / 192 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-3283 / 9720 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (2191 / 58320 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

end

end GafniTao
