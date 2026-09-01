import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

abbrev fordPositiveUpperCoeff0 : Polynomial ℚ :=
  Polynomial.C (1 : ℚ)

abbrev fordPositiveUpperCoeff1 : Polynomial ℚ :=
  Polynomial.C (0 : ℚ)

abbrev fordPositiveUpperCoeff2 : Polynomial ℚ :=
  (Polynomial.C (-3 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff3 : Polynomial ℚ :=
  Polynomial.C (-1 : ℚ)

abbrev fordPositiveUpperCoeff4 : Polynomial ℚ :=
  ((Polynomial.C (9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff5 : Polynomial ℚ :=
  (Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff6 : Polynomial ℚ :=
  (((Polynomial.C (-9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 2 : ℚ))

abbrev fordPositiveUpperCoeff7 : Polynomial ℚ :=
  ((Polynomial.C (-9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff8 : Polynomial ℚ :=
  ((((Polynomial.C (27 / 8 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-3 / 2 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff9 : Polynomial ℚ :=
  (((Polynomial.C (9 / 2 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 6 : ℚ))

abbrev fordPositiveUpperCoeff10 : Polynomial ℚ :=
  (((((Polynomial.C (-81 / 40 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (9 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff11 : Polynomial ℚ :=
  ((((Polynomial.C (-27 / 8 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 2 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff12 : Polynomial ℚ :=
  ((((((Polynomial.C (26090289 / 25768160 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-9 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (1 / 24 : ℚ))

abbrev fordPositiveUpperCoeff13 : Polynomial ℚ :=
  (((((Polynomial.C (26090289 / 12884080 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-3 / 4 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff14 : Polynomial ℚ :=
  (((((((Polynomial.C (-12299769 / 28344976 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (8696763 / 5153632 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 8 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff15 : Polynomial ℚ :=
  ((((((Polynomial.C (-28699461 / 28344976 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (966307 / 1288408 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 120 : ℚ))

abbrev fordPositiveUpperCoeff16 : Polynomial ℚ :=
  ((((((((Polynomial.C (202948983 / 1247178944 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-28699461 / 28344976 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (966307 / 5153632 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff17 : Polynomial ℚ :=
  (((((((Polynomial.C (67649661 / 155897368 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-15944145 / 28344976 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (966307 / 38652240 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

abbrev fordPositiveUpperCoeff18 : Polynomial ℚ :=
  (((((((((Polynomial.C (-744167331 / 13718968384 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (157849209 / 311794736 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-5314715 / 28344976 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (966307 / 695740320 : ℚ))

abbrev fordPositiveUpperCoeff19 : Polynomial ℚ :=
  ((((((((Polynomial.C (-2232501993 / 13718968384 : ℚ) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (52616403 / 155897368 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (-1062943 / 28344976 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ)) * Polynomial.X + Polynomial.C (0 : ℚ))

end

end GafniTao
