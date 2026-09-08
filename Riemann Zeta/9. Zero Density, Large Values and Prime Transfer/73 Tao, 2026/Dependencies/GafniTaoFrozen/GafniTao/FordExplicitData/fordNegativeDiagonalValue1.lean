import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

abbrev fordNegativeDiagonalValueCoeff12 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff13 : ℚ :=
  (521 / 5720 : ℚ)

abbrev fordNegativeDiagonalValueCoeff14 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff15 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff16 : ℚ :=
  (-19321 / 640640 : ℚ)

abbrev fordNegativeDiagonalValueCoeff17 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff18 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff19 : ℚ :=
  (23549719 / 2742719616 : ℚ)

abbrev fordNegativeDiagonalValueCoeff20 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff21 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff22 : ℚ :=
  (-319699139 / 149191891200 : ℚ)

abbrev fordNegativeDiagonalValueCoeff23 : ℚ :=
  (0 : ℚ)

def fordNegativeDiagonalValueBlock1 : Polynomial ℚ :=
  Polynomial.C fordNegativeDiagonalValueCoeff12 * Polynomial.X ^ 12 +
    Polynomial.C fordNegativeDiagonalValueCoeff13 * Polynomial.X ^ 13 +
    Polynomial.C fordNegativeDiagonalValueCoeff14 * Polynomial.X ^ 14 +
    Polynomial.C fordNegativeDiagonalValueCoeff15 * Polynomial.X ^ 15 +
    Polynomial.C fordNegativeDiagonalValueCoeff16 * Polynomial.X ^ 16 +
    Polynomial.C fordNegativeDiagonalValueCoeff17 * Polynomial.X ^ 17 +
    Polynomial.C fordNegativeDiagonalValueCoeff18 * Polynomial.X ^ 18 +
    Polynomial.C fordNegativeDiagonalValueCoeff19 * Polynomial.X ^ 19 +
    Polynomial.C fordNegativeDiagonalValueCoeff20 * Polynomial.X ^ 20 +
    Polynomial.C fordNegativeDiagonalValueCoeff21 * Polynomial.X ^ 21 +
    Polynomial.C fordNegativeDiagonalValueCoeff22 * Polynomial.X ^ 22 +
    Polynomial.C fordNegativeDiagonalValueCoeff23 * Polynomial.X ^ 23

end

end GafniTao
