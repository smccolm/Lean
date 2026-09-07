import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

abbrev fordNegativeDiagonalValueCoeff0 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff1 : ℚ :=
  (1 : ℚ)

abbrev fordNegativeDiagonalValueCoeff2 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff3 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff4 : ℚ :=
  (-3 / 4 : ℚ)

abbrev fordNegativeDiagonalValueCoeff5 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff6 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff7 : ℚ :=
  (33 / 70 : ℚ)

abbrev fordNegativeDiagonalValueCoeff8 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff9 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff10 : ℚ :=
  (-129 / 560 : ℚ)

abbrev fordNegativeDiagonalValueCoeff11 : ℚ :=
  (0 : ℚ)

def fordNegativeDiagonalValueBlock0 : Polynomial ℚ :=
  Polynomial.C fordNegativeDiagonalValueCoeff0 * Polynomial.X ^ 0 +
    Polynomial.C fordNegativeDiagonalValueCoeff1 * Polynomial.X ^ 1 +
    Polynomial.C fordNegativeDiagonalValueCoeff2 * Polynomial.X ^ 2 +
    Polynomial.C fordNegativeDiagonalValueCoeff3 * Polynomial.X ^ 3 +
    Polynomial.C fordNegativeDiagonalValueCoeff4 * Polynomial.X ^ 4 +
    Polynomial.C fordNegativeDiagonalValueCoeff5 * Polynomial.X ^ 5 +
    Polynomial.C fordNegativeDiagonalValueCoeff6 * Polynomial.X ^ 6 +
    Polynomial.C fordNegativeDiagonalValueCoeff7 * Polynomial.X ^ 7 +
    Polynomial.C fordNegativeDiagonalValueCoeff8 * Polynomial.X ^ 8 +
    Polynomial.C fordNegativeDiagonalValueCoeff9 * Polynomial.X ^ 9 +
    Polynomial.C fordNegativeDiagonalValueCoeff10 * Polynomial.X ^ 10 +
    Polynomial.C fordNegativeDiagonalValueCoeff11 * Polynomial.X ^ 11

end

end GafniTao
