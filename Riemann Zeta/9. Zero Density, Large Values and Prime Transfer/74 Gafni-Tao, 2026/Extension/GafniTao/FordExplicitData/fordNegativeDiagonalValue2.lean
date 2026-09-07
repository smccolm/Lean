import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

abbrev fordNegativeDiagonalValueCoeff24 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff25 : ℚ :=
  (6108627917 / 12867800616000 : ℚ)

abbrev fordNegativeDiagonalValueCoeff26 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff27 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff28 : ℚ :=
  (-1726499647 / 18368154604800 : ℚ)

abbrev fordNegativeDiagonalValueCoeff29 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff30 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff31 : ℚ :=
  (101220200959 / 6068741606928000 : ℚ)

abbrev fordNegativeDiagonalValueCoeff32 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff33 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff34 : ℚ :=
  (-1978772156909 / 746029617591398400 : ℚ)

abbrev fordNegativeDiagonalValueCoeff35 : ℚ :=
  (0 : ℚ)

def fordNegativeDiagonalValueBlock2 : Polynomial ℚ :=
  Polynomial.C fordNegativeDiagonalValueCoeff24 * Polynomial.X ^ 24 +
    Polynomial.C fordNegativeDiagonalValueCoeff25 * Polynomial.X ^ 25 +
    Polynomial.C fordNegativeDiagonalValueCoeff26 * Polynomial.X ^ 26 +
    Polynomial.C fordNegativeDiagonalValueCoeff27 * Polynomial.X ^ 27 +
    Polynomial.C fordNegativeDiagonalValueCoeff28 * Polynomial.X ^ 28 +
    Polynomial.C fordNegativeDiagonalValueCoeff29 * Polynomial.X ^ 29 +
    Polynomial.C fordNegativeDiagonalValueCoeff30 * Polynomial.X ^ 30 +
    Polynomial.C fordNegativeDiagonalValueCoeff31 * Polynomial.X ^ 31 +
    Polynomial.C fordNegativeDiagonalValueCoeff32 * Polynomial.X ^ 32 +
    Polynomial.C fordNegativeDiagonalValueCoeff33 * Polynomial.X ^ 33 +
    Polynomial.C fordNegativeDiagonalValueCoeff34 * Polynomial.X ^ 34 +
    Polynomial.C fordNegativeDiagonalValueCoeff35 * Polynomial.X ^ 35

end

end GafniTao
