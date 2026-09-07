import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

noncomputable section

abbrev fordNegativeDiagonalValueCoeff48 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff49 : ℚ :=
  (748686971105159183 / 18785349676719134495788032000 : ℚ)

abbrev fordNegativeDiagonalValueCoeff50 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff51 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff52 : ℚ :=
  (-138430832781861187 / 55968574285106665037107200000 : ℚ)

abbrev fordNegativeDiagonalValueCoeff53 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff54 : ℚ :=
  (0 : ℚ)

abbrev fordNegativeDiagonalValueCoeff55 : ℚ :=
  (2702420847547466017 / 26697009933995879222700134400000 : ℚ)

def fordNegativeDiagonalValueBlock4 : Polynomial ℚ :=
  Polynomial.C fordNegativeDiagonalValueCoeff48 * Polynomial.X ^ 48 +
    Polynomial.C fordNegativeDiagonalValueCoeff49 * Polynomial.X ^ 49 +
    Polynomial.C fordNegativeDiagonalValueCoeff50 * Polynomial.X ^ 50 +
    Polynomial.C fordNegativeDiagonalValueCoeff51 * Polynomial.X ^ 51 +
    Polynomial.C fordNegativeDiagonalValueCoeff52 * Polynomial.X ^ 52 +
    Polynomial.C fordNegativeDiagonalValueCoeff53 * Polynomial.X ^ 53 +
    Polynomial.C fordNegativeDiagonalValueCoeff54 * Polynomial.X ^ 54 +
    Polynomial.C fordNegativeDiagonalValueCoeff55 * Polynomial.X ^ 55

end

end GafniTao
