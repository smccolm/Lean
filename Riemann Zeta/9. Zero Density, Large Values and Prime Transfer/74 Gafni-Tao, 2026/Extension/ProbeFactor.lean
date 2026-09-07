import GafniTao.FordNumericalIntegralUpper

namespace GafniTao

def probeRatHom : ℚ →+* FordBiPolynomial :=
  (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ)).comp
    (Polynomial.C : ℚ →+* Polynomial ℚ)

def probeLift (p : Polynomial ℚ) : FordBiPolynomial :=
  Polynomial.eval₂ probeRatHom fordPositivePhasePolynomial p

example (p q : Polynomial ℚ) :
    probeLift (p * q) = probeLift p * probeLift q := by
  exact map_mul (Polynomial.eval₂RingHom probeRatHom fordPositivePhasePolynomial) p q

end GafniTao
