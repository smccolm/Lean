import Dubon2026.SourceEllipticVeluTwoJInvariant

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> cyclic-quotient interpretation of integral modular-polynomial roots.
This step factors the explicit classical prime-two polynomial into the j-values
of the three actual degree-two Velu curves. Identification of this explicit
polynomial with the existing integral minimal polynomial is a separate required
bridge. The quotient group homomorphism and its kernel remain required too.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the VeluQuotient2 cFour/j solutions,
Def_ModularCurve_ClassicalModularPolynomials, Def_ModularCurve_FibrePoly and
S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j. -/
namespace Dubon2026.SourcePrimeTwoPolynomial
open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
noncomputable section
/-- The quadratic coefficient of the explicit prime-two polynomial. -/
def phiTwoC2 : Polynomial ℤ := -Polynomial.X ^ 2 + 1488 * Polynomial.X - 162000

/-- The linear coefficient of the explicit prime-two polynomial. -/
def phiTwoC1 : Polynomial ℤ :=
  1488 * Polynomial.X ^ 2 + 40773375 * Polynomial.X + 8748000000

/-- The constant coefficient of the explicit prime-two polynomial. -/
def phiTwoC0 : Polynomial ℤ :=
  Polynomial.X ^ 3 - 162000 * Polynomial.X ^ 2 + 8748000000 * Polynomial.X
    - 157464000000000

/-- The explicit classical prime-two polynomial over the integral j-coordinate. -/
def phiTwo : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 3 + Polynomial.C phiTwoC2 * Polynomial.X ^ 2
    + Polynomial.C phiTwoC1 * Polynomial.X + Polynomial.C phiTwoC0

/-- Specialization of the integral j-coordinate of a bivariate polynomial. -/
def fibrePoly {k : Type*} [Field k] (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

theorem fibrePoly_phiTwo_eq {K : Type*} [Field K] (a : K) :
    fibrePoly phiTwo a
      = X ^ 3 + C (-a ^ 2 + 1488 * a - 162000) * X ^ 2
          + C (1488 * a ^ 2 + 40773375 * a + 8748000000) * X
          + C (a ^ 3 - 162000 * a ^ 2 + 8748000000 * a - 157464000000000) := by
  simp only [fibrePoly, phiTwo, phiTwoC2, phiTwoC1, phiTwoC0, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_eval₂RingHom,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_neg, eval₂_ofNat]

theorem cubic_expand {K : Type*} [Field K] (u v w : K) :
    (X - C u) * (X - C v) * (X - C w)
      = X ^ 3 + C (-(u + v + w)) * X ^ 2 + C (u * v + u * w + v * w) * X + C (-(u * v * w)) := by
  simp only [map_neg, map_add, map_mul]
  ring


end
end Dubon2026.SourcePrimeTwoPolynomial
