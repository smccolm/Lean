import Dubon2026.SourceEllipticVeluLeadingCoefficient
import Dubon2026.SourceEllipticOddQuadraticRelation

/-! The actual odd Velu coordinates have a polynomial relation of the exact
Weierstrass degree shape. Its existence comes from the actual fixed field and
integrality; the degree and leading coefficient come from the proved literal
coordinate pole orders. No relation or pole-order premise is supplied here.
Matching the remaining coefficients with the explicit quotient is still needed
for the quotient map on the DUB-17/18 source dependency chain. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- Actual odd Velu coordinates satisfy a monic quadratic with the exact Weierstrass degree shape. -/
theorem exists_odd_genericVelu_relation_shape (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ p q : F[X],
      (genericVeluY W (oddOrderSummingSet W Q n) ^ 2 +
        aeval (genericVeluX W (oddOrderSummingSet W Q n)) p *
          genericVeluY W (oddOrderSummingSet W Q n) +
        aeval (genericVeluX W (oddOrderSummingSet W Q n)) q = 0) ∧
      p.natDegree ≤ 1 ∧ q.natDegree = 3 ∧ q.coeff 3 = -1 := by
  obtain ⟨p, q, h⟩ := exists_odd_genericVelu_quadratic_relation W hQ
  exact ⟨p, q, h, velu_relation_linear_degree_le h,
    (velu_relation_cubic_and_linear_value h).1, velu_relation_cubic_coeff h⟩

end Dubon2026.SourceEllipticFunctionField
