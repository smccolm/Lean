import Dubon2026.SourceEllipticIntegralCoordinates

/-! Integrality of coordinates of an actual Weierstrass point. This is used
to descend a putatively algebraic translate of the generic point, proving that
translation induces a function-field map on the odd quotient dependency chain.
Adapted from TauCeti/AlgebraicGeometry/EllipticCurve/Integrality.lean,
Apache-2.0, bfcff79b60964ba7bdb78b952828313686c327ba. Only the coordinate
integrality argument is needed; denominator and torsion generalizations are omitted. -/

open Polynomial WeierstrassCurve

namespace Dubon2026.SourceEllipticFunctionField

/-- A monic quadratic with integral coefficients has integral roots. -/
theorem isIntegral_quadratic_root {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    {b c y : L} (hb : IsIntegral R b) (hc : IsIntegral R c)
    (hy : y ^ 2 + b * y + c = 0) : IsIntegral R y := by
  let B := integralClosure R L
  let b' : B := ⟨b, hb⟩
  let c' : B := ⟨c, hc⟩
  have hi : IsIntegral B y := by
    refine ⟨X ^ 2 + (C b' * X + C c'), monic_X_pow_add ?_, ?_⟩
    · compute_degree; norm_num
    · simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, add_assoc] using hy
  exact isIntegral_trans (R := R) y hi

/-- Integrality of x forces that of y by the actual monic Weierstrass equation. -/
theorem isIntegral_y_of_equation {F L : Type*} [Field F] [Field L] [Algebra F L]
    (W : WeierstrassCurve F) {x y : L}
    (h : (W⁄L).toAffine.Equation x y) (hx : IsIntegral F x) : IsIntegral F y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  refine isIntegral_quadratic_root
    (b := algebraMap F L W.a₁ * x + algebraMap F L W.a₃)
    (c := -(x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x + algebraMap F L W.a₆))
    ((isIntegral_algebraMap.mul hx).add isIntegral_algebraMap)
    ((((hx.pow 3).add (isIntegral_algebraMap.mul (hx.pow 2))).add
      (isIntegral_algebraMap.mul hx)).add isIntegral_algebraMap).neg ?_
  linear_combination h

end Dubon2026.SourceEllipticFunctionField
