import Dubon2026.SourceEllipticOddRationalDegree
import Dubon2026.SourceEllipticFunctionDegree

/-! The rational quotient coordinate is identified inside the actual elliptic function field.
This ensures the proved rational-function degree concerns the explicit generic
coordinate used by the pending odd quotient field map (DUB-17/18), rather than
an independently supplied parameter. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The actual inclusion of rational functions of x into the elliptic function field. -/
noncomputable def rationalCoordinateHom : RatFunc F →ₐ[F] W.toAffine.FunctionField :=
  IsFractionRing.liftAlgHom
    (g := IsScalarTower.toAlgHom F F[X] W.toAffine.FunctionField)
    (polynomial_algebraMap_injective W.toAffine)

/-- On polynomials, the rational-coordinate inclusion is evaluation at the generic coordinate. -/
theorem rationalCoordinateHom_polynomial (p : F[X]) :
    rationalCoordinateHom W (algebraMap F[X] (RatFunc F) p) =
      aeval (genericX W.toAffine) p := by
  simp [rationalCoordinateHom, IsFractionRing.liftAlgHom_apply,
    algebraMap_eq_aeval_genericX]

variable [DecidableEq F] (S : Finset (F × F))

/-- The rational quotient function maps to the original finite Velu sum at the generic point. -/
theorem rationalCoordinateHom_ratFuncVeluX :
    rationalCoordinateHom W (ratFuncVeluX W S) = genericVeluX W S := by
  rw [ratFuncVeluX, map_div₀, rationalCoordinateHom_polynomial,
    rationalCoordinateHom_polynomial, map_pow, genericVeluX_eq_ratio]

end Dubon2026.SourceEllipticVelu
