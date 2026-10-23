import Dubon2026.SourceEllipticOddSummingSet
import Dubon2026.SourceEllipticOddReindex
import Dubon2026.SourceEllipticFunctionGeneric

/-! Coordinate bridges for actual translated generic points. The pinned native
point-map and group law are reused; these formulas connect them to the existing
coordinate function used by the odd cyclic quotient. They serve the translation
invariance needed for the actual quotient equation on the DUB-17/18 chain. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F K L : Type*} [Field F] [Field K] [Field L]

/-- Coordinates of a nonzero point satisfy the actual nonsingularity condition. -/
theorem nonsingular_coordsOrZero {W : Affine F} {P : W.Point} (hP : P ≠ 0) :
    W.Nonsingular (coordsOrZero P).1 (coordsOrZero P).2 := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => exact h

/-- A nonzero point is recovered from its coordinates. -/
theorem some_coordsOrZero {W : Affine F} {P : W.Point} (hP : P ≠ 0) :
    Point.some (coordsOrZero P).1 (coordsOrZero P).2 (nonsingular_coordsOrZero hP) = P := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => rfl

/-- Actual point base change maps both coordinates by the given algebra homomorphism. -/
theorem coordsOrZero_point_map [DecidableEq K] [DecidableEq L] [Algebra F K] [Algebra F L]
    {W : Affine F} (f : K →ₐ[F] L) (P : (W⁄K).toAffine.Point) :
    coordsOrZero (Point.map (W' := W) f P) =
      Prod.map f f (coordsOrZero P) := by
  cases P with
  | zero =>
      change (0, 0) = (f 0, f 0)
      rw [map_zero]
  | some x y h => rfl

/-- The existing generic point has the actual generic coordinates. -/
theorem coordsOrZero_genericPoint (W : Affine F) [W.IsElliptic] :
    coordsOrZero (genericPoint W) = (genericX W, genericY W) := rfl

end Dubon2026.SourceEllipticFunctionField
