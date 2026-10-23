import Dubon2026.SourceEllipticOddExtensionStructure

/-! The actual coordinate-ring action underlying the proved odd quotient
field embedding. The scalar towers and coordinate images are fixed by the
literal pullback, so the intermediate integral closure used for the point map
cannot vary with an independently supplied algebra structure (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual quotient coordinate pullback is the restriction of the proved field pullback. -/
noncomputable def oddCoordinatePullback (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing →ₐ[F] W.toAffine.FunctionField :=
  (oddQuotientPullback W hQ).comp (IsScalarTower.toAlgHom F
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField)

/-- The actual quotient coordinate-ring action in the original function field. -/
noncomputable abbrev oddCoordinateAlgebra (hQ : addOrderOf Q = 2 * n + 1) :
    Algebra (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField :=
  (oddCoordinatePullback W hQ).toRingHom.toAlgebra

/-- The coefficient field, quotient coordinate ring and original field form the actual scalar tower. -/
theorem oddCoordinate_scalarTower (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    IsScalarTower F (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField := by
  letI := oddCoordinateAlgebra W hQ
  exact IsScalarTower.of_algebraMap_eq fun a => ((oddCoordinatePullback W hQ).commutes a).symm

/-- The coordinate and curve-field actions agree on the actual quotient coordinate ring. -/
theorem oddCoordinate_field_scalarTower (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    letI := oddQuotientAlgebra W hQ
    IsScalarTower (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
      (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddQuotientAlgebra W hQ
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual coordinate pullback is injective. -/
theorem oddCoordinatePullback_injective (hQ : addOrderOf Q = 2 * n + 1) :
    Function.Injective (oddCoordinatePullback W hQ) :=
  (oddQuotientPullback_injective W hQ).comp (IsFractionRing.injective _ _)

/-- The quotient affine x-coordinate pulls back to the literal finite x-sum. -/
theorem oddCoordinatePullback_X (hQ : addOrderOf Q = 2 * n + 1) :
    oddCoordinatePullback W hQ
      (AdjoinRoot.of (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial X) =
      genericVeluX W (oddOrderSummingSet W Q n) := oddQuotientPullback_genericX W hQ

/-- The quotient affine y-coordinate pulls back to the literal finite y-sum. -/
theorem oddCoordinatePullback_Y (hQ : addOrderOf Q = 2 * n + 1) :
    oddCoordinatePullback W hQ
      (AdjoinRoot.root (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial) =
      genericVeluY W (oddOrderSummingSet W Q n) := oddQuotientPullback_genericY W hQ

end Dubon2026.SourceEllipticFunctionField
