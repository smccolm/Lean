import Dubon2026.SourceEllipticOddCoordinateIntegralImage
import Dubon2026.SourceEllipticOddQuotient
import Dubon2026.SourceEllipticClassNormal
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! The actual common ring for the odd quotient's ideal norm: the integral
closure of its coordinate ring in the original function field. The source
coordinate-ring embedding is supplied by the proved coordinate integrality.
The actual finite separable extension and proved target normality supply
finiteness and the Dedekind property using pinned Mathlib (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual integral closure through the literal odd coordinate pullback, as a subring. -/
noncomputable def oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) : Subring W.toAffine.FunctionField :=
  letI := oddCoordinateAlgebra W hQ
  (integralClosure (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField).toSubring

/-- Membership means integrality over the actual quotient coordinate ring. -/
theorem mem_oddIntermediateRing_iff (hQ : addOrderOf Q = 2 * n + 1) (z : W.toAffine.FunctionField) :
    z ∈ oddIntermediateRing W hQ ↔
      letI := oddCoordinateAlgebra W hQ
      IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing z := Iff.rfl

/-- The source coordinate ring embeds into the actual common integral closure. -/
noncomputable def oddSourceToIntermediate (hQ : addOrderOf Q = 2 * n + 1) :
    W.toAffine.CoordinateRing →+* oddIntermediateRing W hQ :=
  (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).codRestrict
    (oddIntermediateRing W hQ) (isIntegral_coordinate_oddCoordinate W hQ)

/-- The source embedding keeps each actual affine function unchanged in the original field. -/
theorem oddSourceToIntermediate_coe (hQ : addOrderOf Q = 2 * n + 1) (z : W.toAffine.CoordinateRing) :
    (oddSourceToIntermediate W hQ z : W.toAffine.FunctionField) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField z := rfl

/-- The actual source embedding into the common ring is injective. -/
theorem oddSourceToIntermediate_injective (hQ : addOrderOf Q = 2 * n + 1) :
    Function.Injective (oddSourceToIntermediate W hQ) := by
  intro a b h
  exact IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField (congrArg Subtype.val h)

/-- The target coordinate ring embeds through the literal pullback into its actual integral closure. -/
noncomputable def oddTargetToIntermediate (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing →+* oddIntermediateRing W hQ := by
  letI := oddCoordinateAlgebra W hQ
  exact (oddCoordinatePullback W hQ).toRingHom.codRestrict (oddIntermediateRing W hQ)
    fun _ => isIntegral_algebraMap

/-- The target embedding agrees with the actual quotient pullback in the original field. -/
theorem oddTargetToIntermediate_coe (hQ : addOrderOf Q = 2 * n + 1)
    (z : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing) :
    (oddTargetToIntermediate W hQ z : W.toAffine.FunctionField) = oddCoordinatePullback W hQ z := rfl

/-- The actual target embedding into the common ring is injective. -/
theorem oddTargetToIntermediate_injective (hQ : addOrderOf Q = 2 * n + 1) :
    Function.Injective (oddTargetToIntermediate W hQ) := by
  intro a b h
  exact oddCoordinatePullback_injective W hQ (congrArg Subtype.val h)

/-- The target action on the common ring is fixed by its actual pullback. -/
noncomputable abbrev oddIntermediateAlgebra (hQ : addOrderOf Q = 2 * n + 1) :
    Algebra (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing (oddIntermediateRing W hQ) :=
  (oddTargetToIntermediate W hQ).toAlgebra

/-- The common ring and original function field use compatible target actions. -/
theorem oddIntermediate_scalarTower (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    letI := oddIntermediateAlgebra W hQ
    IsScalarTower (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
      (oddIntermediateRing W hQ) W.toAffine.FunctionField := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The specified common ring is the actual integral closure, with its actual target action. -/
theorem isIntegralClosure_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    letI := oddIntermediateAlgebra W hQ
    IsIntegralClosure (oddIntermediateRing W hQ)
      (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  change IsIntegralClosure
    (integralClosure (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField)
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing W.toAffine.FunctionField
  infer_instance

end Dubon2026.SourceEllipticFunctionField
