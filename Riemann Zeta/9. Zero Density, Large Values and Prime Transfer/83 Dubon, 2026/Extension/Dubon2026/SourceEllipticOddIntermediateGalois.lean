import Dubon2026.SourceEllipticOddIntermediateEvaluation
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! The actual common ring has the original function field as its fraction
field, and its extension over the quotient coordinate ring is Galois on
fraction fields. Native fraction-field equivalences preserve the proved
pullback action. This discharges the Galois input to the prime-ideal norm
formula without assuming a perfect function field in positive characteristic.
It serves the exact odd point-map comparison on DUB-17/18. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

attribute [local instance] FractionRing.liftAlgebra

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The fraction field of the actual common integral closure is the original elliptic function field. -/
theorem isFractionRing_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    IsFractionRing (oddIntermediateRing W hQ) W.toAffine.FunctionField := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddQuotientAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := oddCoordinate_field_scalarTower W hQ
  letI := oddIntermediate_scalarTower W hQ
  letI := isIntegralClosure_oddIntermediateRing W hQ
  letI := finiteDimensional_oddQuotient W hQ
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField
    W.toAffine.FunctionField (oddIntermediateRing W hQ)

/-- The canonical fraction-ring extension used by the ideal norm is the proved actual Galois extension. -/
theorem isGalois_oddIntermediateFractionRing (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddIntermediateAlgebra W hQ
    letI := isTorsionFree_oddIntermediateRing W hQ
    IsGalois (FractionRing (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing)
      (FractionRing (oddIntermediateRing W hQ)) := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddQuotientAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  letI := oddCoordinate_field_scalarTower W hQ
  letI := oddIntermediate_scalarTower W hQ
  letI := isFractionRing_oddIntermediateRing W hQ
  letI := finiteDimensional_oddQuotient W hQ
  letI := isGalois_oddQuotient W hQ
  let A := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
  let B := oddIntermediateRing W hQ
  let e : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField ≃ₐ[A] FractionRing A :=
    (FractionRing.algEquiv A _).symm
  let f : W.toAffine.FunctionField ≃ₐ[B] FractionRing B := (FractionRing.algEquiv B _).symm
  exact IsGalois.of_equiv_equiv (f := e.toRingEquiv) (g := f.toRingEquiv)
    (RingHom.ext fun z => IsFractionRing.algEquiv_commutes e f z)

end Dubon2026.SourceEllipticFunctionField
