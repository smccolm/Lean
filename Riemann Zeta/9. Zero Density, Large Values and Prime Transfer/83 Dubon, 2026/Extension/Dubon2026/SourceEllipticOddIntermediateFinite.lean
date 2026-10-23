import Dubon2026.SourceEllipticOddIntermediateRing

/-! Finiteness and the Dedekind property of the actual common ring used by
the odd quotient point norm. The already proved finite separable extension
allows direct use of pinned Mathlib integral-closure results. Algebraic closure
is used precisely for the proved coordinate-ring normality, matching the
odd-prime quotient-product source contract (DUB-17/18). -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd quotient coordinate ring is Dedekind over the algebraically closed base. -/
theorem isDedekindDomain_oddCoordinate (hQ : addOrderOf Q = 2 * n + 1) :
    IsDedekindDomain (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing := by
  letI := odd_quotient_isElliptic W Q hQ
  exact isDedekindDomain_of_isAlgClosed'

/-- The actual common integral closure is finite over the actual quotient coordinate ring. -/
theorem moduleFinite_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddIntermediateAlgebra W hQ
    Module.Finite (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing (oddIntermediateRing W hQ) := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddQuotientAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := oddCoordinate_field_scalarTower W hQ
  letI := oddIntermediate_scalarTower W hQ
  letI := isIntegralClosure_oddIntermediateRing W hQ
  letI := finiteDimensional_oddQuotient W hQ
  letI := isSeparable_oddQuotient W hQ
  letI := isDedekindDomain_oddCoordinate W hQ
  exact IsIntegralClosure.finite
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField
    W.toAffine.FunctionField (oddIntermediateRing W hQ)

/-- The actual common ring is Dedekind, with the original source and target embeddings fixed. -/
theorem isDedekindDomain_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    IsDedekindDomain (oddIntermediateRing W hQ) := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddQuotientAlgebra W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := oddCoordinate_field_scalarTower W hQ
  letI := oddIntermediate_scalarTower W hQ
  letI := isIntegralClosure_oddIntermediateRing W hQ
  letI := finiteDimensional_oddQuotient W hQ
  letI := isSeparable_oddQuotient W hQ
  letI := isDedekindDomain_oddCoordinate W hQ
  exact IsIntegralClosure.isDedekindDomain
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField
    W.toAffine.FunctionField (oddIntermediateRing W hQ)

omit [IsAlgClosed F] in
/-- The actual common-ring target action is torsion free. -/
theorem isTorsionFree_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddIntermediateAlgebra W hQ
    Module.IsTorsionFree (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing (oddIntermediateRing W hQ) := by
  letI := oddIntermediateAlgebra W hQ
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr (oddTargetToIntermediate_injective W hQ)

end Dubon2026.SourceEllipticFunctionField
