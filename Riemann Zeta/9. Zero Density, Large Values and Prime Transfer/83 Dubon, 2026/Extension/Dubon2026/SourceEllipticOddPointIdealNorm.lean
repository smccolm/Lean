import Dubon2026.SourceEllipticOddPointResidueDegree
import Dubon2026.SourceEllipticOddIntermediateGalois

/-! The actual relative norm of the extended affine point ideal is exactly
the ideal of the literal quotient coordinates. The intermediate ring,
Galois extension, maximal ideals and residue degree are all derived from
the actual odd quotient. This removes the ideal-norm assumption from the
comparison with the additive point map on DUB-17/18. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

attribute [local instance] FractionRing.liftAlgebra

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
variable {x y : F} (h : W.toAffine.Equation x y)

/-- The relative ideal norm of the actual common-ring point prime is the literal quotient point ideal. -/
theorem relNorm_oddIntermediateEval_ker (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    letI := oddIntermediateAlgebra W hQ
    letI := isTorsionFree_oddIntermediateRing W hQ
    letI := moduleFinite_oddIntermediateRing W hQ
    letI := isDedekindDomain_oddCoordinate W hQ
    letI := isDedekindDomain_oddIntermediateRing W hQ
    Ideal.relNorm (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
      (RingHom.ker (oddIntermediateEval W h hQ hd)) =
      CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
        (veluAffineX W (oddOrderSummingSet W Q n) x)
        (C (veluAffineY W (oddOrderSummingSet W Q n) x y)) := by
  letI := oddIntermediateAlgebra W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  letI := moduleFinite_oddIntermediateRing W hQ
  letI := isDedekindDomain_oddCoordinate W hQ
  letI := isDedekindDomain_oddIntermediateRing W hQ
  letI := isGalois_oddIntermediateFractionRing W hQ
  let A := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
  let P := RingHom.ker (oddIntermediateEval W h hQ hd)
  let p := CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
    (veluAffineX W (oddOrderSummingSet W Q n) x) (C (veluAffineY W (oddOrderSummingSet W Q n) x y))
  letI : P.IsMaximal := isMaximal_oddIntermediateEval_ker W h hQ hd
  letI : p.IsMaximal := isMaximal_oddQuotientPointIdeal W h hQ hd
  letI : P.LiesOver p := ⟨(comap_oddIntermediateEval_ker_target W h hQ hd).symm⟩
  change Ideal.relNorm A P = p
  rw [Ideal.relNorm_eq_pow_of_isPrime_isGalois P p, inertiaDeg_oddPointIdeal W h hQ hd, pow_one]

include h in
/-- Extend the actual source point ideal and norm it down: the result is the actual literal quotient point ideal. -/
theorem relNorm_map_XYIdeal_odd (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    letI := oddIntermediateAlgebra W hQ
    letI := isTorsionFree_oddIntermediateRing W hQ
    letI := moduleFinite_oddIntermediateRing W hQ
    letI := isDedekindDomain_oddCoordinate W hQ
    letI := isDedekindDomain_oddIntermediateRing W hQ
    Ideal.relNorm (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
      ((CoordinateRing.XYIdeal W.toAffine x (C y)).map (oddSourceToIntermediate W hQ)) =
      CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
        (veluAffineX W (oddOrderSummingSet W Q n) x)
        (C (veluAffineY W (oddOrderSummingSet W Q n) x y)) := by
  letI := oddIntermediateAlgebra W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  letI := moduleFinite_oddIntermediateRing W hQ
  letI := isDedekindDomain_oddCoordinate W hQ
  letI := isDedekindDomain_oddIntermediateRing W hQ
  rw [map_XYIdeal_eq_oddIntermediateEval_ker W h hQ hd, relNorm_oddIntermediateEval_ker W h hQ hd]

end Dubon2026.SourceEllipticFunctionField
