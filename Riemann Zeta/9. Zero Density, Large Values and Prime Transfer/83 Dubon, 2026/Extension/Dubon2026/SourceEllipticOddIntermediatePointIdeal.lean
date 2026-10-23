import Dubon2026.SourceEllipticOddIntermediateEvaluation

/-! The original point ideal extended into the actual common integral
closure, its maximality, and its contraction to the literal quotient point.
These are the concrete prime ideals in the norm computation for the odd
point map required by DUB-17/18. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
variable {x y : F} (h : W.toAffine.Equation x y)

/-- The actual source point ideal extends to the evaluation kernel in the actual common ring. -/
theorem map_XYIdeal_eq_oddIntermediateEval_ker (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (CoordinateRing.XYIdeal W.toAffine x (C y)).map (oddSourceToIntermediate W hQ) =
      RingHom.ker (oddIntermediateEval W h hQ hd) := by
  letI := oddIntermediateSourceAlgebra W hQ
  letI := isLocalization_oddIntermediateRing W hQ
  have hc : (RingHom.ker (oddIntermediateEval W h hQ hd)).under W.toAffine.CoordinateRing =
      CoordinateRing.XYIdeal W.toAffine x (C y) := by
    ext z
    change oddIntermediateEval W h hQ hd (oddSourceToIntermediate W hQ z) = 0 ↔ _
    rw [oddIntermediateEval_source]
    change z ∈ RingHom.ker (evalAlgHom (W := W.toAffine) (A := F) h).toRingHom ↔ _
    rw [ker_evalAlgHom_eq_XYIdeal]
  change (CoordinateRing.XYIdeal W.toAffine x (C y)).map
    (algebraMap W.toAffine.CoordinateRing (oddIntermediateRing W hQ)) = _
  rw [← hc]
  exact IsLocalization.map_under
    (Submonoid.powers (kernelCoordinate W (oddOrderSummingSet W Q n))) _ _

/-- The actual common-ring point ideal is maximal. -/
theorem isMaximal_oddIntermediateEval_ker (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (RingHom.ker (oddIntermediateEval W h hQ hd)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (oddIntermediateEval_surjective W h hQ hd)

/-- The actual common-ring point ideal contracts to the literal quotient point ideal. -/
theorem comap_oddIntermediateEval_ker_target (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (RingHom.ker (oddIntermediateEval W h hQ hd)).comap (oddTargetToIntermediate W hQ) =
      CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
        (veluAffineX W (oddOrderSummingSet W Q n) x)
        (C (veluAffineY W (oddOrderSummingSet W Q n) x y)) := by
  have he : (oddIntermediateEval W h hQ hd).comp (oddTargetToIntermediate W hQ) =
      (oddAffineEval W h hQ hd).toRingHom := RingHom.ext (oddIntermediateEval_target W h hQ hd)
  change RingHom.ker ((oddIntermediateEval W h hQ hd).comp (oddTargetToIntermediate W hQ)) = _
  rw [he, oddAffineEval_eq_evalAlgHom, ker_evalAlgHom_eq_XYIdeal]

omit [IsAlgClosed F] in
include h in
/-- The literal quotient point ideal is maximal because actual evaluation is onto the coefficient field. -/
theorem isMaximal_oddQuotientPointIdeal (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
      (veluAffineX W (oddOrderSummingSet W Q n) x)
      (C (veluAffineY W (oddOrderSummingSet W Q n) x y))).IsMaximal := by
  rw [← ker_evalAlgHom_eq_XYIdeal (odd_veluAffine_equation W h hQ hd)]
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  refine ⟨algebraMap F _ a, ?_⟩
  exact AlgHom.commutes _ a

end Dubon2026.SourceEllipticFunctionField
