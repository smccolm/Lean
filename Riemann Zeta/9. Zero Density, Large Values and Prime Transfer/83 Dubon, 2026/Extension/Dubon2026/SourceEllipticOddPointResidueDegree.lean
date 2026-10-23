import Dubon2026.SourceEllipticOddIntermediatePointIdeal
import Mathlib.NumberTheory.RamificationInertia.Inertia

/-! The actual point-ideal extension has residue degree one. The quotient
algebra map is onto because the common-ring evaluation of any element can
already be represented by a coefficient-field constant in the target ring.
This is the exact exponent in the native Galois ideal-norm formula, needed
to identify the actual odd point norm (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

attribute [local instance] Ideal.Quotient.field

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
variable {x y : F} (h : W.toAffine.Equation x y)

/-- The actual prime over the literal quotient point has residue degree exactly one. -/
theorem inertiaDeg_oddPointIdeal (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    letI := oddIntermediateAlgebra W hQ
    (CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
      (veluAffineX W (oddOrderSummingSet W Q n) x)
      (C (veluAffineY W (oddOrderSummingSet W Q n) x y))).inertiaDeg
        (RingHom.ker (oddIntermediateEval W h hQ hd)) = 1 := by
  letI := oddIntermediateAlgebra W hQ
  let A := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
  let B := oddIntermediateRing W hQ
  let P : Ideal B := RingHom.ker (oddIntermediateEval W h hQ hd)
  let p : Ideal A := CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
    (veluAffineX W (oddOrderSummingSet W Q n) x) (C (veluAffineY W (oddOrderSummingSet W Q n) x y))
  letI : P.IsMaximal := isMaximal_oddIntermediateEval_ker W h hQ hd
  letI : p.IsMaximal := isMaximal_oddQuotientPointIdeal W h hQ hd
  letI : P.LiesOver p := ⟨(comap_oddIntermediateEval_ker_target W h hQ hd).symm⟩
  change p.inertiaDeg P = 1
  rw [Ideal.inertiaDeg_algebraMap]
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨(algebraMap (A ⧸ p) (B ⧸ P)).injective, ?_⟩
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨Ideal.Quotient.mk p (algebraMap F A (oddIntermediateEval W h hQ hd b)), ?_⟩
  change Ideal.Quotient.mk P (oddTargetToIntermediate W hQ
    (algebraMap F A (oddIntermediateEval W h hQ hd b))) = Ideal.Quotient.mk P b
  apply Ideal.Quotient.eq.mpr
  change oddIntermediateEval W h hQ hd
    (oddTargetToIntermediate W hQ (algebraMap F A (oddIntermediateEval W h hQ hd b)) - b) = 0
  rw [map_sub, oddIntermediateEval_target, AlgHom.commutes]
  exact sub_self _

end Dubon2026.SourceEllipticFunctionField
