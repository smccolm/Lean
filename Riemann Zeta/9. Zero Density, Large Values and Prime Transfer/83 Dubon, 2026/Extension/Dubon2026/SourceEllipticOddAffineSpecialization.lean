import Dubon2026.SourceEllipticVeluAffineEvaluation

/-! Specialization of the actual quotient pullback at every affine point away
from the kernel. This derives the literal quotient equation at that point and
identifies the full coordinate-ring evaluation map, providing the target ideal
in the norm point-map comparison for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual coordinate pullback with its proved kernel-localization codomain. -/
noncomputable def oddKernelPullback (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing →ₐ[F]
      kernelLocalRing W (oddOrderSummingSet W Q n) :=
  (oddCoordinatePullback W hQ).codRestrict
    ((kernelLocalRing W (oddOrderSummingSet W Q n)).restrictScalars F)
    (oddCoordinatePullback_mem_kernelLocalRing W hQ)

/-- The localized quotient x-coordinate is the literal generic finite sum. -/
theorem oddKernelPullback_X (hQ : addOrderOf Q = 2 * n + 1) :
    oddKernelPullback W hQ
      (AdjoinRoot.of (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial X) =
      ⟨genericVeluX W (oddOrderSummingSet W Q n), genericVeluX_mem_kernelLocalRing W _⟩ :=
  Subtype.ext (oddCoordinatePullback_X W hQ)

/-- The localized quotient y-coordinate is the literal generic finite sum. -/
theorem oddKernelPullback_Y (hQ : addOrderOf Q = 2 * n + 1) :
    oddKernelPullback W hQ
      (AdjoinRoot.root (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial) =
      ⟨genericVeluY W (oddOrderSummingSet W Q n), genericVeluY_mem_kernelLocalRing W _⟩ :=
  Subtype.ext (oddCoordinatePullback_Y W hQ)

variable {x y : F} (h : W.toAffine.Equation x y)

/-- The actual quotient evaluation obtained by pullback and localized source evaluation. -/
noncomputable def oddAffineEval (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing →ₐ[F] F :=
  { (kernelLocalEval W _ h hd).comp (oddKernelPullback W hQ).toRingHom with
    commutes' a := by
      change kernelLocalEval W _ h hd (oddKernelPullback W hQ (algebraMap F _ a)) = _
      rw [AlgHom.commutes, kernelLocalEval_constant]
      rfl }

/-- The actual quotient evaluation sends x to the literal affine x-formula. -/
theorem oddAffineEval_X (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    oddAffineEval W h hQ hd
      (AdjoinRoot.of (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial X) =
      veluAffineX W (oddOrderSummingSet W Q n) x := by
  change kernelLocalEval W _ h hd (oddKernelPullback W hQ _) = _
  rw [oddKernelPullback_X, kernelLocalEval_genericVeluX]

/-- The actual quotient evaluation sends y to the literal affine y-formula. -/
theorem oddAffineEval_Y (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    oddAffineEval W h hQ hd
      (AdjoinRoot.root (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.polynomial) =
      veluAffineY W (oddOrderSummingSet W Q n) x y := by
  change kernelLocalEval W _ h hd (oddKernelPullback W hQ _) = _
  rw [oddKernelPullback_Y, kernelLocalEval_genericVeluY]

include h in
/-- The literal odd quotient formulas satisfy the actual quotient equation at every point off the kernel. -/
theorem odd_veluAffine_equation (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.Equation
      (veluAffineX W (oddOrderSummingSet W Q n) x)
      (veluAffineY W (oddOrderSummingSet W Q n) x y) := by
  have he := Dubon2026.SourceEllipticClassGroup.equation_of_algHom (oddAffineEval W h hQ hd)
  rwa [oddAffineEval_X, oddAffineEval_Y] at he

/-- Pullback followed by localized evaluation equals evaluation at the literal quotient coordinates. -/
theorem oddAffineEval_eq_evalAlgHom (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    oddAffineEval W h hQ hd = evalAlgHom
      (W := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine) (A := F)
      (odd_veluAffine_equation W h hQ hd) := by
  apply algHom_ext
  · rw [oddAffineEval_X, evalAlgHom_of_X]
  · rw [oddAffineEval_Y, evalAlgHom_root]

end Dubon2026.SourceEllipticFunctionField
