import Dubon2026.SourceEllipticOddCoordinatePullback

/-! Every original affine coordinate function is integral over the actual
quotient coordinate ring. The earlier monic-polynomial proof over F[X_velu]
is transported through its actual inclusion. This supplies the source-ring
embedding into the intermediate integral closure for the norm point map,
without an assumed pointedness certificate (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- Integrality over the literal quotient polynomial ring implies integrality over the actual quotient coordinate ring. -/
theorem isIntegral_oddCoordinate_of_polynomial (hQ : addOrderOf Q = 2 * n + 1)
    {z : W.toAffine.FunctionField}
    (hz : IsIntegral (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)}) z) :
    letI := oddCoordinateAlgebra W hQ
    IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing z := by
  let A := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
  letI := oddCoordinateAlgebra W hQ
  letI := oddCoordinate_scalarTower W hQ
  have hx : IsIntegral A (genericVeluX W (oddOrderSummingSet W Q n)) := by
    rw [← oddCoordinatePullback_X W hQ]
    exact isIntegral_algebraMap
  have hle : Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)} ≤
      (integralClosure A W.toAffine.FunctionField).restrictScalars F := by
    apply Algebra.adjoin_le
    rintro _ (rfl : _ = _)
    exact hx
  exact isIntegral_of_integral_image (fun b => hle b.property) hz

/-- The original generic x-coordinate is integral over the actual quotient coordinate ring. -/
theorem isIntegral_genericX_oddCoordinate (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing (genericX W.toAffine) :=
  isIntegral_oddCoordinate_of_polynomial W hQ (isIntegral_genericX_over_genericVeluX W _)

/-- The original generic y-coordinate is integral over the actual quotient coordinate ring. -/
theorem isIntegral_genericY_oddCoordinate (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddCoordinateAlgebra W hQ
    IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing (genericY W.toAffine) :=
  isIntegral_oddCoordinate_of_polynomial W hQ (isIntegral_genericY_over_genericVeluX W _)

/-- Every original affine coordinate function lies in the actual intermediate integral closure. -/
theorem isIntegral_coordinate_oddCoordinate (hQ : addOrderOf Q = 2 * n + 1) (z : W.toAffine.CoordinateRing) :
    letI := oddCoordinateAlgebra W hQ
    IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField z) := by
  letI := oddCoordinateAlgebra W hQ
  letI := oddCoordinate_scalarTower W hQ
  let A := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq z
  have hp (f : F[X]) : IsIntegral A (aeval (genericX W.toAffine) f) := by
    have hi := isIntegral_aeval_over_subalgebra
      (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)})
      (isIntegral_genericX_over_genericVeluX W _) f
    exact isIntegral_oddCoordinate_of_polynomial W hQ hi
  have hpoly (f : F[X]) :
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine (C f)) =
        aeval (genericX W.toAffine) f := by
    rw [CoordinateRing.mk, AdjoinRoot.mk_C]
    exact (IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField f).symm.trans
      (algebraMap_eq_aeval_genericX W.toAffine f)
  simp only [CoordinateRing.smul, map_add, map_mul, mul_one, hpoly]
  change IsIntegral A (aeval (genericX W.toAffine) p + aeval (genericX W.toAffine) q * genericY W.toAffine)
  exact (hp p).add ((hp q).mul (isIntegral_genericY_oddCoordinate W hQ))

end Dubon2026.SourceEllipticFunctionField
