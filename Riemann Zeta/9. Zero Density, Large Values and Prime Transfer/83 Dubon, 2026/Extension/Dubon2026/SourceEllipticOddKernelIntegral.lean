import Dubon2026.SourceEllipticOddCoordinateIntegral

/-! Integrality of each actual odd-kernel denominator. Multiplying the inverse
kernel polynomial by the complementary product avoids a separate pole argument.
This serves the explicit y-coordinate and actual odd quotient map for DUB-17/18. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve F} {Q : W.toAffine.Point} {n : ℕ}

/-- Every linear kernel denominator has integral inverse over the actual quotient x-ring. -/
theorem isIntegral_odd_kernel_factor_inverse (hQ : addOrderOf Q = 2 * n + 1)
    {P : F × F} (hPmem : P ∈ oddOrderSummingSet W Q n) :
    IsIntegral (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)})
      (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ := by
  let S := oddOrderSummingSet W Q n
  let p : F[X] := ∏ R ∈ S.erase P, (X - C R.1)
  have hp : (X - C P.1) * p = hP S Prod.fst :=
    Finset.mul_prod_erase S (fun R : F × F => (X - C R.1 : F[X])) hPmem
  have hm := congrArg (aeval (genericX W.toAffine)) hp
  simp only [map_mul, map_sub, aeval_X, aeval_C] at hm
  have hd := generic_kernel_denominator_ne_zero W S
  have hf : genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact hd hm.symm
  have he : (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ =
      aeval (genericX W.toAffine) p * (aeval (genericX W.toAffine) (hP S Prod.fst))⁻¹ := by
    apply mul_left_cancel₀ hf
    rw [mul_inv_cancel₀ hf, ← mul_assoc, hm, mul_inv_cancel₀ hd]
  rw [he]
  exact (isIntegral_aeval_over_subalgebra _
    (isIntegral_genericX_over_genericVeluX W S) p).mul (isIntegral_odd_kernel_inverse hQ)

end Dubon2026.SourceEllipticVelu
