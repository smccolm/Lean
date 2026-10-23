import Dubon2026.SourceEllipticOddRationalDegree
import Dubon2026.SourceEllipticIntegralCoordinates

/-! The actual elliptic coordinates are integral over the polynomial ring in
the odd quotient x-coordinate, and the kernel denominator becomes integrally
invertible. These are concrete algebraic inputs to the quotient equation and
intermediate coordinate ring needed for the odd point map (DUB-17/18). -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The original generic x-coordinate is integral over the actual polynomial quotient ring. -/
theorem isIntegral_genericX_over_genericVeluX :
    IsIntegral (Algebra.adjoin F {genericVeluX W S}) (genericX W.toAffine) := by
  rw [genericVeluX_eq_ratio]
  have hd : (hP S Prod.fst ^ 2).natDegree <
      (AP S Prod.fst (fun P => veluT W P.1 P.2) (fun P => veluU W P.1 P.2)).natDegree := by
    rw [(hP_monic _ _).natDegree_pow, natDegree_hP, natDegree_AP]
    omega
  have hq : aeval (genericX W.toAffine) (hP S Prod.fst ^ 2) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero 2 (generic_kernel_denominator_ne_zero W S)
  rw [← map_pow]
  exact isIntegral_coordinate_over_ratio (AP_monic S Prod.fst _ _) hd hq

/-- The original generic y-coordinate is integral over the same actual quotient ring. -/
theorem isIntegral_genericY_over_genericVeluX :
    IsIntegral (Algebra.adjoin F {genericVeluX W S}) (genericY W.toAffine) :=
  isIntegral_genericY_of_genericX W.toAffine _ (isIntegral_genericX_over_genericVeluX W S)

variable {W S} {Q : W.toAffine.Point} {n : ℕ}

/-- For the actual odd half-orbit, the inverse squared kernel denominator is integral. -/
theorem isIntegral_odd_kernel_square_inverse (hQ : addOrderOf Q = 2 * n + 1) :
    IsIntegral (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)})
      (aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst) ^ 2)⁻¹ := by
  rw [genericVeluX_eq_ratio]
  have hd : (hP (oddOrderSummingSet W Q n) Prod.fst ^ 2).natDegree <
      (AP (oddOrderSummingSet W Q n) Prod.fst (fun P => veluT W P.1 P.2)
        (fun P => veluU W P.1 P.2)).natDegree := by
    rw [odd_generic_denominator_degree hQ, odd_generic_numerator_degree hQ]
    omega
  have hq : aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst ^ 2) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero 2 (generic_kernel_denominator_ne_zero W _)
  rw [← map_pow]
  exact isIntegral_inverse_denominator_over_ratio
    (AP_monic _ Prod.fst _ _) hd hq (isCoprime_odd_generic hQ)

/-- The kernel denominator itself has integral inverse over the actual odd quotient ring. -/
theorem isIntegral_odd_kernel_inverse (hQ : addOrderOf Q = 2 * n + 1) :
    IsIntegral (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)})
      (aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst))⁻¹ := by
  have hh := isIntegral_aeval_over_subalgebra _
    (isIntegral_genericX_over_genericVeluX W (oddOrderSummingSet W Q n))
    (hP (oddOrderSummingSet W Q n) Prod.fst)
  have he : (aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst))⁻¹ =
      aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst) *
        (aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst) ^ 2)⁻¹ := by
    field_simp [generic_kernel_denominator_ne_zero W (oddOrderSummingSet W Q n)]
  rw [he]
  exact hh.mul (isIntegral_odd_kernel_square_inverse hQ)

end Dubon2026.SourceEllipticVelu
