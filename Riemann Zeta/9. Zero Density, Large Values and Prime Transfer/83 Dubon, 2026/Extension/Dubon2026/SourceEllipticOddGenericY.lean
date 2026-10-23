import Dubon2026.SourceEllipticOddKernelIntegral

/-! The literal Velu y-coordinate at the actual generic point, and its
integrality over the polynomial ring in the odd quotient x-coordinate.
The coordinate formula is adapted from anthropics/fermats-last-theorem,
Definitions/Def_WeierstrassCurve_VeluPointMap.lean, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
This is a prerequisite for the actual odd quotient equation, not that equation. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The explicit finite Velu y-coordinate sum in the original elliptic function field. -/
noncomputable def genericVeluY : W.toAffine.FunctionField :=
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  y - ∑ P ∈ S, (c (veluU W P.1 P.2) * (2 * y + c W.a₁ * x + c W.a₃) /
      (x - c P.1) ^ 3 + c (veluT W P.1 P.2) * (c W.a₁ * (x - c P.1) + y - c P.2) /
      (x - c P.1) ^ 2 +
      c (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) /
      (x - c P.1) ^ 2)

variable {W} {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd quotient y-sum is integral over its actual polynomial x-ring. -/
theorem isIntegral_genericVeluY (hQ : addOrderOf Q = 2 * n + 1) :
    IsIntegral (Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)})
      (genericVeluY W (oddOrderSummingSet W Q n)) := by
  let A := Algebra.adjoin F {genericVeluX W (oddOrderSummingSet W Q n)}
  have hx := isIntegral_genericX_over_genericVeluX W (oddOrderSummingSet W Q n)
  have hy := isIntegral_genericY_over_genericVeluX W (oddOrderSummingSet W Q n)
  have hc (a : F) : IsIntegral A (algebraMap F W.toAffine.FunctionField a) := by
    simpa only [aeval_C] using isIntegral_aeval_over_subalgebra A hx (C a)
  have h2 : IsIntegral A (2 : W.toAffine.FunctionField) := by
    simpa only [map_ofNat] using hc 2
  unfold genericVeluY
  refine hy.sub (IsIntegral.sum _ fun P hP => ?_)
  simp only [div_eq_mul_inv, ← inv_pow]
  have hd := isIntegral_odd_kernel_factor_inverse hQ hP
  exact (((hc _).mul (((h2.mul hy).add ((hc W.a₁).mul hx)).add (hc W.a₃))).mul
    (hd.pow 3)).add (((hc _).mul (((hc W.a₁).mul (hx.sub (hc P.1))).add hy |>.sub
      (hc P.2))).mul (hd.pow 2)) |>.add ((hc _).mul (hd.pow 2))

end Dubon2026.SourceEllipticVelu
