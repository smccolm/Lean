import Dubon2026.SourceEllipticKernelLocalEvaluation

/-! Evaluation of the actual localized generic coordinates and inverse kernel
factors. These identities specialize the literal quotient formulas at affine
points away from the kernel, for the actual norm point map (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))
variable {x y : F} (h : W.toAffine.Equation x y) (hd : (hP S Prod.fst).eval x ≠ 0)

/-- Localized evaluation sends generic x to the actual affine x-coordinate. -/
theorem kernelLocalEval_genericX :
    kernelLocalEval W S h hd
      ⟨genericX W.toAffine, by simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X⟩ = x := by
  change kernelLocalEval W S h hd (algebraMap W.toAffine.CoordinateRing (kernelLocalRing W S)
    (CoordinateRing.mk W.toAffine (C X))) = x
  rw [kernelLocalEval_algebraMap]
  exact evalAlgHom_of_X (W := W.toAffine) (A := F) h

/-- Localized evaluation sends generic y to the actual affine y-coordinate. -/
theorem kernelLocalEval_genericY :
    kernelLocalEval W S h hd ⟨genericY W.toAffine, genericY_mem_kernelLocalRing W S⟩ = y := by
  change kernelLocalEval W S h hd (algebraMap W.toAffine.CoordinateRing (kernelLocalRing W S)
    (CoordinateRing.mk W.toAffine X)) = y
  rw [kernelLocalEval_algebraMap]
  exact evalAlgHom_root (W := W.toAffine) (A := F) h

/-- The evaluation of each actual inverse kernel factor is the inverse affine denominator. -/
theorem kernelLocalEval_inverse_factor {P : F × F} (hPmem : P ∈ S) :
    kernelLocalEval W S h hd
      ⟨(genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹,
        inverse_kernel_factor_mem_local W S hPmem⟩ = (x - P.1)⁻¹ := by
  let T := kernelLocalRing W S
  let X : T := ⟨genericX W.toAffine, by simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X⟩
  let u : T := ⟨(genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹,
    inverse_kernel_factor_mem_local W S hPmem⟩
  have hx : genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1 ≠ 0 :=
    sub_ne_zero.mpr (genericX_ne_constant W.toAffine P.1)
  have he : (X - algebraMap F T P.1) * u = 1 := by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx
  have hm := congrArg (kernelLocalEval W S h hd) he
  rw [map_mul, map_sub, map_one, kernelLocalEval_constant] at hm
  change (kernelLocalEval W S h hd X - P.1) * kernelLocalEval W S h hd u = 1 at hm
  rw [kernelLocalEval_genericX] at hm
  exact eq_inv_of_mul_eq_one_right hm

end Dubon2026.SourceEllipticFunctionField
