import Dubon2026.SourceEllipticKernelLocalization

/-! The literal Velu coordinates belong to the original affine coordinate
ring localized at its actual kernel denominator. Complementary factors give
each inverse linear denominator, reusing the finite-product proof already
used for odd coordinate integrality. These are the regular affine formulas
needed for evaluation of the actual norm point map (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- Every original polynomial coordinate function belongs to the actual kernel localization. -/
theorem aeval_genericX_mem_kernelLocalRing (p : F[X]) :
    aeval (genericX W.toAffine) p ∈ kernelLocalRing W S := by
  rw [← algebraMap_eq_aeval_genericX]
  rw [IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField]
  exact (kernelLocalRing W S).algebraMap_mem _

/-- The original y-coordinate belongs to the actual kernel localization. -/
theorem genericY_mem_kernelLocalRing : genericY W.toAffine ∈ kernelLocalRing W S :=
  (kernelLocalRing W S).algebraMap_mem _

/-- Every actual kernel linear factor has its inverse in the kernel localization. -/
theorem inverse_kernel_factor_mem_local {P : F × F} (hPmem : P ∈ S) :
    (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ∈ kernelLocalRing W S := by
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
  exact (kernelLocalRing W S).mul_mem (aeval_genericX_mem_kernelLocalRing W S p)
    (inverse_kernel_mem_local W S)

/-- The actual finite quotient x-formula is regular on the kernel localization. -/
theorem genericVeluX_mem_kernelLocalRing : genericVeluX W S ∈ kernelLocalRing W S := by
  let T := (kernelLocalRing W S).restrictScalars F
  have hx : genericX W.toAffine ∈ T := by
    simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X
  change genericVeluX W S ∈ T
  unfold genericVeluX Xv
  refine T.add_mem hx (T.sum_mem fun P hP => ?_)
  simp only [div_eq_mul_inv, ← inv_pow]
  have hi : (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ∈ T :=
    inverse_kernel_factor_mem_local W S hP
  exact T.add_mem (T.mul_mem (T.algebraMap_mem _) hi) (T.mul_mem (T.algebraMap_mem _) (T.pow_mem hi 2))

/-- The actual finite quotient y-formula is regular on the kernel localization. -/
theorem genericVeluY_mem_kernelLocalRing : genericVeluY W S ∈ kernelLocalRing W S := by
  let T := (kernelLocalRing W S).restrictScalars F
  have hx : genericX W.toAffine ∈ T := by
    simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X
  have hy : genericY W.toAffine ∈ T := genericY_mem_kernelLocalRing W S
  change genericVeluY W S ∈ T
  unfold genericVeluY
  refine T.sub_mem hy (T.sum_mem fun P hP => ?_)
  simp only [div_eq_mul_inv, ← inv_pow]
  have hi : (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ∈ T :=
    inverse_kernel_factor_mem_local W S hP
  exact T.add_mem (T.add_mem
    (T.mul_mem (T.mul_mem (T.algebraMap_mem _)
      (T.add_mem (T.add_mem (T.mul_mem (T.natCast_mem 2) hy) (T.mul_mem (T.algebraMap_mem _) hx))
        (T.algebraMap_mem _))) (T.pow_mem hi 3))
    (T.mul_mem (T.mul_mem (T.algebraMap_mem _)
      (T.sub_mem (T.add_mem (T.mul_mem (T.algebraMap_mem _)
        (T.sub_mem hx (T.algebraMap_mem _))) hy) (T.algebraMap_mem _))) (T.pow_mem hi 2)))
    (T.mul_mem (T.algebraMap_mem _) (T.pow_mem hi 2))

end Dubon2026.SourceEllipticFunctionField
