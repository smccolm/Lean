import Dubon2026.SourceEllipticKernelEvaluationCoordinates

/-! The literal finite Velu formulas at an affine point are evaluations of
the proved generic coordinates in the actual kernel localization. The formulas
follow the frozen anthropics/fermats-last-theorem Definitions/Def_WeierstrassCurve_
VeluPointMap.lean (Apache-2.0, 6e837e75355538c7f80bab5b956861e86c4eacc2).
This supplies actual-coordinate specialization for the norm point map on
DUB-17/18, without substituting an independently chosen point map. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The literal finite Velu x-formula at an affine coordinate. -/
noncomputable def veluAffineX (x : F) : F :=
  Xv S Prod.fst (fun P => veluT W P.1 P.2) (fun P => veluU W P.1 P.2) x

/-- The literal finite Velu y-formula at affine coordinates. -/
noncomputable def veluAffineY (x y : F) : F :=
  y - ∑ P ∈ S, (veluU W P.1 P.2 * (2 * y + W.a₁ * x + W.a₃) / (x - P.1) ^ 3 +
    veluT W P.1 P.2 * (W.a₁ * (x - P.1) + y - P.2) / (x - P.1) ^ 2 +
    (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) / (x - P.1) ^ 2)

variable {x y : F} (h : W.toAffine.Equation x y) (hd : (hP S Prod.fst).eval x ≠ 0)

/-- The actual localized generic quotient x-coordinate evaluates to the literal affine formula. -/
theorem kernelLocalEval_genericVeluX :
    kernelLocalEval W S h hd ⟨genericVeluX W S, genericVeluX_mem_kernelLocalRing W S⟩ = veluAffineX W S x := by
  let T := kernelLocalRing W S
  let X : T := ⟨genericX W.toAffine, by simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X⟩
  let c := algebraMap F T
  let u (P : S) : T := ⟨(genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.val.1)⁻¹,
    inverse_kernel_factor_mem_local W S P.property⟩
  have he : (⟨genericVeluX W S, genericVeluX_mem_kernelLocalRing W S⟩ : T) =
      X + ∑ P : S, (c (veluT W P.val.1 P.val.2) * u P + c (veluU W P.val.1 P.val.2) * u P ^ 2) := by
    apply Subtype.ext
    simp [genericVeluX, Xv, X, c, u, T, div_eq_mul_inv, ← inv_pow]
    exact (Finset.sum_attach S (fun P =>
      algebraMap F W.toAffine.FunctionField (veluT W P.1 P.2) *
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ +
      algebraMap F W.toAffine.FunctionField (veluU W P.1 P.2) *
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ^ 2)).symm
  have hc (a : F) : kernelLocalEval W S h hd (c a) = a := kernelLocalEval_constant W S h hd a
  have hu (P : S) : kernelLocalEval W S h hd (u P) = (x - P.val.1)⁻¹ :=
    kernelLocalEval_inverse_factor W S h hd P.property
  rw [he]
  simp only [map_add, map_sum, map_mul, map_pow, hc, hu, X, kernelLocalEval_genericX]
  simp only [veluAffineX, Xv, div_eq_mul_inv, inv_pow]
  congr 1
  exact Finset.sum_coe_sort S (fun P => veluT W P.1 P.2 * (x - P.1)⁻¹ +
    veluU W P.1 P.2 * ((x - P.1) ^ 2)⁻¹)

/-- The actual localized generic quotient y-coordinate evaluates to the literal affine formula. -/
theorem kernelLocalEval_genericVeluY :
    kernelLocalEval W S h hd ⟨genericVeluY W S, genericVeluY_mem_kernelLocalRing W S⟩ = veluAffineY W S x y := by
  let T := kernelLocalRing W S
  let X : T := ⟨genericX W.toAffine, by simpa only [aeval_X] using aeval_genericX_mem_kernelLocalRing W S X⟩
  let Y : T := ⟨genericY W.toAffine, genericY_mem_kernelLocalRing W S⟩
  let c := algebraMap F T
  let u (P : S) : T := ⟨(genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.val.1)⁻¹,
    inverse_kernel_factor_mem_local W S P.property⟩
  have he : (⟨genericVeluY W S, genericVeluY_mem_kernelLocalRing W S⟩ : T) =
      Y - ∑ P : S, (c (veluU W P.val.1 P.val.2) * (c 2 * Y + c W.a₁ * X + c W.a₃) * u P ^ 3 +
        c (veluT W P.val.1 P.val.2) * (c W.a₁ * (X - c P.val.1) + Y - c P.val.2) * u P ^ 2 +
        c (W.a₁ * veluU W P.val.1 P.val.2 - veluGx W P.val.1 P.val.2 * veluGy W P.val.1 P.val.2) * u P ^ 2) := by
    apply Subtype.ext
    simp [genericVeluY, X, Y, c, u, T, div_eq_mul_inv, ← inv_pow]
    simp only [map_ofNat (algebraMap F W.toAffine.FunctionField)]
    exact (Finset.sum_attach S (fun P =>
      algebraMap F W.toAffine.FunctionField (veluU W P.1 P.2) *
        (2 * genericY W.toAffine + algebraMap F W.toAffine.FunctionField W.a₁ * genericX W.toAffine +
          algebraMap F W.toAffine.FunctionField W.a₃) *
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ^ 3 +
      algebraMap F W.toAffine.FunctionField (veluT W P.1 P.2) *
        (algebraMap F W.toAffine.FunctionField W.a₁ *
          (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1) + genericY W.toAffine -
          algebraMap F W.toAffine.FunctionField P.2) *
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ^ 2 +
      (algebraMap F W.toAffine.FunctionField W.a₁ * algebraMap F W.toAffine.FunctionField (veluU W P.1 P.2) -
        algebraMap F W.toAffine.FunctionField (veluGx W P.1 P.2) *
        algebraMap F W.toAffine.FunctionField (veluGy W P.1 P.2)) *
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1)⁻¹ ^ 2)).symm
  have hc (a : F) : kernelLocalEval W S h hd (c a) = a := kernelLocalEval_constant W S h hd a
  have hu (P : S) : kernelLocalEval W S h hd (u P) = (x - P.val.1)⁻¹ :=
    kernelLocalEval_inverse_factor W S h hd P.property
  rw [he]
  simp only [map_sub, map_add, map_sum, map_mul, map_pow, hc, hu, X, Y,
    kernelLocalEval_genericX, kernelLocalEval_genericY]
  simp only [veluAffineY, div_eq_mul_inv, inv_pow]
  congr 1
  exact Finset.sum_coe_sort S (fun P =>
    veluU W P.1 P.2 * (2 * y + W.a₁ * x + W.a₃) * ((x - P.1) ^ 3)⁻¹ +
    veluT W P.1 P.2 * (W.a₁ * (x - P.1) + y - P.2) * ((x - P.1) ^ 2)⁻¹ +
    (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) * ((x - P.1) ^ 2)⁻¹)

end Dubon2026.SourceEllipticFunctionField
