import Dubon2026.HopfTensorCoordinateInclusions
import Dubon2026.HopfPointsRestriction

/-! # Actual tensor-coordinate Hopf points are the product of the original point groups -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [HopfAlgebra R B] [CommRing K] [Algebra R K]

/-- Pair the two genuine coordinate restriction homomorphisms. -/
private def tensorPointRestrictionHom :
    WithConv ((A ⊗[R] B) →ₐ[R] K) →*
      WithConv (A →ₐ[R] K) × WithConv (B →ₐ[R] K) :=
  (hopfPointsRestriction hopfTensorIncludeLeft).prod
    (hopfPointsRestriction hopfTensorIncludeRight)

/-- Genuine coordinate restriction identifies the points of the tensor Hopf algebra with the product of the original convolution point groups. -/
def hopfTensorPointsProductEquiv :
    WithConv ((A ⊗[R] B) →ₐ[R] K) ≃*
      WithConv (A →ₐ[R] K) × WithConv (B →ₐ[R] K) where
  toFun := tensorPointRestrictionHom
  invFun p := WithConv.toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv)
  left_inv p := by
    apply WithConv.ext
    apply Algebra.TensorProduct.ext'
    intro a b
    change p.ofConv (hopfTensorIncludeLeft a) * p.ofConv (hopfTensorIncludeRight b) =
      p.ofConv (a ⊗ₜ[R] b)
    rw [hopfTensorIncludeLeft_apply, hopfTensorIncludeRight_apply, ← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv p := by
    apply Prod.ext
    · apply WithConv.ext
      ext a
      change Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv
        (hopfTensorIncludeLeft a) = p.1.ofConv a
      rw [hopfTensorIncludeLeft_apply]
      exact Algebra.TensorProduct.productMap_left_apply _ _ a
    · apply WithConv.ext
      ext b
      change Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv
        (hopfTensorIncludeRight b) = p.2.ofConv b
      rw [hopfTensorIncludeRight_apply]
      exact Algebra.TensorProduct.productMap_right_apply _ _ b
  map_mul' := tensorPointRestrictionHom.map_mul

/-- The inverse product identification multiplies the original two coordinate values on a pure tensor. -/
theorem hopfTensorPointsProductEquiv_symm_tmul
    (p : WithConv (A →ₐ[R] K) × WithConv (B →ₐ[R] K)) (a : A) (b : B) :
    (hopfTensorPointsProductEquiv (R := R)).symm p (a ⊗ₜ[R] b) = p.1 a * p.2 b := by
  rfl

end
end Dubon2026
