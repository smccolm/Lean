import Dubon2026.GaloisTensorFixedCoordinates
import Dubon2026.AlgebraBaseChangePoints

/-! # Original point evaluation of genuine semilinear Galois coordinate action -/

namespace Dubon2026
noncomputable section
open Module
open scoped TensorProduct

variable {F K A : Type*} [Field F] [Field K] [Algebra F K]
  [CommRing A] [Algebra F A]

/-- The genuine coefficient automorphism of the actual geometric coordinate algebra, retaining its original ground-field algebra structure. -/
def galoisTensorCoefficientAutomorphism (g : K ≃ₐ[F] K) :
    K ⊗[F] A ≃ₐ[F] K ⊗[F] A :=
  Algebra.TensorProduct.congr g (AlgEquiv.refl : A ≃ₐ[F] A)

/-- The actual semilinear coefficient action evaluates against the same original point by twisting that point with the inverse original coefficient automorphism. -/
theorem galoisTensorCoefficientAutomorphism_point (g : K ≃ₐ[F] K)
    (p : A →ₐ[F] K) (z : K ⊗[F] A) :
    AlgHom.liftEquiv F K A K p (galoisTensorCoefficientAutomorphism g z) =
      g (AlgHom.liftEquiv F K A K (g.symm.toAlgHom.comp p) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k a =>
    change g k * p a = g (k * g.symm (p a))
    rw [map_mul, AlgEquiv.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Genuine Galois-fixed geometric algebra coordinates are exactly the images of original coordinates, using the same original finite basis and proved coefficient fixed-field descent. -/
theorem galoisTensorCoefficientAutomorphism_fixed_iff [IsGalois F K]
    {ι : Type*} [Finite ι] (b : Basis ι F A) (z : K ⊗[F] A) :
    (∀ g : K ≃ₐ[F] K, galoisTensorCoefficientAutomorphism g z = z) ↔
      ∃ a : A, (1 : K) ⊗ₜ[F] a = z := by
  exact galoisTensor_fixed_iff_original b z

end
end Dubon2026
