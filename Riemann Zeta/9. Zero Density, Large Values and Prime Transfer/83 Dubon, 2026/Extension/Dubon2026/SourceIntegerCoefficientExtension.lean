import Mathlib.RingTheory.TensorProduct.Basic

/-! DUB-17/18 -> arithmetic primitive projector -> faithful Hecke
coefficient extension. Use the native scalar-extension universal property
with the actual coefficient embedding and integral operator map. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {F K A B : Type*} [Field F] [Field K] [Ring A] [Ring B] [Algebra K B]

/-- The literal scalar extension of an integral algebra map along a coefficient embedding. -/
def integerCoefficientExtension (ι : F →+* K) (φ : A →+* B) : F ⊗[ℤ] A →+* B := by
  letI := Algebra.compHom B ι
  letI : IsScalarTower ℤ F B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact ((AlgHom.liftEquiv ℤ F A B) φ.toIntAlgHom).toRingHom

theorem integerCoefficientExtension_tmul (ι : F →+* K) (φ : A →+* B) (a : F) (t : A) :
    integerCoefficientExtension ι φ (a ⊗ₜ[ℤ] t) = ι a • φ t := rfl

end
end Dubon2026
