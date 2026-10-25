import Dubon2026.SourceIntegerCoefficientExtensionLaws

/-! DUB-17/18 -> nonzero primitive Tate component. Literal coefficient
extension preserves the prescribed character normalization and the exact
Hecke scalar identities of the arithmetic projector. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {F K A B : Type*} [Field F] [Field K] [Ring A] [Ring B] [Algebra K B]

theorem integerCoefficientExtension_character
    (ι : F →+* K) (φ : A →+* B) (η : A →+* F) (ψ : B →ₐ[K] K)
    (hψ : ∀ a, ψ (φ a) = ι (η a)) (z : F ⊗[ℤ] A) :
    ψ (integerCoefficientExtension ι φ z) =
      ι (integerCoefficientExtension (RingHom.id F) η z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a t =>
    simp only [integerCoefficientExtension_tmul, map_smul, hψ,
      RingHom.id_apply, smul_eq_mul, map_mul]

theorem integerCoefficientExtension_eigen_identity
    (ι : F →+* K) (φ : A →+* B) (x y : F ⊗[ℤ] A) (a : F)
    (h : x * y = a • y) :
    integerCoefficientExtension ι φ x * integerCoefficientExtension ι φ y =
      ι a • integerCoefficientExtension ι φ y := by
  simpa only [map_mul, integerCoefficientExtension_smul] using
    congrArg (integerCoefficientExtension ι φ) h

end
end Dubon2026
