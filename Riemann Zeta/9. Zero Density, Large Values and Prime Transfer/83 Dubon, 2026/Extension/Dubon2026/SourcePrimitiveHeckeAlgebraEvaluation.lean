import Dubon2026.SourceTensorCharacterIdempotent
import Dubon2026.SourceIntegerCoefficientExtensionCharacter
import Dubon2026.SourceIntegerCoefficientExtensionOne
import Dubon2026.SourcePrimitiveTensorEigencharacter

/-! DUB-17/18 -> nonzero primitive rank-two image. Evaluate the literal
arithmetic projector in the coefficient extension of the original p-adic
Hecke algebra, preserving integral operators and the prescribed character. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable (N : ℕ) [NeZero N]
variable {K E T : Type*} [Field K] [Field E] [CommRing T]
variable [Algebra K E] [Algebra K T]

/-- The arithmetic Hecke tensor evaluated in a coefficient-extended Hecke algebra. -/
def primitiveHeckeAlgebraEvaluation (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T) :
    sourcePrimitiveCoefficientField f ⊗[ℤ] sourceOriginalIntegralHeckeAlgebra N 2 →+*
      E ⊗[K] T :=
  integerCoefficientExtension τ (Algebra.TensorProduct.includeRight.toRingHom.comp δ)

theorem primitiveHeckeAlgebraEvaluation_integral (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T)
    (t : sourceOriginalIntegralHeckeAlgebra N 2) :
    primitiveHeckeAlgebraEvaluation N f τ δ (K := K)
      ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] t) =
      (1 : E) ⊗ₜ[K] δ t :=
  integerCoefficientExtension_one_tmul τ
    ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := T)).toRingHom.comp δ) t

theorem primitiveHeckeAlgebraEvaluation_character (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T) (κ : T →ₐ[K] E)
    (hκ : ∀ t, κ (δ t) = τ (sourcePrimitiveFieldHeckeCharacter f t))
    (z : sourcePrimitiveCoefficientField f ⊗[ℤ] sourceOriginalIntegralHeckeAlgebra N 2) :
    coefficientTensorCharacter κ (primitiveHeckeAlgebraEvaluation N f τ δ z) =
      τ (primitiveTensorEigencharacter N f z) := by
  apply integerCoefficientExtension_character τ
    (Algebra.TensorProduct.includeRight.toRingHom.comp δ)
    (sourcePrimitiveFieldHeckeCharacter f).toRingHom (coefficientTensorCharacter κ) _ z
  intro t
  change coefficientTensorCharacter κ ((1 : E) ⊗ₜ[K] δ t) = _
  rw [coefficientTensorCharacter_tmul, one_mul]
  exact hκ t

end
end Dubon2026
