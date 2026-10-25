import Dubon2026.SourceGeneratedCharacterIdempotent
import Dubon2026.SourceCharacterIdempotentRankTwo
import Mathlib.RingTheory.TensorProduct.Basic

/-! DUB-17/18 -> original primitive Tate image. The prescribed character
extends to the actual scalar-extended Hecke algebra. Prime-generator
scalar identities then identify the whole idempotent ideal's character. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {K E T : Type*} [Field K] [Field E] [CommRing T]
variable [Algebra K E] [Algebra K T]

/-- The prescribed Hecke character on its literal coefficient-field tensor algebra. -/
def coefficientTensorCharacter (κ : T →ₐ[K] E) : E ⊗[K] T →ₐ[E] E :=
  AlgHom.liftEquiv K E T E κ

theorem coefficientTensorCharacter_tmul (κ : T →ₐ[K] E) (a : E) (t : T) :
    coefficientTensorCharacter κ (a ⊗ₜ[K] t) = a * κ t := rfl

theorem tensor_character_idempotent_scalar {I : Type*}
    (χ : I → T) (hχ : Algebra.adjoin K (Set.range χ) = ⊤)
    (κ : T →ₐ[K] E) (e : E ⊗[K] T)
    (he : ∀ i, ((1 : E) ⊗ₜ[K] χ i) * e = κ (χ i) • e) :
    ∀ z : E ⊗[K] T, z * e = coefficientTensorCharacter κ z • e := by
  have ht : ∀ t : T, ((1 : E) ⊗ₜ[K] t) * e = κ t • e :=
    character_scalar_action_of_generators χ hχ Algebra.TensorProduct.includeRight κ e he
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy, add_smul]
  | tmul a t =>
    rw [coefficientTensorCharacter_tmul]
    calc
      (a ⊗ₜ[K] t) * e = (a • ((1 : E) ⊗ₜ[K] t)) * e := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • (((1 : E) ⊗ₜ[K] t) * e) := smul_mul_assoc _ _ _
      _ = (a * κ t) • e := by rw [ht, smul_smul]

end
end Dubon2026
