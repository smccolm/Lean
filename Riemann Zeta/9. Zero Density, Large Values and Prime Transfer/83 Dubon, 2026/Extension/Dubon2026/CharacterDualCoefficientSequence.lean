import Dubon2026.TraceZeroContinuousCharacterPairing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The actual character-valued dual of a coefficient sequence

The dual maps are literal precomposition. Their equivariance and exactness
derive the dual-sequence premises needed by cup adjunction in DUB-17's local
duality route, using pinned linear algebra rather than a new duality interface.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G]
  (A B C : Rep.{0} k G) (χ : G →* k)

/-- The character-valued dual has the original linear maps and conjugate action. -/
abbrev characterDualCoefficientRep (A : Rep.{0} k G) (χ : G →* k) : Rep k G :=
  Rep.of (Representation.linHom A.ρ (coefficientCharacterRep χ).ρ)

/-- The original dual coefficient map is literal precomposition. -/
def characterDualCoefficientMap (f : A →ₗ[k] B) :
    characterDualCoefficientRep B χ →ₗ[k] characterDualCoefficientRep A χ := f.dualMap

/-- Precomposition respects the same character-valued dual action. -/
theorem characterDualCoefficientMap_equivariant (f : A →ₗ[k] B)
    (hf : ∀ g a, f (A.ρ g a) = B.ρ g (f a))
    (g : G) (ℓ : characterDualCoefficientRep B χ) :
    characterDualCoefficientMap A B χ f ((characterDualCoefficientRep B χ).ρ g ℓ) =
      (characterDualCoefficientRep A χ).ρ g (characterDualCoefficientMap A B χ f ℓ) := by
  apply LinearMap.ext
  intro a
  change χ g * ℓ (B.ρ g⁻¹ (f a)) = χ g * ℓ (f (A.ρ g⁻¹ a))
  rw [hf]

/-- Surjectivity of the original quotient gives injectivity of its actual dual. -/
theorem characterDualCoefficientMap_injective (f : A →ₗ[k] B)
    (hf : Function.Surjective f) : Function.Injective (characterDualCoefficientMap A B χ f) :=
  LinearMap.dualMap_injective_of_surjective hf

/-- Injectivity of the original inclusion gives surjectivity of its actual dual,
using the pinned extension theorem for linear functionals. -/
theorem characterDualCoefficientMap_surjective (f : A →ₗ[k] B)
    (hf : Function.Injective f) : Function.Surjective (characterDualCoefficientMap A B χ f) :=
  LinearMap.dualMap_surjective_of_injective hf

/-- Original coefficient exactness gives exactness of the reversed character
dual sequence. No separate dual-exactness premise is retained. -/
theorem characterDualCoefficientSequence_exact
    (φ : A →ₗ[k] B) (ψ : B →ₗ[k] C)
    (hExact : LinearMap.range φ = LinearMap.ker ψ) :
    LinearMap.range (characterDualCoefficientMap B C χ ψ) =
      LinearMap.ker (characterDualCoefficientMap A B χ φ) := by
  change LinearMap.range ψ.dualMap = LinearMap.ker φ.dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, hExact]

/-- The actual coefficient pairing is evaluation of the original linear map. -/
def characterDualEvaluation :
    A →ₗ[k] characterDualCoefficientRep A χ →ₗ[k] coefficientCharacterRep χ :=
  LinearMap.flip (LinearMap.id : (A →ₗ[k] k) →ₗ[k] A →ₗ[k] k)

/-- Original evaluation is equivariant into the actual character line. -/
theorem characterDualEvaluation_equivariant
    (g : G) (a : A) (ℓ : characterDualCoefficientRep A χ) :
    characterDualEvaluation A χ (A.ρ g a) ((characterDualCoefficientRep A χ).ρ g ℓ) =
      (coefficientCharacterRep χ).ρ g (characterDualEvaluation A χ a ℓ) := by
  have hi : A.ρ g⁻¹ (A.ρ g a) = a := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  change χ g * ℓ (A.ρ g⁻¹ (A.ρ g a)) = χ g * ℓ a
  rw [hi]

/-- The exact adjointness relation for the original inclusion and dual quotient
is literal equality of evaluation on the original coefficient elements. -/
theorem characterDualEvaluation_precompose (f : A →ₗ[k] B)
    (a : A) (ℓ : characterDualCoefficientRep B χ) :
    characterDualEvaluation B χ (f a) ℓ =
      characterDualEvaluation A χ a (characterDualCoefficientMap A B χ f ℓ) := rfl

end
end Dubon2026
