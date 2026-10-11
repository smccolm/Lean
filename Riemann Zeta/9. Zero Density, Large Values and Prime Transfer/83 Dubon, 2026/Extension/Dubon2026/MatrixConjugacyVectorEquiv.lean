import Dubon2026.MatrixCoefficientPointActions
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Actual changes of basis on the original matrix representation group -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

/-- The genuine invertible matrix acts on its original column-vector additive group. -/
def matrixConjugacyVectorEquiv (U : GeneralLinearGroup ι A) :
    Multiplicative (ι → A) ≃* Multiplicative (ι → A) :=
  AddEquiv.toMultiplicative (GeneralLinearGroup.toLin U).toLinearEquiv.toAddEquiv

/-- The actual change of basis preserves the original matrix-vector formula. -/
theorem matrixConjugacyVectorEquiv_apply (U : GeneralLinearGroup ι A) (v : ι → A) :
    matrixConjugacyVectorEquiv U (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (U.val *ᵥ v) := by
  rfl

/-- The same original matrix conjugacy intertwines the complete original Galois-module actions. -/
theorem matrixConjugacyVectorEquiv_equivariant
    (ρ τ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) (g : G) (v : Multiplicative (ι → A)) :
    matrixConjugacyVectorEquiv U (matrixUnderlyingGroupAction ρ g v) =
      matrixUnderlyingGroupAction τ g (matrixConjugacyVectorEquiv U v) := by
  have hm : (τ g).val * U.val = U.val * (ρ g).val := by
    change (τ g * U).val = (U * ρ g).val
    rw [hc g]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  change Multiplicative.ofAdd (U.val *ᵥ ((ρ g).val *ᵥ Multiplicative.toAdd v)) =
    Multiplicative.ofAdd ((τ g).val *ᵥ (U.val *ᵥ Multiplicative.toAdd v))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]

end
end Dubon2026
