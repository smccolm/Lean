import Dubon2026.DeterminantCoefficientLaw
import Dubon2026.SymmetricRepresentationReduction

/-! # Determinant families of the original symmetric-power representations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S]

/-- The determinant family of the actual degree-n homogeneous representation has degree n+1 over every coefficient extension. -/
theorem symmetricMatrixRepresentation_determinant_degree (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (φ : R →+* S)
    (a : S) (x : MonoidAlgebra S G) :
    determinantCoefficientLaw (symmetricMatrixRepresentation n ρ) φ (a • x) =
      a ^ (n + 1) * determinantCoefficientLaw (symmetricMatrixRepresentation n ρ) φ x := by
  simpa using determinantCoefficientLaw_homogeneous (symmetricMatrixRepresentation n ρ) φ a x

/-- The actual determinant family can be computed by first changing the original rank-two coefficients and then taking its genuine symmetric power. -/
theorem symmetricMatrixRepresentation_determinant_baseChange (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (φ : R →+* S)
    (x : MonoidAlgebra S G) :
    determinantCoefficientLaw (symmetricMatrixRepresentation n ρ) φ x =
      matrixRepresentationDeterminant
        (symmetricMatrixRepresentation n ((GeneralLinearGroup.map φ).comp ρ)) x := by
  unfold determinantCoefficientLaw
  rw [symmetricMatrixRepresentation_map]

end
end Dubon2026
