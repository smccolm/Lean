import Dubon2026.OriginalMatrixTraceBasis
import Dubon2026.CoefficientRepresentationMatrixAlgebra

/-! # The genuine original representation algebra over its closed trace coefficients is finite, free and closed -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- Actual original residual absolute irreducibility makes the genuine original representation matrix algebra finite and free over its actual closed trace coefficient ring, and closed in the original ambient matrix topology. -/
theorem originalClosedTraceMatrixAlgebra_finite_free_closed
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Module.Finite (closedMatrixTraceAlgebra (O := O) ρ)
        (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ) ∧
      Module.Free (closedMatrixTraceAlgebra (O := O) ρ)
        (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ) ∧
      IsClosed (coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ :
        Set (Matrix ι ι R)) := by
  classical
  obtain ⟨κ, instκ, a, b, hb, hcoord⟩ := originalMatrixTraceBasis_exists (L := L) hR eR ρ
  letI := instκ
  have hff := coefficientRepresentationMatrixAlgebra_finite_free
    (closedMatrixTraceAlgebra (O := O) ρ) ρ a b hb hcoord
  exact ⟨hff.1, hff.2, isClosed_coefficientRepresentationMatrixAlgebra
    (closedMatrixTraceAlgebra (O := O) ρ) (isClosed_closedMatrixTraceAlgebra ρ) ρ a b hb hcoord⟩

end
end Dubon2026
