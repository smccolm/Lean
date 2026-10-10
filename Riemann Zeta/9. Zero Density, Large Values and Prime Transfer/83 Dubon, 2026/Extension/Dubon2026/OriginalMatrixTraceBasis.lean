import Dubon2026.ClosedMatrixTraceCoefficientRing
import Dubon2026.MatrixTraceBasisCoordinates
import Dubon2026.LocalMatrixRepresentationBasis

/-! # Genuine original representation matrices have coordinates in their actual closed trace algebra -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- In a full original matrix basis consisting of actual representation matrices, every original representation matrix has all its genuine coordinates in the actual closed trace coefficient algebra. -/
theorem originalMatrixBasis_coordinates_mem_closedTrace {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (a : κ → G)
    (b : Basis κ R (Matrix ι ι R)) (hb : ∀ i, b i = (ρ (a i)).val) (x : G) (i : κ) :
    b.repr (ρ x).val i ∈ closedMatrixTraceAlgebra (O := O) ρ := by
  letI := closedMatrixTraceAlgebra_isLocalHom hR eR ρ
  have hmul (y z : G) : (ρ y).val * (ρ z).val = (ρ (y * z)).val := by
    rw [map_mul]
    rfl
  apply matrixBasisCoordinates_mem_of_trace (closedMatrixTraceAlgebra (O := O) ρ) b
  · intro j k
    rw [hb j, hb k, hmul]
    exact trace_mem_closedMatrixTraceAlgebra ρ (a j * a k)
  · intro j
    rw [hb j, hmul]
    exact trace_mem_closedMatrixTraceAlgebra ρ (x * a j)

/-- For the actual absolutely irreducible original true residual representation, select a genuine finite basis from the original whole representation matrices and derive, for every group element, that all matrix coordinates belong to the actual closed original trace algebra. -/
theorem originalMatrixTraceBasis_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → G) (b : Basis κ R (Matrix ι ι R)),
      (∀ i, b i = (ρ (a i)).val) ∧
      ∀ x i, b.repr (ρ x).val i ∈ closedMatrixTraceAlgebra (O := O) ρ := by
  classical
  obtain ⟨κ, instκ, a, b, hb⟩ := localMatrixRepresentation_exists_basis (L := L) ρ
  letI := instκ
  exact ⟨κ, instκ, a, b, hb,
    fun x i => originalMatrixBasis_coordinates_mem_closedTrace hR eR ρ a b hb x i⟩

end
end Dubon2026
