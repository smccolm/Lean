import Dubon2026.LocalMatrixRepresentationSpanning
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # A genuine finite matrix basis selected from the original whole representation -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R]

/-- Absolute irreducibility of the original true residual representation supplies a genuine finite basis of the full original coefficient matrix algebra consisting of actual original representation matrices. -/
theorem localMatrixRepresentation_exists_basis
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → G) (b : Basis κ R (Matrix ι ι R)),
      ∀ i, b i = (ρ (a i)).val := by
  letI : Module.FinitePresentation R (Matrix ι ι R) :=
    Module.finitePresentation_of_projective R (Matrix ι ι R)
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat
    (fun g : G => (ρ g).val) (localMatrixRepresentation_span_eq_top (L := L) ρ)
  letI : Finite κ := Module.Finite.finite_basis b
  exact ⟨κ, Fintype.ofFinite κ, a, b, hb⟩

end
end Dubon2026
