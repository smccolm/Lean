import Dubon2026.RepresentationCoordinateEquivalence
import Dubon2026.ContinuousRepresentationFiniteQuotient
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Actual finite quotient coordinate algebras for continuous discrete representations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original coordinate algebra is Noetherian for an actual finite group and a Noetherian coefficient ring. -/
theorem representationCoordinateAlgebra_isNoetherian [Finite G] [IsNoetherianRing R] :
    IsNoetherianRing (RepresentationCoordinateAlgebra G ι R) := by
  infer_instance

/-- The original continuous representation of a compact group over a discrete Noetherian ring is evaluated from the actual Noetherian coordinate algebra of its original kernel quotient. -/
theorem continuousMatrixRepresentation_noetherianCoordinates
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace R] [DiscreteTopology R] [IsNoetherianRing R]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    IsNoetherianRing (RepresentationCoordinateAlgebra (G ⧸ ρ.ker) ι R) ∧
      ∃ f : RepresentationCoordinateAlgebra (G ⧸ ρ.ker) ι R →ₐ[R] R,
        ((GeneralLinearGroup.map f.toRingHom).comp
          (universalMatrixRepresentation (G ⧸ ρ.ker) ι R)).comp
            (QuotientGroup.mk' ρ.ker) = ρ := by
  letI : Finite (G ⧸ ρ.ker) := continuousMatrixRepresentation_quotient_finite ρ hρ
  refine ⟨representationCoordinateAlgebra_isNoetherian, ?_⟩
  refine ⟨representationCoordinateEvaluation (QuotientGroup.kerLift ρ), ?_⟩
  rw [universalMatrixRepresentation_evaluation]
  exact continuousMatrixRepresentation_factor ρ

end
end Dubon2026
