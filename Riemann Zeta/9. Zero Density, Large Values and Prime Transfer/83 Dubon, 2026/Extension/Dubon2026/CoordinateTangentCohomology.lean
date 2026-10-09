import Dubon2026.CoordinateCocycleLinearity
import Dubon2026.FirstOrderCohomologyClassification

/-! # The actual linear first-cohomology class of coordinate tangents -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The genuine coordinate tangent has its original adjoint H1 class by a proved linear map. -/
def coordinateTangentCohomologyMap (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateDerivations ρ →ₗ[R] groupCohomology.H1 (matrixAdjointRep ρ) :=
  (groupCohomology.H1π (matrixAdjointRep ρ)).hom.comp (coordinateDerivationCocycleLinearMap ρ)

/-- The original linear tangent class vanishes exactly when its actual original cocycle is an adjoint coboundary. -/
theorem coordinateTangentCohomologyMap_eq_zero_iff
    (ρ : G →* GeneralLinearGroup ι R) (d : RepresentationCoordinateDerivations ρ) :
    coordinateTangentCohomologyMap ρ d = 0 ↔
      (representationCoordinateDerivationCocycleEquiv ρ d : G → Matrix ι ι R) ∈
        groupCohomology.coboundaries₁ (matrixAdjointRep ρ) :=
  groupCohomology.H1π_eq_zero_iff (representationCoordinateDerivationCocycleEquiv ρ d)

/-- Every actual adjoint first-cohomology class is represented by a genuine original coordinate tangent. -/
theorem coordinateTangentCohomologyMap_surjective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (coordinateTangentCohomologyMap ρ) := by
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    obtain ⟨d, hd⟩ := (representationCoordinateDerivationCocycleEquiv ρ).surjective c
    refine ⟨d, ?_⟩
    change groupCohomology.H1π (matrixAdjointRep ρ)
      (representationCoordinateDerivationCocycleEquiv ρ d) = _
    rw [hd]

/-- Equality of the original linear tangent classes is precisely strict conjugacy of the actual original matrix lifts. -/
theorem coordinateTangentCohomologyMap_eq_iff (ρ : G →* GeneralLinearGroup ι R)
    (d e : RepresentationCoordinateDerivations ρ) :
    coordinateTangentCohomologyMap ρ d = coordinateTangentCohomologyMap ρ e ↔
      MatrixFirstOrderStrictlyConjugate ρ
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ d))
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ e)) :=
  (matrixFirstOrderStrictlyConjugate_iff ρ _ _).symm

end
end Dubon2026
