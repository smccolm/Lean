import Dubon2026.RepresentationCoordinateFibers
import Dubon2026.FirstOrderDeformationEquiv

/-! # Actual first-order representation coordinates and original adjoint cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual dual-number coordinate fiber is equivalent to the original first-order matrix representation fiber. -/
def firstOrderRepresentationCoordinateEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateFiber ρ (TrivSqZeroExt.fstHom R R R) ≃ MatrixFirstOrderLift ρ :=
  representationCoordinateFiberEquiv ρ (TrivSqZeroExt.fstHom R R R)

/-- The actual tangent coordinate fiber is equivalent to the genuine adjoint cocycle module of the original representation. -/
def firstOrderCoordinateCocycleEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateFiber ρ (TrivSqZeroExt.fstHom R R R) ≃
      groupCohomology.cocycles₁ (matrixAdjointRep ρ) :=
  (firstOrderRepresentationCoordinateEquiv ρ).trans (matrixFirstOrderLiftEquiv ρ)

/-- The cocycle of the actual original coordinate point is the original first-order matrix cocycle, not a new abstract tangent variable. -/
theorem firstOrderCoordinateCocycleEquiv_apply (ρ : G →* GeneralLinearGroup ι R)
    (f : RepresentationCoordinateFiber ρ (TrivSqZeroExt.fstHom R R R)) :
    firstOrderCoordinateCocycleEquiv ρ f =
      matrixFirstOrderCocycle ρ (firstOrderRepresentationCoordinateEquiv ρ f) := rfl

/-- Every original adjoint cocycle is represented by an actual coordinate-algebra map in the original first-order fiber. -/
theorem firstOrderCoordinateCocycleEquiv_surjective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (firstOrderCoordinateCocycleEquiv ρ) :=
  (firstOrderCoordinateCocycleEquiv ρ).surjective

end
end Dubon2026
