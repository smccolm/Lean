import Dubon2026.RepresentationCoordinateDerivations
import Dubon2026.RepresentationCoordinateFiniteType
import Mathlib.RingTheory.Kaehler.Basic

/-! # The genuine cotangent module of the original representation coordinate algebra -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Actual linear maps from the genuine coordinate Kähler differential module to the original point's epsilon ideal. -/
abbrev RepresentationCoordinateCotangentMaps (ρ : G →* GeneralLinearGroup ι R) :=
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  KaehlerDifferential R (RepresentationCoordinateAlgebra G ι R) →ₗ[RepresentationCoordinateAlgebra G ι R]
    (TrivSqZeroExt.kerIdeal R R)

/-- The genuine cotangent module of the original coordinate algebra represents the original adjoint cocycles at the original representation point. -/
def representationCoordinateCotangentCocycleEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateCotangentMaps ρ ≃ groupCohomology.cocycles₁ (matrixAdjointRep ρ) := by
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  exact (KaehlerDifferential.linearMapEquivDerivation R
    (RepresentationCoordinateAlgebra G ι R) (M := TrivSqZeroExt.kerIdeal R R)).toEquiv.trans
      (representationCoordinateDerivationCocycleEquiv ρ)

/-- For the original finitely generated group, its actual representation coordinate Kähler module is finitely generated over the actual coordinate algebra. -/
theorem representationCoordinateCotangent_finite [Group.FG G] :
    Module.Finite (RepresentationCoordinateAlgebra G ι R)
      (KaehlerDifferential R (RepresentationCoordinateAlgebra G ι R)) := by
  letI := representationCoordinateAlgebra_finiteType (G := G) (ι := ι) (R := R)
  infer_instance

/-- Every original adjoint cocycle is the value of an actual linear map on the genuine coordinate cotangent module. -/
theorem representationCoordinateCotangentCocycleEquiv_surjective
    (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (representationCoordinateCotangentCocycleEquiv ρ) :=
  (representationCoordinateCotangentCocycleEquiv ρ).surjective

end
end Dubon2026
