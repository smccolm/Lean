import Dubon2026.CoordinateTangentCohomology
import Dubon2026.SymmetricCoordinateDerivations

/-! # Actual symmetric tangent classes vanish on the original cohomology kernel -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R : Type} [Group G] [CommRing R]

/-- The canonical scalar structure on the original coordinate derivations, with the genuine representation-point action made explicit. -/
instance representationCoordinateDerivationsModule {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : G →* GeneralLinearGroup ι R) : Module R (RepresentationCoordinateDerivations ρ) := by
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  letI : IsScalarTower R (RepresentationCoordinateAlgebra G ι R) (DualNumber R) :=
    IsScalarTower.of_algHom (representationCoordinateConstantLift ρ)
  let moduleStructure := Derivation.instModule (R := R)
    (A := RepresentationCoordinateAlgebra G ι R) (M := TrivSqZeroExt.kerIdeal R R) (S := R)
  exact moduleStructure

/-- The genuine symmetric derivative followed by the original target adjoint class is a linear map on actual coordinate tangents. -/
def symmetricTangentCohomologyLift (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    RepresentationCoordinateDerivations ρ →ₗ[R]
      groupCohomology.H1 (matrixAdjointRep (symmetricMatrixRepresentation n ρ)) :=
  (coordinateTangentCohomologyMap (symmetricMatrixRepresentation n ρ)).comp
    (symmetricCoordinateDerivationMap n ρ)

/-- The actual symmetric tangent class kills the whole kernel of the original adjoint class map, as a consequence of genuine strict-conjugacy preservation. -/
theorem symmetricTangentCohomologyLift_ker (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    LinearMap.ker (coordinateTangentCohomologyMap ρ) ≤
      LinearMap.ker (symmetricTangentCohomologyLift n ρ) := by
  intro d hd
  have he : coordinateTangentCohomologyMap ρ d = coordinateTangentCohomologyMap ρ 0 := by
    simpa only [map_zero] using hd
  have hc := (coordinateTangentCohomologyMap_eq_iff ρ d 0).mp he
  have hs := symmetricFirstOrderLift_strictlyConjugate n ρ _ _ hc
  rw [← symmetricCoordinateDerivationMap_firstOrder n ρ d,
    ← symmetricCoordinateDerivationMap_firstOrder n ρ 0] at hs
  have hclass := (coordinateTangentCohomologyMap_eq_iff
    (symmetricMatrixRepresentation n ρ) (symmetricCoordinateDerivationMap n ρ d)
      (symmetricCoordinateDerivationMap n ρ 0)).mpr hs
  change coordinateTangentCohomologyMap (symmetricMatrixRepresentation n ρ)
    (symmetricCoordinateDerivationMap n ρ d) = 0
  simpa only [map_zero] using hclass

end
end Dubon2026
