import Dubon2026.CoordinateDerivationMatrices

/-! # Actual linearity of the coordinate-derivation and adjoint-cocycle correspondence -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original coordinate-derivation correspondence is an actual linear map into the genuine adjoint cocycle module. -/
def coordinateDerivationCocycleLinearMap (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateDerivations ρ →ₗ[R] groupCohomology.cocycles₁ (matrixAdjointRep ρ) where
  toFun := representationCoordinateDerivationCocycleEquiv ρ
  map_add' d e := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change representationCoordinateDerivationCocycleEquiv ρ (d + e) g =
      representationCoordinateDerivationCocycleEquiv ρ d g +
        representationCoordinateDerivationCocycleEquiv ρ e g
    rw [representationCoordinateDerivationCocycleEquiv_value,
      representationCoordinateDerivationCocycleEquiv_value,
      representationCoordinateDerivationCocycleEquiv_value,
      coordinateDerivationMatrix_add, add_mul]
  map_smul' a d := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change representationCoordinateDerivationCocycleEquiv ρ (a • d) g =
      a • representationCoordinateDerivationCocycleEquiv ρ d g
    rw [representationCoordinateDerivationCocycleEquiv_value,
      representationCoordinateDerivationCocycleEquiv_value, coordinateDerivationMatrix_smul]
    exact smul_mul_assoc a _ _

/-- The original coordinate-derivation and adjoint-cocycle correspondence is a genuine linear equivalence. -/
def coordinateDerivationCocycleLinearEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateDerivations ρ ≃ₗ[R] groupCohomology.cocycles₁ (matrixAdjointRep ρ) :=
  LinearEquiv.ofBijective (coordinateDerivationCocycleLinearMap ρ)
    (representationCoordinateDerivationCocycleEquiv ρ).bijective

/-- The actual linear equivalence retains exactly the original coordinate-cocycle function. -/
theorem coordinateDerivationCocycleLinearEquiv_apply
    (ρ : G →* GeneralLinearGroup ι R) (d : RepresentationCoordinateDerivations ρ) :
    coordinateDerivationCocycleLinearEquiv ρ d =
      representationCoordinateDerivationCocycleEquiv ρ d := rfl

end
end Dubon2026
