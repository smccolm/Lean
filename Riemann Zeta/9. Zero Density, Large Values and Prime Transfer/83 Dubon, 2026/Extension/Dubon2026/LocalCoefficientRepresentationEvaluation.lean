import Dubon2026.ResidualRepresentationLocalization
import Dubon2026.ResidualCoefficientCoordinateUnits

/-! # Evaluation of the genuine residual local ring over local coefficient extensions -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- The original coordinate lift to a local coefficient extension has an actual extension from the genuine residual localization. -/
def localizedCoefficientCoordinateMap
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    ResidualRepresentationLocalRing ρ →ₐ[O] A :=
  IsLocalization.liftAlgHom (M := (residualRepresentationCoordinateIdeal ρ).primeCompl)
    (f := f.val) (fun y => localCoefficientCoordinateMap_isUnit ρ e f y.val y.property)

/-- The genuine localized map preserves every value of the original local coefficient coordinate lift. -/
theorem localizedCoefficientCoordinateMap_algebraMap
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e))
    (x : RepresentationCoordinateAlgebra G ι O) :
    localizedCoefficientCoordinateMap ρ e f (algebraMap _ (ResidualRepresentationLocalRing ρ) x) =
      f.val x :=
  IsLocalization.lift_eq _ _

/-- The actual extension of the original local coefficient lift to the residual localization is unique. -/
theorem localizedCoefficientCoordinateMap_unique
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e))
    (h : ResidualRepresentationLocalRing ρ →ₐ[O] A)
    (hh : ∀ x, h (algebraMap _ (ResidualRepresentationLocalRing ρ) x) = f.val x) :
    localizedCoefficientCoordinateMap ρ e f = h := by
  apply IsLocalization.algHom_ext (residualRepresentationCoordinateIdeal ρ).primeCompl
  apply AlgHom.ext
  intro x
  exact (localizedCoefficientCoordinateMap_algebraMap ρ e f x).trans (hh x).symm

/-- The genuine localized universal representation evaluates to the entire original representation over the actual local coefficient extension. -/
theorem localizedCoefficientCoordinateMap_representation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := A)
      (localizedCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)).toRingHom).comp
        (localizedUniversalMatrixRepresentation ρ) = τ.val := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localizedCoefficientCoordinateMap ρ e
    ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)
    (algebraMap _ (ResidualRepresentationLocalRing ρ)
      (representationCoordinateMatrix G ι O g i j)) = (τ.val g).val i j
  rw [localizedCoefficientCoordinateMap_algebraMap]
  exact representationCoordinateEvaluation_entry τ.val g i j

end
end Dubon2026
