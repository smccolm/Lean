import Dubon2026.ResidualRepresentationLocalization
import Dubon2026.ResidualCoordinateLocalUnits

/-! # Actual integral representation evaluation from the original residual localization -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The actual original integral coordinate lift extends to its genuine residual localization because every original denominator maps to a unit. -/
def localizedIntegralCoordinateMap
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O))) :
    ResidualRepresentationLocalRing ρ →ₐ[O] O :=
  IsLocalization.liftAlgHom (M := (residualRepresentationCoordinateIdeal ρ).primeCompl)
    (f := f.val) (fun y => integralCoordinateMap_isUnit ρ f y.val y.property)

/-- The actual localized integral map agrees with every original coordinate value. -/
theorem localizedIntegralCoordinateMap_algebraMap
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))
    (x : RepresentationCoordinateAlgebra G ι O) :
    localizedIntegralCoordinateMap ρ f (algebraMap _ (ResidualRepresentationLocalRing ρ) x) =
      f.val x :=
  IsLocalization.lift_eq _ _

/-- The extension of the actual original integral coordinate map to its residual localization is unique. -/
theorem localizedIntegralCoordinateMap_unique
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))
    (h : ResidualRepresentationLocalRing ρ →ₐ[O] O)
    (hh : ∀ x, h (algebraMap _ (ResidualRepresentationLocalRing ρ) x) = f.val x) :
    localizedIntegralCoordinateMap ρ f = h := by
  apply IsLocalization.algHom_ext (residualRepresentationCoordinateIdeal ρ).primeCompl
  apply AlgHom.ext
  intro x
  exact (localizedIntegralCoordinateMap_algebraMap ρ f x).trans (hh x).symm

/-- Evaluation of the entire actual localized universal representation recovers the original integral representation itself. -/
theorem localizedIntegralCoordinateMap_representation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : MatrixRepresentationFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O))) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := O)
      (localizedIntegralCoordinateMap ρ
      ((representationCoordinateFiberEquiv ρ (Algebra.ofId O (IsLocalRing.ResidueField O))).symm τ)).toRingHom).comp
        (localizedUniversalMatrixRepresentation ρ) = τ.val := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localizedIntegralCoordinateMap ρ
    ((representationCoordinateFiberEquiv ρ (Algebra.ofId O (IsLocalRing.ResidueField O))).symm τ)
    (algebraMap _ (ResidualRepresentationLocalRing ρ)
      (representationCoordinateMatrix G ι O g i j)) = (τ.val g).val i j
  rw [localizedIntegralCoordinateMap_algebraMap]
  exact representationCoordinateEvaluation_entry τ.val g i j

end
end Dubon2026
