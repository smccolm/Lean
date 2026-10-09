import Dubon2026.LocalizedRepresentationEvaluation
import Dubon2026.LocalizedResidualEvaluation

/-! # Actual integral representation fibers of the original residual local ring -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The literal fiber of maps from the genuine residual localization reducing to its original residual point. -/
abbrev LocalizedIntegralCoordinateFiber
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  {f : ResidualRepresentationLocalRing ρ →ₐ[O] O //
    (Algebra.ofId O (IsLocalRing.ResidueField O)).comp f =
      localizedResidualRepresentationEvaluation ρ}

/-- The actual extension of the original integral coordinate lift preserves the entire original residual evaluation. -/
theorem localizedIntegralCoordinateMap_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O))) :
    (Algebra.ofId O (IsLocalRing.ResidueField O)).comp (localizedIntegralCoordinateMap ρ f) =
      localizedResidualRepresentationEvaluation ρ := by
  apply IsLocalization.algHom_ext (residualRepresentationCoordinateIdeal ρ).primeCompl
  apply AlgHom.ext
  intro x
  change (Algebra.ofId O (IsLocalRing.ResidueField O))
    (localizedIntegralCoordinateMap ρ f (algebraMap _ (ResidualRepresentationLocalRing ρ) x)) =
      localizedResidualRepresentationEvaluation ρ (algebraMap _ (ResidualRepresentationLocalRing ρ) x)
  rw [localizedIntegralCoordinateMap_algebraMap, localizedResidualRepresentationEvaluation_algebraMap]
  exact DFunLike.congr_fun f.property x

/-- Restriction to the original coordinates and unique localization extension identify the entire actual integral coordinate fibers. -/
def localizedIntegralCoordinateFiberEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    LocalizedIntegralCoordinateFiber ρ ≃
      RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)) where
  toFun f := ⟨f.val.comp (Algebra.algHom O (RepresentationCoordinateAlgebra G ι O)
    (ResidualRepresentationLocalRing ρ)), by
      apply AlgHom.ext
      intro x
      have hf := DFunLike.congr_fun f.property
        (algebraMap _ (ResidualRepresentationLocalRing ρ) x)
      exact hf.trans (localizedResidualRepresentationEvaluation_algebraMap ρ x)⟩
  invFun f := ⟨localizedIntegralCoordinateMap ρ f, localizedIntegralCoordinateMap_reduction ρ f⟩
  left_inv f := by
    apply Subtype.ext
    exact localizedIntegralCoordinateMap_unique ρ _ f.val (fun _ => rfl)
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    exact localizedIntegralCoordinateMap_algebraMap ρ f

/-- The actual original residual local ring represents exactly the original integral matrix lifts in this coefficient ring. -/
def localizedIntegralRepresentationFiberEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    LocalizedIntegralCoordinateFiber ρ ≃
      MatrixRepresentationFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)) :=
  (localizedIntegralCoordinateFiberEquiv ρ).trans
    (representationCoordinateFiberEquiv ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))

/-- The whole original representation returned by the actual localized fiber equivalence is evaluation of the genuine localized universal representation. -/
theorem localizedIntegralRepresentationFiberEquiv_apply
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : LocalizedIntegralCoordinateFiber ρ) :
    (localizedIntegralRepresentationFiberEquiv ρ f).val =
      (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := O)
        f.val.toRingHom).comp (localizedUniversalMatrixRepresentation ρ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

end
end Dubon2026
