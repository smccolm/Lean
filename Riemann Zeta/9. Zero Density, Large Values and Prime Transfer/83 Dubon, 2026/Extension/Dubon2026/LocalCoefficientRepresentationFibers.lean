import Dubon2026.LocalCoefficientRepresentationEvaluation
import Dubon2026.LocalizedResidualEvaluation

/-! # Genuine representation fibers over local coefficient extensions -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- The literal fiber of maps from the original residual localization to a local coefficient extension with its genuine residue identification. -/
abbrev LocalizedCoefficientCoordinateFiber
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :=
  {f : ResidualRepresentationLocalRing ρ →ₐ[O] A //
    (localCoefficientReduction e).comp f = localizedResidualRepresentationEvaluation ρ}

/-- The entire original residual point is preserved by the actual localized coefficient lift. -/
theorem localizedCoefficientCoordinateMap_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    (localCoefficientReduction e).comp (localizedCoefficientCoordinateMap ρ e f) =
      localizedResidualRepresentationEvaluation ρ := by
  apply IsLocalization.algHom_ext (residualRepresentationCoordinateIdeal ρ).primeCompl
  apply AlgHom.ext
  intro x
  change localCoefficientReduction e
    (localizedCoefficientCoordinateMap ρ e f (algebraMap _ (ResidualRepresentationLocalRing ρ) x)) =
      localizedResidualRepresentationEvaluation ρ (algebraMap _ (ResidualRepresentationLocalRing ρ) x)
  rw [localizedCoefficientCoordinateMap_algebraMap, localizedResidualRepresentationEvaluation_algebraMap]
  exact DFunLike.congr_fun f.property x

/-- Restriction and unique localization extension give inverse maps for the genuine local coefficient coordinate fibers. -/
def localizedCoefficientCoordinateFiberEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    LocalizedCoefficientCoordinateFiber ρ e ≃
      RepresentationCoordinateFiber ρ (localCoefficientReduction e) where
  toFun f := ⟨f.val.comp (Algebra.algHom O (RepresentationCoordinateAlgebra G ι O)
    (ResidualRepresentationLocalRing ρ)), by
      apply AlgHom.ext
      intro x
      have hf := DFunLike.congr_fun f.property
        (algebraMap _ (ResidualRepresentationLocalRing ρ) x)
      exact hf.trans (localizedResidualRepresentationEvaluation_algebraMap ρ x)⟩
  invFun f := ⟨localizedCoefficientCoordinateMap ρ e f, localizedCoefficientCoordinateMap_reduction ρ e f⟩
  left_inv f := by
    apply Subtype.ext
    exact localizedCoefficientCoordinateMap_unique ρ e _ f.val (fun _ => rfl)
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    exact localizedCoefficientCoordinateMap_algebraMap ρ e f

/-- The actual residual local ring represents the original representation lifts to the given genuine local coefficient extension. -/
def localizedCoefficientRepresentationFiberEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    LocalizedCoefficientCoordinateFiber ρ e ≃
      MatrixRepresentationFiber ρ (localCoefficientReduction e) :=
  (localizedCoefficientCoordinateFiberEquiv ρ e).trans
    (representationCoordinateFiberEquiv ρ (localCoefficientReduction e))

/-- The entire original matrix representation in the genuine local coefficient fiber equivalence is actual evaluation of the localized universal representation. -/
theorem localizedCoefficientRepresentationFiberEquiv_apply
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : LocalizedCoefficientCoordinateFiber ρ e) :
    (localizedCoefficientRepresentationFiberEquiv ρ e f).val =
      (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := A)
        f.val.toRingHom).comp (localizedUniversalMatrixRepresentation ρ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

end
end Dubon2026
