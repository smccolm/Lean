import Dubon2026.ResidualRepresentationLocalization

/-! # The actual residual point of the original localized universal representation -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The original residual evaluation extends to the genuine localization at its literal kernel. -/
def localizedResidualRepresentationEvaluation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    ResidualRepresentationLocalRing ρ →ₐ[O] IsLocalRing.ResidueField O :=
  IsLocalization.liftAlgHom (M := (residualRepresentationCoordinateIdeal ρ).primeCompl)
    (f := representationCoordinateEvaluation (R := O) ρ)
    (fun y => isUnit_iff_ne_zero.mpr y.property)

/-- The actual localized residual evaluation preserves every original coordinate value. -/
theorem localizedResidualRepresentationEvaluation_algebraMap
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (x : RepresentationCoordinateAlgebra G ι O) :
    localizedResidualRepresentationEvaluation ρ
      (algebraMap _ (ResidualRepresentationLocalRing ρ) x) =
        representationCoordinateEvaluation (R := O) ρ x :=
  IsLocalization.lift_eq _ _

/-- The actual localized residual evaluation is onto the true residue field of the original coefficient ring. -/
theorem localizedResidualRepresentationEvaluation_surjective
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Surjective (localizedResidualRepresentationEvaluation ρ) := by
  intro x
  obtain ⟨q, hq⟩ := residualRepresentationCoordinateEvaluation_surjective ρ x
  exact ⟨algebraMap _ (ResidualRepresentationLocalRing ρ) q,
    (localizedResidualRepresentationEvaluation_algebraMap ρ q).trans hq⟩

/-- The kernel of the actual residual evaluation is exactly the maximal ideal of the original residual localization. -/
theorem localizedResidualRepresentationEvaluation_ker
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom =
      IsLocalRing.maximalIdeal (ResidualRepresentationLocalRing ρ) :=
  IsLocalRing.ker_eq_maximalIdeal (R := ResidualRepresentationLocalRing ρ)
    (K := IsLocalRing.ResidueField O)
    (localizedResidualRepresentationEvaluation ρ).toRingHom
    (localizedResidualRepresentationEvaluation_surjective ρ)

/-- The entire genuine localized universal representation reduces to the original residual representation. -/
theorem localizedUniversalMatrixRepresentation_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom).comp
      (localizedUniversalMatrixRepresentation ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localizedResidualRepresentationEvaluation ρ
    (algebraMap _ (ResidualRepresentationLocalRing ρ)
      (representationCoordinateMatrix G ι O g i j)) = (ρ g).val i j
  rw [localizedResidualRepresentationEvaluation_algebraMap]
  exact representationCoordinateEvaluation_entry ρ g i j

end
end Dubon2026
