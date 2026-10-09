import Dubon2026.CompletedRepresentationUniqueness
import Dubon2026.CompletedResidualLocalRing

/-! # Genuine maximal ideals and reduction of original completed coefficient maps -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The original completed coefficient map carries the true completed maximal ideal into the true coefficient maximal ideal. -/
theorem completedLocalCoefficientCoordinateMap_maximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ≤
      Ideal.comap (completedLocalCoefficientCoordinateMap ρ e f).toRingHom
        (IsLocalRing.maximalIdeal A) := by
  rw [← completedResidualRepresentationEvaluation_ker,
    completedResidualRepresentationEvaluation_kernel_image]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change completedLocalCoefficientCoordinateMap ρ e f
    (algebraMap _ (ResidualRepresentationCompletion ρ) x) ∈ IsLocalRing.maximalIdeal A
  rw [completedLocalCoefficientCoordinateMap_of]
  exact localizedCoefficientCoordinateMap_ideal ρ e f hx

/-- The original completed coefficient map preserves the entire genuine residual point. -/
theorem completedLocalCoefficientCoordinateMap_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    (localCoefficientReduction e).comp (completedLocalCoefficientCoordinateMap ρ e f) =
      completedResidualRepresentationEvaluation ρ := by
  let I := RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom
  letI := residualRepresentationLocalRing_isNoetherian ρ
  have finiteKernel : I.FG :=
    (isNoetherianRing_iff_ideal_fg (ResidualRepresentationLocalRing ρ)).mp inferInstance I
  let mapsComparison := adicCompletion_algHom_ext (O := O)
    (R := ResidualRepresentationLocalRing ρ) (A := IsLocalRing.ResidueField O) I finiteKernel
    (⊥ : Ideal (IsLocalRing.ResidueField O))
  let comparison := mapsComparison
    ((localCoefficientReduction e).comp (completedLocalCoefficientCoordinateMap ρ e f))
    (completedResidualRepresentationEvaluation ρ)
  apply comparison
  · intro x hx
    change localCoefficientReduction e (completedLocalCoefficientCoordinateMap ρ e f x) = 0
    apply (localCoefficientReduction_eq_zero_iff e _).mpr
    apply completedLocalCoefficientCoordinateMap_maximal ρ e f
    rw [← completedResidualRepresentationEvaluation_ker,
      completedResidualRepresentationEvaluation_kernel_image]
    exact hx
  · intro x hx
    change completedResidualRepresentationEvaluation ρ x = 0
    change x ∈ RingHom.ker (completedResidualRepresentationEvaluation ρ).toRingHom
    rw [completedResidualRepresentationEvaluation_kernel_image]
    exact hx
  · intro x
    change localCoefficientReduction e (completedLocalCoefficientCoordinateMap ρ e f
      (algebraMap _ (ResidualRepresentationCompletion ρ) x)) =
        completedResidualRepresentationEvaluation ρ
          (algebraMap _ (ResidualRepresentationCompletion ρ) x)
    rw [completedLocalCoefficientCoordinateMap_of, completedResidualRepresentationEvaluation_of]
    exact DFunLike.congr_fun (localizedCoefficientCoordinateMap_reduction ρ e f) x

end
end Dubon2026
