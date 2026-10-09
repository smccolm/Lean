import Dubon2026.CompletedResidualRepresentation
import Dubon2026.AdicCompletionEvaluationKernels
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # The genuine local structure of the original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The genuine completed residual kernel is the extension of the original residual kernel in the original local ring. -/
theorem completedResidualRepresentationEvaluation_kernel_image
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    RingHom.ker (completedResidualRepresentationEvaluation ρ).toRingHom =
      (RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom).map
        (algebraMap (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ)) := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  let kernelEquality := adicCompletion_kerProj_kernel (O := O)
    (R := ResidualRepresentationLocalRing ρ) (A := IsLocalRing.ResidueField O)
    (localizedResidualRepresentationEvaluation ρ)
    (localizedResidualRepresentationEvaluation_surjective ρ)
    ((isNoetherianRing_iff_ideal_fg _).mp inferInstance _)
  exact kernelEquality

/-- The genuine original residual completion is complete with respect to the kernel of its actual completed residual evaluation. -/
theorem completedResidualRepresentationEvaluation_isAdicComplete
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsAdicComplete (RingHom.ker (completedResidualRepresentationEvaluation ρ).toRingHom)
      (ResidualRepresentationCompletion ρ) := by
  rw [completedResidualRepresentationEvaluation_kernel_image]
  let comparison := IsAdicComplete.map_algebraMap_iff (R := ResidualRepresentationLocalRing ρ)
    (S := ResidualRepresentationCompletion ρ) (M := ResidualRepresentationCompletion ρ)
    (I := RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
  exact comparison.mpr (residualRepresentationCompletion_isAdicComplete ρ)

/-- The actual original residual completion is a genuine local ring, derived from its maximal residual kernel and proved adic completeness. -/
instance residualRepresentationCompletionLocalRing
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsLocalRing (ResidualRepresentationCompletion ρ) := by
  let J := RingHom.ker (completedResidualRepresentationEvaluation ρ).toRingHom
  letI : J.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (completedResidualRepresentationEvaluation ρ).toRingHom
    (completedResidualRepresentationEvaluation_surjective ρ)
  letI : IsAdicComplete J (ResidualRepresentationCompletion ρ) :=
    completedResidualRepresentationEvaluation_isAdicComplete ρ
  exact isLocalRing_of_isAdicComplete_maximal J

/-- The kernel of the actual completed residual point is exactly the true maximal ideal of the original completed ring. -/
theorem completedResidualRepresentationEvaluation_ker
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    RingHom.ker (completedResidualRepresentationEvaluation ρ).toRingHom =
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) :=
  IsLocalRing.ker_eq_maximalIdeal (R := ResidualRepresentationCompletion ρ)
    (K := IsLocalRing.ResidueField O) (completedResidualRepresentationEvaluation ρ).toRingHom
    (completedResidualRepresentationEvaluation_surjective ρ)

/-- The genuine original residual local ring completion is complete at its own actual maximal ideal. -/
theorem residualRepresentationCompletion_completeLocal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))
      (ResidualRepresentationCompletion ρ) := by
  rw [← completedResidualRepresentationEvaluation_ker]
  exact completedResidualRepresentationEvaluation_isAdicComplete ρ

end
end Dubon2026
