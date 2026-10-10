import Dubon2026.AdicCompletionOriginalDensity
import Dubon2026.CompletedResidualTopology

/-! # Density of the genuine original localized coordinates in their residual completion -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The original localized coordinate ring is dense in the actual completed residual coefficient ring with its genuine maximal-adic topology. -/
theorem residualRepresentationCompletion_original_dense
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    DenseRange (algebraMap (ResidualRepresentationLocalRing ρ)
      (ResidualRepresentationCompletion ρ)) := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  let I := RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hideal : I.map (algebraMap (ResidualRepresentationLocalRing ρ)
      (ResidualRepresentationCompletion ρ)) =
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) :=
    (completedResidualRepresentationEvaluation_kernel_image ρ).symm.trans
      (completedResidualRepresentationEvaluation_ker ρ)
  have htop : IsAdic (I.map (algebraMap (ResidualRepresentationLocalRing ρ)
      (ResidualRepresentationCompletion ρ))) :=
    hideal.symm ▸ (show IsAdic (IsLocalRing.maximalIdeal
      (ResidualRepresentationCompletion ρ)) from rfl)
  let densityForIdeal := adicCompletion_original_dense
    (R := ResidualRepresentationLocalRing ρ) I hI
  exact densityForIdeal htop

end
end Dubon2026
