import Dubon2026.OriginalPresentedCoefficientRing

/-! # Compact Hausdorff topology of the actual original coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]

/-- The original relation quotient is compact in its actual quotient topology. -/
theorem originalPresentedCoefficientRing_compactSpace
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompactSpace (OriginalPresentedCoefficientRing H q σ) := by
  let ρ := originalPresentedResidualRestriction H q σ
  letI := residualRepresentationCompletion_compactSpace ρ
  exact inferInstanceAs (CompactSpace (ResidualRepresentationCompletion ρ ⧸
    completedPresentationRelationIdeal ρ q.toMonoidHom.ker))

/-- The actual Noetherian relation ideal is closed, so the original quotient topology is Hausdorff. -/
theorem originalPresentedCoefficientRing_t2Space
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    T2Space (OriginalPresentedCoefficientRing H q σ) := by
  let ρ := originalPresentedResidualRestriction H q σ
  letI := residualRepresentationCompletion_compactSpace ρ
  letI := residualRepresentationCompletion_isNoetherian ρ
  exact compactNoetherianQuotient_t2Space (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)

end
end Dubon2026
