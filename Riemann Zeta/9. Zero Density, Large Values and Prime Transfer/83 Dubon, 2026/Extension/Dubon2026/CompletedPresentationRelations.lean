import Dubon2026.MatrixRelationQuotientTopology
import Dubon2026.MatrixRelationCoefficientFactors
import Dubon2026.CompletedUniversalProfiniteRepresentation
import Dubon2026.NoetherianAdicCompletion

/-! # All original profinite relations in the genuine completed coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The ideal of every original profinite relation in the actual completed universal coefficient ring. -/
def completedPresentationRelationIdeal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :
    Ideal (ResidualRepresentationCompletion ρ) :=
  matrixRepresentationRelationIdeal (completedUniversalProfiniteRepresentation ρ).toMonoidHom N

/-- The genuine original completed coefficient quotient imposes all original profinite relations. -/
abbrev CompletedPresentationCoefficientQuotient
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :=
  ResidualRepresentationCompletion ρ ⧸ completedPresentationRelationIdeal ρ N

/-- All actual profinite matrix relations generate a closed ideal in the original completed ring. -/
theorem completedPresentationRelationIdeal_isClosed
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :
    IsClosed (completedPresentationRelationIdeal ρ N : Set (ResidualRepresentationCompletion ρ)) := by
  letI := residualRepresentationCompletion_isNoetherian ρ
  letI := residualRepresentationCompletion_compactSpace ρ
  exact IsNoetherianRing.isClosed_ideal _

/-- The actual completed coefficient quotient by every profinite relation remains Noetherian. -/
theorem completedPresentationCoefficientQuotient_isNoetherian
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :
    IsNoetherianRing (CompletedPresentationCoefficientQuotient ρ N) := by
  letI := residualRepresentationCompletion_isNoetherian ρ
  exact isNoetherianRing_of_surjective (ResidualRepresentationCompletion ρ)
    (CompletedPresentationCoefficientQuotient ρ N)
    (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N))
    Ideal.Quotient.mk_surjective

/-- The actual quotient by all original profinite relations is complete and separated for its original image maximal ideal. -/
theorem completedPresentationCoefficientQuotient_isAdicComplete
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :
    IsAdicComplete
      ((IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).map
        (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N)))
      (CompletedPresentationCoefficientQuotient ρ N) := by
  letI := residualRepresentationCompletion_isNoetherian ρ
  letI := residualRepresentationCompletion_compactSpace ρ
  exact compactNoetherianAdicQuotient_complete
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))
    (completedPresentationRelationIdeal ρ N) rfl

/-- The genuine completed universal matrices descend continuously through the entire original profinite relation quotient. -/
theorem completedPresentationRepresentation_continuous
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) [N.Normal] :
    Continuous (matrixRelationQuotientRepresentation
      (completedUniversalProfiniteRepresentation ρ).toMonoidHom N) :=
  matrixRelationQuotientRepresentation_continuous
    (completedUniversalProfiniteRepresentation ρ).toMonoidHom
    (completedUniversalProfiniteRepresentation ρ).continuous N

end
end Dubon2026
