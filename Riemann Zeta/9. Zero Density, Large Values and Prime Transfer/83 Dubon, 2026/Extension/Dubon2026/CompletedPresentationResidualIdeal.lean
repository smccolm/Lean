import Dubon2026.CompletedPresentationRelations
import Dubon2026.CompletedProfiniteResidualReduction

/-! # Original residual compatibility makes the actual completed relation quotient proper -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Every genuine residual relation lies in the true maximal ideal of the original completed universal coefficient ring. -/
theorem completedPresentationRelationIdeal_le_maximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) :
    completedPresentationRelationIdeal ρ N ≤
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) := by
  rw [← completedResidualRepresentationEvaluation_ker]
  apply (matrixRepresentationRelationIdeal_le_kernel_iff
    (completedUniversalProfiniteRepresentation ρ).toMonoidHom N
    (completedResidualRepresentationEvaluation ρ).toRingHom).mpr
  rw [completedUniversalProfiniteRepresentation_reduction ρ σ hσ hσeta]
  exact hN

/-- The ideal of all original residual-compatible profinite relations is proper. -/
theorem completedPresentationRelationIdeal_ne_top
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) : completedPresentationRelationIdeal ρ N ≠ ⊤ := by
  intro htop
  have hm := completedPresentationRelationIdeal_le_maximal ρ σ hσ hσeta N hN
  rw [htop, top_le_iff] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal (ResidualRepresentationCompletion ρ)).ne_top hm

/-- The actual completed coefficient quotient of genuine residual-compatible relations is a nontrivial local ring. -/
theorem completedPresentationCoefficientQuotient_isLocalRing
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) : IsLocalRing (CompletedPresentationCoefficientQuotient ρ N) := by
  letI : Nontrivial (CompletedPresentationCoefficientQuotient ρ N) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (completedPresentationRelationIdeal_ne_top ρ σ hσ hσeta N hN)
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N)) Ideal.Quotient.mk_surjective

end
end Dubon2026
