import Dubon2026.ProfiniteCoefficientEvaluation
import Dubon2026.CompletedPresentationRelations

/-! # Genuine coefficient universality after all original profinite relations -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The actual coefficient evaluation of an original continuous lift killing all original relations. -/
def profiniteRelationCoefficientMap
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker) : CompletedPresentationCoefficientQuotient ρ N →ₐ[O] A := by
  let f := completedCoefficientMapOfProfiniteLift ρ e τ hτ
  have hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp
      (completedUniversalProfiniteRepresentation ρ).toMonoidHom).ker := by
    rw [completedCoefficientMapOfProfiniteLift_entire hA ρ e τ hτ]
    exact hN
  exact matrixRelationCoefficientMap
    (completedUniversalProfiniteRepresentation ρ).toMonoidHom N f hf

/-- The genuine all-relation coefficient factor retains every original completed coefficient value. -/
theorem profiniteRelationCoefficientMap_mk
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker) (r : ResidualRepresentationCompletion ρ) :
    profiniteRelationCoefficientMap hA ρ e τ hτ N hN
      (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N) r) =
        completedCoefficientMapOfProfiniteLift ρ e τ hτ r := rfl

/-- The genuine coefficient map on the all-relation quotient is continuous in the original quotient topology. -/
theorem profiniteRelationCoefficientMap_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker) : Continuous (profiniteRelationCoefficientMap hA ρ e τ hτ N hN) := by
  apply (QuotientRing.isOpenQuotientMap_mk
    (completedPresentationRelationIdeal ρ N)).isQuotientMap.continuous_iff.mpr
  exact (completedCoefficientMapOfProfiniteLift_uniformContinuous hA ρ e τ hτ).continuous

/-- The actual all-relation coefficient factor preserves the original residue evaluation on every coefficient. -/
theorem profiniteRelationCoefficientMap_reduction
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker) (r : ResidualRepresentationCompletion ρ) :
    localCoefficientReduction e (profiniteRelationCoefficientMap hA ρ e τ hτ N hN
      (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N) r)) =
        completedResidualRepresentationEvaluation ρ r := by
  rw [profiniteRelationCoefficientMap_mk]
  exact DFunLike.congr_fun (completedCoefficientMapOfProfiniteLift_reduction ρ e τ hτ) r

/-- Evaluation of every original whole profinite matrix is exact after imposing all actual relations. -/
theorem profiniteRelationCoefficientMap_entire
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker) (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    GeneralLinearGroup.map (n := ι) (profiniteRelationCoefficientMap hA ρ e τ hτ N hN).toRingHom
      (GeneralLinearGroup.map (n := ι)
        (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N))
        (completedUniversalProfiniteRepresentation ρ g)) = τ g := by
  change GeneralLinearGroup.map (n := ι)
    (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom
    (completedUniversalProfiniteRepresentation ρ g) = τ g
  exact DFunLike.congr_fun (completedCoefficientMapOfProfiniteLift_entire hA ρ e τ hτ) g

/-- All original continuous matrix values uniquely determine the actual map out of the entire relation quotient. -/
theorem profiniteRelationCoefficientMap_unique
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker)
    (f : CompletedPresentationCoefficientQuotient ρ N →ₐ[O] A)
    (hf : ∀ g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G),
      GeneralLinearGroup.map (n := ι) f.toRingHom
        (GeneralLinearGroup.map (n := ι)
          (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N))
          (completedUniversalProfiniteRepresentation ρ g)) = τ g) :
    f = profiniteRelationCoefficientMap hA ρ e τ hτ N hN := by
  let fc := f.comp (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal ρ N))
  have hfc := completedCoefficientMapOfProfiniteLift_unique ρ e τ hτ fc
    (MonoidHom.ext hf)
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (DFunLike.congr_fun hfc r).symm

end
end Dubon2026
