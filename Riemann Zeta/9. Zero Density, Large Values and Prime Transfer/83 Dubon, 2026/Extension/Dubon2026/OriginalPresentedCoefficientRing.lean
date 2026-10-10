import Dubon2026.OriginalPresentedFramedFibers
import Dubon2026.CompletedPresentationTrueResidue

/-! # The genuine complete local coefficient ring of an original presented residual representation -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Restrict the original whole residual representation along the genuine presentation and its original dense abstract group. -/
abbrev originalPresentedResidualRestriction
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  (σ.toMonoidHom.comp q.toMonoidHom).comp
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom

/-- The actual original completed coordinate ring divided by every original profinite presentation relation. -/
abbrev OriginalPresentedCoefficientRing
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  CompletedPresentationCoefficientQuotient
    (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker

/-- The original presentation relations automatically vanish under the actual residual representation, so the genuine coefficient ring is local. -/
theorem originalPresentedCoefficientRing_isLocal
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsLocalRing (OriginalPresentedCoefficientRing H q σ) := by
  apply completedPresentationCoefficientQuotient_isLocalRing
    (originalPresentedResidualRestriction H q σ) (σ.comp q).toMonoidHom
    (σ.comp q).continuous (fun _ => rfl) q.toMonoidHom.ker
  intro x hx
  change σ (q x) = 1
  change q x = 1 at hx
  rw [hx, map_one]

/-- The same actual all-relation coefficient ring is Noetherian and complete, has exactly the original residue field, and carries its genuine maximal-adic topology. -/
theorem originalPresentedCoefficientRing_localData
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     IsNoetherianRing (OriginalPresentedCoefficientRing H q σ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (OriginalPresentedCoefficientRing H q σ))
         (OriginalPresentedCoefficientRing H q σ) ∧
       (inferInstance : TopologicalSpace (OriginalPresentedCoefficientRing H q σ)) =
         (IsLocalRing.maximalIdeal (OriginalPresentedCoefficientRing H q σ)).adicTopology ∧
       ∀ r : ResidualRepresentationCompletion (originalPresentedResidualRestriction H q σ),
         localCoefficientReduction (completedPresentationResidueEquiv
           (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker)
           (Ideal.Quotient.mk (completedPresentationRelationIdeal
             (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) r) =
               completedResidualRepresentationEvaluation (originalPresentedResidualRestriction H q σ) r) := by
  let ρ := originalPresentedResidualRestriction H q σ
  letI := originalPresentedCoefficientRing_isLocal H q σ
  letI := residualRepresentationCompletion_isNoetherian ρ
  letI := residualRepresentationCompletion_compactSpace ρ
  let J := completedPresentationRelationIdeal ρ q.toMonoidHom.ker
  exact ⟨completedPresentationCoefficientQuotient_isNoetherian ρ q.toMonoidHom.ker,
    compactLocalAdicQuotient_maximal_complete J rfl,
    localQuotient_maximal_adicTopology J rfl,
    completedPresentationResidueEquiv_original ρ q.toMonoidHom.ker⟩

/-- The genuine universal representation over this derived complete local ring has exactly the original whole residual representation. -/
theorem originalPresentedCoefficientRing_universal_residue
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction (completedPresentationResidueEquiv
         (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker)).toRingHom).comp
           (completedPresentationRepresentation
             (originalPresentedResidualRestriction H q σ) H q hq) = σ.toMonoidHom) := by
  letI := originalPresentedCoefficientRing_isLocal H q σ
  exact completedPresentationRepresentation_trueResidue
    (originalPresentedResidualRestriction H q σ) H q hq σ (fun _ => rfl)

end
end Dubon2026
