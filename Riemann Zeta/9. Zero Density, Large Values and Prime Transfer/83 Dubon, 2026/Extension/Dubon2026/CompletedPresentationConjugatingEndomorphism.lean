import Dubon2026.CompletedPresentationUniversality
import Dubon2026.CompletedPresentationTrueResidue
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Actual universal coefficient endomorphisms for whole strictly conjugate representations -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The actual framed universal property is valid for the original target topology after its equality with the true maximal-adic topology is proved and transported explicitly. -/
theorem completedPresentationCoefficient_exists_unique_of_isAdic
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra O A]
    [t : TopologicalSpace A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (σ : H →ₜ* GeneralLinearGroup ι A)
    (hσ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      ((σ.toMonoidHom.comp q.toMonoidHom).comp
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) = ρ) :
    ∃! f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A,
      (∀ h : H, GeneralLinearGroup.map (n := ι) f.toRingHom
        (completedPresentationRepresentation ρ H q hq h) = σ h) ∧
      Continuous f ∧
      ((localCoefficientReduction e).comp f).comp
        (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)) =
          completedResidualRepresentationEvaluation ρ := by
  change t = (IsLocalRing.maximalIdeal A).adicTopology at hA
  subst t
  letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
  exact completedPresentationCoefficient_exists_unique rfl ρ e H q hq σ hσ

/-- Apply the proved original framed universal property to a genuine continuous representation strictly conjugate to the same original universal one, producing an actual continuous endomorphism of its coefficient ring. -/
theorem completedPresentation_conjugating_endomorphism_exists
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    (τ : H →ₜ* GeneralLinearGroup ι (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      τ.toMonoidHom (completedPresentationRepresentation ρ H q hq)) :
    ∃ f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O]
        CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker,
      (∀ h : H, GeneralLinearGroup.map f.toRingHom
        (completedPresentationRepresentation ρ H q hq h) = τ h) ∧ Continuous f := by
  let e := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  have hred := matrixStrictlyConjugate_reduction _ _ _ hτ
  have hτoriginal : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      ((τ.toMonoidHom.comp q.toMonoidHom).comp
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) = ρ := by
    apply MonoidHom.ext
    intro g
    have hr := DFunLike.congr_fun hred (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hentry := congrArg (fun U : GeneralLinearGroup ι
      (IsLocalRing.ResidueField (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) =>
        e (U.val i j)) hr
    change localCoefficientReduction e
      ((completedPresentationRepresentation ρ H q hq
        (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))).val i j) =
      localCoefficientReduction e ((τ (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))).val i j)
      at hentry
    change localCoefficientReduction e
      ((τ (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))).val i j) = (ρ g).val i j
    rw [← hentry, completedPresentationRepresentation_original,
      completedUniversalProfiniteRepresentation_eta]
    change localCoefficientReduction (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
      (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)
        ((completedUniversalMatrixRepresentation ρ g).val i j)) = (ρ g).val i j
    rw [completedPresentationResidueEquiv_original]
    exact congrArg (fun U : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => U.val i j)
      (DFunLike.congr_fun (completedUniversalMatrixRepresentation_reduction ρ) g)
  obtain ⟨f, hf, _hu⟩ := completedPresentationCoefficient_exists_unique_of_isAdic
    hR ρ e H q hq τ hτoriginal
  exact ⟨f, hf.1, hf.2.1⟩

end
end Dubon2026
