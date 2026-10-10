import Dubon2026.ProfiniteRelationCoefficientUniversality
import Dubon2026.CompletedPresentationRepresentation

/-! # The genuine continuous coefficient universal property for an original profinite presentation -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Every genuine continuous lift of the original residual representation is obtained from the actual completed all-relation coefficient quotient by one unique continuous residue-preserving coefficient map. -/
theorem completedPresentationCoefficient_exists_unique
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (σ : H →ₜ* GeneralLinearGroup ι A)
    (hσ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction (σ.comp q)) = ρ) :
    ∃! f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A,
      (∀ h : H, GeneralLinearGroup.map (n := ι) f.toRingHom
        (completedPresentationRepresentation ρ H q hq h) = σ h) ∧
      Continuous f ∧
      ((localCoefficientReduction e).comp f).comp
        (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)) =
          completedResidualRepresentationEvaluation ρ := by
  let τ := σ.comp q
  have hN : q.toMonoidHom.ker ≤ τ.toMonoidHom.ker := by
    intro g hg
    change σ (q g) = 1
    rw [show q g = 1 from hg, map_one]
  let f := profiniteRelationCoefficientMap hA ρ e τ hσ q.toMonoidHom.ker hN
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    obtain ⟨g, rfl⟩ := hq h
    rw [completedPresentationRepresentation_original]
    exact profiniteRelationCoefficientMap_entire hA ρ e τ hσ q.toMonoidHom.ker hN g
  · exact profiniteRelationCoefficientMap_continuous hA ρ e τ hσ q.toMonoidHom.ker hN
  · apply AlgHom.ext
    intro r
    exact profiniteRelationCoefficientMap_reduction hA ρ e τ hσ q.toMonoidHom.ker hN r
  · intro a ha
    apply profiniteRelationCoefficientMap_unique hA ρ e τ hσ q.toMonoidHom.ker hN a
    intro g
    rw [← completedPresentationRepresentation_original ρ H q hq]
    exact ha.1 (q g)

end
end Dubon2026
