import Dubon2026.CompletedPresentationLocalCoefficientData
import Dubon2026.CompletedPresentationRepresentation
import Dubon2026.LocalCoefficientReduction

/-! # The actual original residual representation of the complete local presentation quotient -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original residue-field equivalence of the genuine local all-relation coefficient quotient. -/
def completedPresentationResidueEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ N)] :
    IsLocalRing.ResidueField (CompletedPresentationCoefficientQuotient ρ N) ≃ₐ[O]
      IsLocalRing.ResidueField O :=
  (localQuotientResidueAlgEquiv (O := O) (completedPresentationRelationIdeal ρ N)).symm.trans
    (completedResidualFieldEquiv ρ)

/-- Every original completed coefficient reduces through the actual quotient residue field to its original residual evaluation. -/
theorem completedPresentationResidueEquiv_original
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ N)]
    (r : ResidualRepresentationCompletion ρ) :
    localCoefficientReduction (completedPresentationResidueEquiv ρ N)
      (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N) r) =
        completedResidualRepresentationEvaluation ρ r := by
  change completedResidualFieldEquiv ρ
    ((localQuotientResidueAlgEquiv (O := O) (completedPresentationRelationIdeal ρ N)).symm
      (IsLocalRing.residue _ (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N) r))) = _
  rw [← localQuotientResidueAlgEquiv_residue (O := O)
    (completedPresentationRelationIdeal ρ N) r, AlgEquiv.symm_apply_apply]
  exact completedResidualFieldEquiv_residue ρ r

/-- The original whole presented-group universal representation reduces to the given original residual representation through the quotient's true residue field. -/
theorem completedPresentationRepresentation_trueResidue
    [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσeta : ∀ g, σ (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = ρ g) :
    (GeneralLinearGroup.map (n := ι)
      (localCoefficientReduction (completedPresentationResidueEquiv ρ
        q.toMonoidHom.ker)).toRingHom).comp
        (completedPresentationRepresentation ρ H q hq) = σ.toMonoidHom := by
  have hr := completedUniversalProfiniteRepresentation_reduction ρ
    (σ.comp q).toMonoidHom (σ.comp q).continuous hσeta
  apply MonoidHom.ext
  intro h
  obtain ⟨x, rfl⟩ := hq h
  change GeneralLinearGroup.map (n := ι) _
    (completedPresentationRepresentation ρ H q hq (q x)) = σ (q x)
  rw [completedPresentationRepresentation_original]
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localCoefficientReduction (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
    (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)
      ((completedUniversalProfiniteRepresentation ρ x).val i j)) = (σ (q x)).val i j
  rw [completedPresentationResidueEquiv_original]
  exact congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun hr x)

end
end Dubon2026
