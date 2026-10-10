import Dubon2026.CompletedPresentationResidualIdeal
import Dubon2026.CompletedResidualField
import Dubon2026.LocalQuotientAdicTopology

/-! # Actual complete local coefficient data for all original residual relations -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- All original residual-compatible profinite relations yield a genuine Noetherian complete local coefficient quotient, with its literal maximal-adic topology and original residue field. Locality is derived from those relations, not assumed for the quotient. -/
theorem completedPresentationCoefficientQuotient_localData
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) :
    ∃ hlocal : IsLocalRing (CompletedPresentationCoefficientQuotient ρ N),
      (letI := hlocal
       ∃ e : IsLocalRing.ResidueField (CompletedPresentationCoefficientQuotient ρ N) ≃ₐ[O]
           IsLocalRing.ResidueField O,
         IsNoetherianRing (CompletedPresentationCoefficientQuotient ρ N) ∧
         IsAdicComplete (IsLocalRing.maximalIdeal (CompletedPresentationCoefficientQuotient ρ N))
           (CompletedPresentationCoefficientQuotient ρ N) ∧
         (inferInstance : TopologicalSpace (CompletedPresentationCoefficientQuotient ρ N)) =
           (IsLocalRing.maximalIdeal (CompletedPresentationCoefficientQuotient ρ N)).adicTopology ∧
         ∀ r : ResidualRepresentationCompletion ρ,
           e (IsLocalRing.residue _ (Ideal.Quotient.mk
             (completedPresentationRelationIdeal ρ N) r)) =
             completedResidualRepresentationEvaluation ρ r) := by
  letI := completedPresentationCoefficientQuotient_isLocalRing ρ σ hσ hσeta N hN
  letI := residualRepresentationCompletion_isNoetherian ρ
  letI := residualRepresentationCompletion_compactSpace ρ
  let J := completedPresentationRelationIdeal ρ N
  let e := (localQuotientResidueAlgEquiv (O := O) J).symm.trans
    (completedResidualFieldEquiv ρ)
  refine ⟨inferInstance, e, completedPresentationCoefficientQuotient_isNoetherian ρ N,
    compactLocalAdicQuotient_maximal_complete J rfl,
    localQuotient_maximal_adicTopology J rfl, ?_⟩
  intro r
  change completedResidualFieldEquiv ρ
    ((localQuotientResidueAlgEquiv (O := O) J).symm
      (IsLocalRing.residue _ (Ideal.Quotient.mk J r))) = _
  rw [← localQuotientResidueAlgEquiv_residue (O := O) J r, AlgEquiv.symm_apply_apply]
  exact completedResidualFieldEquiv_residue ρ r

end
end Dubon2026
