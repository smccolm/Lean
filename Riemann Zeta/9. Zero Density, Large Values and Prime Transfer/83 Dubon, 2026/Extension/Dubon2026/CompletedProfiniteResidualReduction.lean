import Dubon2026.CompletedUniversalProfiniteRepresentation
import Dubon2026.CompletedResidualField
import Dubon2026.AdicPowerQuotientTopology

/-! # The original residue field of the entire completed profinite representation -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The actual completed evaluation into the original coefficient residue field is continuous. -/
theorem completedResidualRepresentationEvaluation_continuous
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Continuous (completedResidualRepresentationEvaluation ρ) := by
  letI : TopologicalSpace (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)) :=
    inferInstanceAs (TopologicalSpace (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)))
  letI : DiscreteTopology (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)) := by
    apply QuotientAddGroup.discreteTopology
      (N := (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).toAddSubgroup)
    simpa only [pow_one] using
      (isAdic_iff.mp (rfl : IsAdic (WithIdeal.i : Ideal (ResidualRepresentationCompletion ρ)))).1 1
  have he : Continuous (completedResidualFieldEquiv ρ) := continuous_of_discreteTopology
  exact he.comp (QuotientRing.isOpenQuotientMap_mk
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))).continuous

/-- Continuity and the original dense abstract group identify the residual reduction on every actual profinite element. -/
theorem completedUniversalProfiniteRepresentation_reduction
    [T2Space (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g) :
    (GeneralLinearGroup.map (n := ι)
      (completedResidualRepresentationEvaluation ρ).toRingHom).comp
        (completedUniversalProfiniteRepresentation ρ).toMonoidHom = σ := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι)
      (completedResidualRepresentationEvaluation ρ).toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (completedResidualRepresentationEvaluation_continuous ρ).comp
      (continuous_apply_apply i j)
  have he := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    (hmap.comp (completedUniversalProfiniteRepresentation ρ).continuous) hσ
    (funext fun g => by
      change GeneralLinearGroup.map (n := ι)
        (completedResidualRepresentationEvaluation ρ).toRingHom
        (completedUniversalProfiniteRepresentation ρ
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = _
      rw [completedUniversalProfiniteRepresentation_eta]
      change _ = σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)
      rw [hσeta]
      exact DFunLike.congr_fun (completedUniversalMatrixRepresentation_reduction ρ) g)
  exact MonoidHom.ext (fun g => congrFun he g)

end
end Dubon2026
