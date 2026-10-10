import Dubon2026.CompletedPresentationRelations

/-! # The actual universal matrix representation of the original presented profinite group -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original whole profinite group acts through the genuine completed coordinate quotient by its entire presentation kernel. -/
def completedPresentationRepresentation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) :
    H →* GeneralLinearGroup ι (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker) :=
  (matrixRelationQuotientRepresentation (completedUniversalProfiniteRepresentation ρ).toMonoidHom
    q.toMonoidHom.ker).comp
      (QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hq).symm.toMonoidHom

/-- The actual presented-group representation has exactly the original universal matrix at every original presentation value. -/
theorem completedPresentationRepresentation_original
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    completedPresentationRepresentation ρ H q hq (q g) =
      GeneralLinearGroup.map (n := ι)
        (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ q.toMonoidHom.ker))
        (completedUniversalProfiniteRepresentation ρ g) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hq
  have he : e.symm (q g) = QuotientGroup.mk' q.toMonoidHom.ker g :=
    e.symm_apply_eq.mpr rfl
  change matrixRelationQuotientRepresentation
    (completedUniversalProfiniteRepresentation ρ).toMonoidHom q.toMonoidHom.ker (e.symm (q g)) = _
  rw [he]
  rfl

/-- The genuine presented-group universal representation is continuous in the original group and coefficient quotient topologies. -/
theorem completedPresentedGroupRepresentation_continuous
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) : Continuous (completedPresentationRepresentation ρ H q hq) := by
  apply (IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
  have hm : Continuous (GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ q.toMonoidHom.ker))) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp
      (continuous_apply_apply i j)
  have he : (completedPresentationRepresentation ρ H q hq) ∘ q =
      (GeneralLinearGroup.map (n := ι)
        (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ q.toMonoidHom.ker))) ∘
        (completedUniversalProfiniteRepresentation ρ) :=
    funext (completedPresentationRepresentation_original ρ H q hq)
  rw [he]
  exact hm.comp (completedUniversalProfiniteRepresentation ρ).continuous

end
end Dubon2026
