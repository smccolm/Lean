import Dubon2026.SourceCohomologyTracePullbackCoefficients

/-! DUB-17/18 -> all-weight adic association -> Gamma1 transfer/Hecke
compatibility -> native H1 trace base change. The original Shapiro
restriction/evaluation theorem and actual coinduced-function pullback
supply the comparison, without a separately assumed Shapiro naturality law. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R D G : Type} [CommRing R] [Group D] [Group G]
  (A : Rep.{0} R G) (φ : D →* G) (S : Subgroup G)

/-- Native Shapiro commutes with actual group pullback and the literal
pullback of coinduced coefficient functions. -/
theorem sourceShapiroH1_pullback_naturality :
    groupCohomology.map φ (sourceCoinducedTracePullback A φ S) 1 ≫
      (groupCohomology.coindIso (Rep.res (S.comap φ).subtype (Rep.res φ A)) 1).hom =
    (groupCohomology.coindIso (Rep.res S.subtype A) 1).hom ≫
      groupCohomology.map (sourceTracePullbackSubgroupHom φ S)
        (𝟙 (Rep.res (S.comap φ).subtype (Rep.res φ A))) 1 := by
  let evS : Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype A)) ⟶
      Rep.res S.subtype A :=
    (Rep.resCoindHomEquiv S.subtype
      (Rep.coind S.subtype (Rep.res S.subtype A)) (Rep.res S.subtype A)).symm (𝟙 _)
  let evT : Rep.res (S.comap φ).subtype
      (Rep.coind (S.comap φ).subtype (Rep.res (S.comap φ).subtype (Rep.res φ A))) ⟶
      Rep.res (S.comap φ).subtype (Rep.res φ A) :=
    (Rep.resCoindHomEquiv (S.comap φ).subtype
      (Rep.coind (S.comap φ).subtype (Rep.res (S.comap φ).subtype (Rep.res φ A)))
      (Rep.res (S.comap φ).subtype (Rep.res φ A))).symm (𝟙 _)
  have hS := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    (Rep.res S.subtype A) 1 evS (fun _ => rfl)
  have hT := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    (Rep.res (S.comap φ).subtype (Rep.res φ A)) 1 evT (fun _ => rfl)
  rw [hS, hT]
  simp only [← groupCohomology.map_comp]
  congr 1
  apply Rep.hom_ext
  ext f
  exact sourceCoinducedTracePullback_eval_one A φ S f

end
end Dubon2026
