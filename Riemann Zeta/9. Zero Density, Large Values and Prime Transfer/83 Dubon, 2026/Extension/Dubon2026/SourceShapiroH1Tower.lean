import Dubon2026.SourceCoinducedTowerFunctions
import Dubon2026.OriginalShapiroRestriction

/-! DUB-17/18 -> actual all-weight association -> Gamma1 Hecke-compatible
surjective transfer -> composition of native H1 traces. The existing
literal restriction/evaluation formula identifies the two Shapiro maps. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  (A : Rep.{0} R G) (S T : Subgroup G) (hST : S ≤ T)

/-- Flattening the genuine coinduced tower and applying the original
Shapiro map equals the two successive native Shapiro maps, with the
literal nested subgroup reindexing retained. -/
theorem sourceShapiroH1_tower :
    groupCohomology.map (MonoidHom.id G) (sourceCoinducedTowerFlatten A S T hST) 1 ≫
      (groupCohomology.coindIso (Rep.res S.subtype A) 1).hom ≫
        groupCohomology.map (Subgroup.subgroupOfEquivOfLe hST).toMonoidHom
          (𝟙 (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) 1 =
    (groupCohomology.coindIso
      (Rep.coind (S.subgroupOf T).subtype
        (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) 1).hom ≫
      (groupCohomology.coindIso
        (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)) 1).hom := by
  let B := Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)
  let C := Rep.coind (S.subgroupOf T).subtype B
  let evS : Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype A)) ⟶
      Rep.res S.subtype A :=
    (Rep.resCoindHomEquiv S.subtype
      (Rep.coind S.subtype (Rep.res S.subtype A)) (Rep.res S.subtype A)).symm (𝟙 _)
  let evT : Rep.res T.subtype (Rep.coind T.subtype C) ⟶ C :=
    (Rep.resCoindHomEquiv T.subtype (Rep.coind T.subtype C) C).symm (𝟙 _)
  let evST : Rep.res (S.subgroupOf T).subtype C ⟶ B :=
    (Rep.resCoindHomEquiv (S.subgroupOf T).subtype C B).symm (𝟙 _)
  have hS := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    (Rep.res S.subtype A) 1 evS (fun _ => rfl)
  have hT := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    C 1 evT (fun _ => rfl)
  have hST' := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    B 1 evST (fun _ => rfl)
  rw [hS, hT, hST']
  simp only [← groupCohomology.map_comp]
  congr 1

end
end Dubon2026
