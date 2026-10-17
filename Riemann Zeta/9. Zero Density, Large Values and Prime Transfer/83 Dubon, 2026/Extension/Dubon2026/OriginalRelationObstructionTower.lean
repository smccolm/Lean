import Dubon2026.OriginalRestrictedRelationObstruction

/-! # The descended relation obstruction uses the original tower presentation

Restrict the canonical relation-sequence diagram once more and use the
proved coefficient connecting naturality. This is the precise comparison
needed for DUB-17's finite descended representative, before local invariants.
It avoids constructing a new free presentation over the infinite group.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G H J : Type} [Group G] [Group H] [Group J]
  (π : G →* H) (τ : H →* J) (B : Rep ℤ J) (C : Rep ℤ H) (D : Rep ℤ G)

/-- The original canonical relation map in a tower preserves the actual
restricted connecting class, for every class over the larger group. -/
theorem originalRestrictedRelation_delta_tower :
    groupCohomology.δ (originalRelationGroupChange_shortExact π (Rep.res τ B)) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map
        ((Rep.resFunctor π).map (originalRelationGroupChange τ B)) =
    groupCohomology.δ (originalRelationGroupChange_shortExact (τ.comp π) B) 1 2 rfl := by
  have h := originalCoefficient_delta_naturality
    ((Rep.resFunctor π).mapShortComplex.map (originalRelationGroupChangeSequenceMap τ B))
    (originalRelationGroupChange_shortExact π (Rep.res τ B))
    (originalRelationGroupChange_shortExact (τ.comp π) B) 1 2 rfl
  change groupCohomology.δ (originalRelationGroupChange_shortExact π (Rep.res τ B)) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map
        ((Rep.resFunctor π).map (originalRelationGroupChange τ B)) =
    (groupCohomology.functor ℤ G 1).map (𝟙 (Rep.res (τ.comp π) B)) ≫
      groupCohomology.δ (originalRelationGroupChange_shortExact (τ.comp π) B) 1 2 rfl at h
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- If the descended relation preserves its actual coefficient values,
its inflated obstruction equals the connecting class of the original
tower presentation under that same relation morphism. -/
theorem originalRelation_obstruction_tower
    (η : originalRelationModule (Rep.res τ B) ⟶ C)
    (j : Rep.res π C ⟶ D)
    (φ : Rep.res (τ.comp π) (originalRelationModule B) ⟶ D)
    (hη : (Rep.resFunctor π).map η ≫ j =
      (Rep.resFunctor π).map (originalRelationGroupChange τ B) ≫ φ) :
    originalRelationExtensionObstruction (Rep.res τ B) C η ≫ groupCohomology.map π j 2 =
      groupCohomology.map π (𝟙 (Rep.res π (Rep.res τ B))) 1 ≫
        groupCohomology.δ (originalRelationGroupChange_shortExact (τ.comp π) B) 1 2 rfl ≫
        (groupCohomology.functor ℤ G 2).map φ := by
  erw [originalRestrictedRelation_obstruction_inflation, hη]
  erw [CategoryTheory.Functor.map_comp]
  have h := congrArg (fun m =>
    groupCohomology.map π (𝟙 (Rep.res π (Rep.res τ B))) 1 ≫ m ≫
      (groupCohomology.functor ℤ G 2).map φ)
    (originalRestrictedRelation_delta_tower π τ B)
  simpa only [Category.assoc] using h

/-- The same finite obstruction comparison followed by an actual map to
the original source presentation. The only compatibility input is the
literal coefficient square, not a cohomology or cup identity. -/
theorem originalRelation_obstruction_tower_presentation
    (Y : ShortComplex (Rep ℤ G)) (hY : Y.ShortExact)
    (d : (originalRelationShortComplex B).map (Rep.resFunctor (τ.comp π)) ⟶ Y)
    (η : originalRelationModule (Rep.res τ B) ⟶ C) (j : Rep.res π C ⟶ D)
    (φ : Y.X₁ ⟶ D)
    (hη : (Rep.resFunctor π).map η ≫ j =
      (Rep.resFunctor π).map (originalRelationGroupChange τ B) ≫ d.τ₁ ≫ φ) :
    originalRelationExtensionObstruction (Rep.res τ B) C η ≫ groupCohomology.map π j 2 =
      groupCohomology.map π (𝟙 (Rep.res π (Rep.res τ B))) 1 ≫
        groupCohomology.map (MonoidHom.id G) d.τ₃ 1 ≫
          groupCohomology.δ hY 1 2 rfl ≫ (groupCohomology.functor ℤ G 2).map φ := by
  have ht := originalRelation_obstruction_tower π τ B C D η j (d.τ₁ ≫ φ) hη
  have hd := originalCoefficient_delta_naturality d
    (originalRelationGroupChange_shortExact (τ.comp π) B) hY 1 2 rfl
  change groupCohomology.δ (originalRelationGroupChange_shortExact (τ.comp π) B) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map d.τ₁ =
    groupCohomology.map (MonoidHom.id G) d.τ₃ 1 ≫ groupCohomology.δ hY 1 2 rfl at hd
  erw [ht, CategoryTheory.Functor.map_comp]
  have he := congrArg (fun m =>
    groupCohomology.map π (𝟙 (Rep.res π (Rep.res τ B))) 1 ≫ m ≫
      (groupCohomology.functor ℤ G 2).map φ) hd
  simpa only [Category.assoc] using he

end
end Dubon2026
