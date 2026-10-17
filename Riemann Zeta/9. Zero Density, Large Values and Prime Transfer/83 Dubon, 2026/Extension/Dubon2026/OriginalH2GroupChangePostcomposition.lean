import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # H2 group pullback followed by the actual coefficient map

Apply the pinned composition theorem before substituting the large relation
coefficient. This is the needed functoriality edge for DUB-17's original
relation obstruction comparison, with default elaboration limits.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Actual H2 group pullback commutes with the displayed coefficient
postcomposition. -/
theorem originalH2_groupChange_postcomposition
    {G H : Type} [Group G] [Group H] (f : G →* H)
    (A B : Rep ℤ H) (C : Rep ℤ G) (φ : A ⟶ B) (j : Rep.res f B ⟶ C) :
    groupCohomology.map f (𝟙 (Rep.res f A)) 2 ≫
      (groupCohomology.functor ℤ G 2).map ((Rep.resFunctor f).map φ ≫ j) =
      (groupCohomology.functor ℤ H 2).map φ ≫ groupCohomology.map f j 2 := by
  calc
    _ = groupCohomology.map f ((Rep.resFunctor f).map φ ≫ j) 2 := by
      simpa only [MonoidHom.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] using
        (groupCohomology.map_comp f (MonoidHom.id G)
          (𝟙 (Rep.res f A)) ((Rep.resFunctor f).map φ ≫ j) 2).symm
    _ = _ := by
      simpa only [MonoidHom.id_comp] using
        (groupCohomology.map_comp (MonoidHom.id H) f φ j 2)

end
end Dubon2026
