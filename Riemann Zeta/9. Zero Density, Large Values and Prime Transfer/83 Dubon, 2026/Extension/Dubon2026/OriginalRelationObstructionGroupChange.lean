import Dubon2026.OriginalRelationGroupChangeConnecting
import Dubon2026.OriginalH2GroupChangePostcomposition
import Dubon2026.OriginalRelationExtensionObstruction

/-! # The original relation obstruction commutes with the stage maps

The original group pullback, canonical relation map and actual coefficient
transition preserve the H1-to-H2 obstruction. This is the finite obstruction
comparison required when DUB-17 passes to the constructed arithmetic level.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G H : Type} [Group G] [Group H] (f : G →* H)
  (B C : Rep ℤ H) (D : Rep ℤ G)

/-- The actual original H1-to-H2 relation obstruction is natural under
the canonical relation restriction and the given coefficient transition. -/
theorem originalRelationExtensionObstruction_groupChange
    (φ : originalRelationModule B ⟶ C) (j : Rep.res f C ⟶ D) :
    groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫
      originalRelationExtensionObstruction (Rep.res f B) D
        (originalRelationGroupChange f B ≫ (Rep.resFunctor f).map φ ≫ j) =
      originalRelationExtensionObstruction B C φ ≫ groupCohomology.map f j 2 := by
  have hm := originalH2_groupChange_postcomposition f (originalRelationModule B) C D φ j
  calc
    _ = (groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫
        groupCohomology.δ (originalRelationShortComplex_shortExact (Rep.res f B)) 1 2 rfl ≫
        (groupCohomology.functor ℤ G 2).map (originalRelationGroupChange f B)) ≫
        (groupCohomology.functor ℤ G 2).map ((Rep.resFunctor f).map φ ≫ j) := by
      unfold originalRelationExtensionObstruction
      erw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
      rfl
    _ = (groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
        groupCohomology.map f (𝟙 (Rep.res f (originalRelationModule B))) 2) ≫
        (groupCohomology.functor ℤ G 2).map ((Rep.resFunctor f).map φ ≫ j) :=
      congrArg (fun m => m ≫ (groupCohomology.functor ℤ G 2).map
        ((Rep.resFunctor f).map φ ≫ j)) (originalRelationGroupChange_delta f B)
    _ = _ := by
      erw [Category.assoc, hm]
      rfl

end
end Dubon2026
