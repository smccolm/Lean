import Dubon2026.OriginalRelationGroupChangeConnecting
import Dubon2026.OriginalH2GroupChangePostcomposition
import Dubon2026.OriginalRelationExtensionObstruction

/-! # Inflation of the same original relation obstruction

Use the original restricted presentation, instead of replacing it by the
free presentation over the larger group. This is the finite-stage comparison
needed to connect DUB-17's actual source-cocycle cup with its descended
relation morphism. The coefficient transition and group pullback are literal.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G H : Type} [Group G] [Group H] (π : G →* H)
  (B C : Rep ℤ H) (D : Rep ℤ G)

/-- Inflating the finite relation obstruction gives the connecting
obstruction of the same restricted presentation and actual coefficient map. -/
theorem originalRestrictedRelation_obstruction_inflation
    (φ : originalRelationModule B ⟶ C) (j : Rep.res π C ⟶ D) :
    originalRelationExtensionObstruction B C φ ≫ groupCohomology.map π j 2 =
      groupCohomology.map π (𝟙 (Rep.res π B)) 1 ≫
        groupCohomology.δ (originalRelationGroupChange_shortExact π B) 1 2 rfl ≫
        (groupCohomology.functor ℤ G 2).map ((Rep.resFunctor π).map φ ≫ j) := by
  have hδ := originalCohomologyGroupChange_delta_naturality π
    (𝟙 ((originalRelationShortComplex B).map (Rep.resFunctor π)))
    (originalRelationShortComplex_shortExact B)
    (originalRelationGroupChange_shortExact π B) 1 2 rfl
  change groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      groupCohomology.map π (𝟙 (Rep.res π (originalRelationModule B))) 2 =
    groupCohomology.map π (𝟙 (Rep.res π B)) 1 ≫
      groupCohomology.δ (originalRelationGroupChange_shortExact π B) 1 2 rfl at hδ
  unfold originalRelationExtensionObstruction
  erw [Category.assoc, ← originalH2_groupChange_postcomposition π
    (originalRelationModule B) C D φ j, ← Category.assoc, hδ, Category.assoc]

end
end Dubon2026
