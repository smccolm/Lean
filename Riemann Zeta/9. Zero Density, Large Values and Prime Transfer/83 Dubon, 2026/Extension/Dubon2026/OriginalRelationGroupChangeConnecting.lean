import Dubon2026.OriginalRelationGroupChange
import Dubon2026.OriginalCoefficientConnectingNaturality

/-! # Connecting naturality for the actual relation restriction map

The existing group and coefficient naturality theorems compare the literal
relation presentations. This retains the original H1-to-H2 obstruction when
passing to DUB-17's enlarged arithmetic stage; no comparison certificate is
left as an input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G H : Type} [Group G] [Group H] (f : G →* H) (B : Rep ℤ H)

/-- The original connecting map commutes with the actual restriction of
the relation presentation. -/
theorem originalRelationGroupChange_delta :
    groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫
      groupCohomology.δ (originalRelationShortComplex_shortExact (Rep.res f B)) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map (originalRelationGroupChange f B) =
    groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      groupCohomology.map f (𝟙 (Rep.res f (originalRelationModule B))) 2 := by
  have hc := originalCoefficient_delta_naturality (originalRelationGroupChangeSequenceMap f B)
    (originalRelationShortComplex_shortExact (Rep.res f B))
    (originalRelationGroupChange_shortExact f B) 1 2 rfl
  change groupCohomology.δ (originalRelationShortComplex_shortExact (Rep.res f B)) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map (originalRelationGroupChange f B) =
      (groupCohomology.functor ℤ G 1).map (𝟙 (Rep.res f B)) ≫
        groupCohomology.δ (originalRelationGroupChange_shortExact f B) 1 2 rfl at hc
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hc
  have hg := originalCohomologyGroupChange_delta_naturality f
    (𝟙 ((originalRelationShortComplex B).map (Rep.resFunctor f)))
    (originalRelationShortComplex_shortExact B)
    (originalRelationGroupChange_shortExact f B) 1 2 rfl
  change groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      groupCohomology.map f (𝟙 (Rep.res f (originalRelationModule B))) 2 =
    groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫
      groupCohomology.δ (originalRelationGroupChange_shortExact f B) 1 2 rfl at hg
  exact (congrArg (fun m => groupCohomology.map f (𝟙 (Rep.res f B)) 1 ≫ m) hc).trans hg.symm

end
end Dubon2026
