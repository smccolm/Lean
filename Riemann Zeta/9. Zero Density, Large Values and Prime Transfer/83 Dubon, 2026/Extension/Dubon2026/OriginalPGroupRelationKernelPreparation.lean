import Dubon2026.OriginalArbitraryRelationFree
import Dubon2026.OriginalRelationKernelTwoDegree
import Dubon2026.OriginalFundamentalPGroupVanishing

/-! # Derived kernel inputs for the actual fundamental presentation

The literal relation kernel is integrally free and inherits all subgroup
H1/H2 vanishing, positive vanishing and invariant norm preimages. These
are derived from the original coefficient's two subgroup degrees and
serve DUB-17's projective-presentation and internal-Hom duality route.
Projectivity and the duality conclusion are not asserted here.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The original p-group coefficient's actual free kernel is integrally free, has vanishing subgroup H1/H2 and positive cohomology, and has literal invariant norm preimages. -/
theorem originalPGroup_relationKernel_prepared
    {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Module.Free ℤ (originalRelationModule B) ∧
      (∀ S : Subgroup G,
        Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 1) ∧
          Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 2)) ∧
      (∀ n : ℕ, Limits.IsZero (groupCohomology (originalRelationModule B) (n + 1))) ∧
      OriginalInvariantNormSurjective (originalRelationModule B) := by
  have hK := originalPGroup_relationKernel_subgroup_first_second_zero B p hG h
  exact ⟨originalArbitraryRelationModule_free B, hK,
    originalPGroup_positive_zero_of_subgroup_first_second p hG (originalRelationModule B) hK,
    originalPGroup_norm_preimages_of_subgroup_first_second p hG (originalRelationModule B) hK⟩

end
end Dubon2026
