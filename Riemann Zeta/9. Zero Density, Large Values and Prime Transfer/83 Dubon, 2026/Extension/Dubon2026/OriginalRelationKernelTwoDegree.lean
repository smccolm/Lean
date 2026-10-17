import Dubon2026.OriginalArbitraryRelationSubgroup
import Dubon2026.OriginalNormInvariantLifting
import Dubon2026.OriginalInvariantLiftFirstVanishing
import Dubon2026.OriginalNestedSubgroupNorms

/-! # Derived two-degree vanishing of the actual free-cover kernel

The original fundamental coefficient's subgroup vanishing gives literal
norm preimages. Its actual free cover therefore lifts invariants, and
the genuine long exact sequence proves H1/H2 vanishing of the literal
kernel. This removes those inputs from the projective-presentation route
to DUB-17's lattice/internal-Hom duality. Kernel projectivity is not claimed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)

/-- The actual arbitrary-index relation kernel has zero subgroup H1/H2 when the original target has H1 vanishing and literal subgroup norm preimages. -/
theorem originalRelationKernel_subgroup_first_second_zero (S : Subgroup G) [Fintype S]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1))
    (hnorm : ∀ x : B, x ∈ (Rep.res S.subtype B).ρ.invariants →
      ∃ y : B, (Rep.res S.subtype B).ρ.norm y = x) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 2) := by
  have hX := originalArbitraryRelationSubgroup_shortExact B S
  have hfree1 := originalArbitraryFree_subgroup_positive_zero (k := ℤ) B S 0
  have hfree2 := originalArbitraryFree_subgroup_positive_zero (k := ℤ) B S 1
  constructor
  · apply originalKernel_first_zero_of_invariant_lifting hX hfree1
    exact originalInvariant_lift_of_norm_preimages
      ((Rep.resFunctor S.subtype).map (originalRelationFreeCover B))
      (originalRelationFreeCover_surjective B) hnorm
  · have hi := groupCohomology.isIso_δ_of_isZero hX 1 hfree1 hfree2
    exact hfirst.of_iso (@asIso _ _ _ _ (groupCohomology.δ hX 1 2 rfl) hi).symm

/-- The actual relation kernel inherits subgroup H1/H2 vanishing from the original p-group coefficient; norm-lifting assumptions are derived. -/
theorem originalPGroup_relationKernel_subgroup_first_second_zero
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2))
    (S : Subgroup G) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 2) := by
  letI := Fintype.ofFinite S
  exact originalRelationKernel_subgroup_first_second_zero B S (h S).1
    (originalPGroup_subgroup_norm_preimages B p hG h S)

end
end Dubon2026
