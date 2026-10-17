import Dubon2026.OriginalIntegralInternalHomVanishing
import Dubon2026.OriginalInternalHomSplitting

/-! # Projectivity of the actual fundamental coefficient's relation kernel

The original kernel is integrally free. Its actual free cover has an
integrally free kernel as well, so the proved internal-Hom H1 vanishing
constructs an equivariant section. The pinned retract theorem then proves
projectivity in the original representation category. This supplies the
projective resolution needed by DUB-17's finite class/Ext duality route;
no projectivity or splitting certificate is an input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The actual free cover of the literal fundamental relation kernel splits, with all freeness and internal-Hom vanishing inputs derived from the original two subgroup degrees. -/
theorem originalPGroup_relationKernel_cover_splits
    {G : Type} [Group G] [Fintype G] (B : Rep.{0} ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Nonempty (originalRelationShortComplex (originalRelationModule B)).Splitting := by
  letI := originalArbitraryRelationModule_free B
  letI := originalArbitraryRelationModule_free (originalRelationModule B)
  letI : Module.Free ℤ (originalRelationShortComplex (originalRelationModule B)).X₃ :=
    originalArbitraryRelationModule_free B
  exact originalShortComplex_splitting_of_internalHom_first_zero
    (originalRelationShortComplex_shortExact (originalRelationModule B))
    (originalPGroup_relationKernel_internalHom_first_zero B
      (originalRelationModule (originalRelationModule B)) p hG h)

/-- The literal relation kernel is projective over the integral group ring; this is stronger than its already proved integral freeness. -/
theorem originalPGroup_relationKernel_projective
    {G : Type} [Group G] [Fintype G] (B : Rep.{0} ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Projective (originalRelationModule B) := by
  obtain ⟨s⟩ := originalPGroup_relationKernel_cover_splits B p hG h
  let r : Retract (originalRelationModule B) (Rep.free ℤ G (originalRelationModule B)) :=
    ⟨s.s, originalRelationFreeCover (originalRelationModule B), s.s_g⟩
  exact r.projective

end
end Dubon2026
