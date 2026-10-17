import Dubon2026.OriginalPGroupInternalHomAcyclicity
import Dubon2026.OriginalCoefficientNormCohomology

/-! # Literal norm witnesses for lattice maps into the fundamental coefficient

Equivariant maps are invariants in the original internal Hom. Its proved
norm surjectivity constructs the source's actual sum-of-conjugates
witness, an input to the finite class/Ext duality comparison for DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

/-- Every actual map from an integral projective source into the original p-group acyclic coefficient is a literal norm, with no norm-witness hypothesis. -/
theorem originalPGroup_internalHom_map_norm_witness
    {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2))
    (φ : M ⟶ B) :
    ∃ η : M →ₗ[ℤ] B, ∀ x : M, φ.hom x = ∑ g : G, B.ρ g (η (M.ρ g⁻¹ x)) := by
  have hi : φ.hom.toLinearMap ∈ ((Rep.ihom M).obj B).ρ.invariants := by
    intro g
    apply LinearMap.ext
    intro x
    change B.ρ g (φ.hom (M.ρ g⁻¹ x)) = φ.hom x
    rw [← Rep.hom_comm_apply, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨η, hη⟩ := originalPGroup_internalHom_norm_preimages M B p hG h
    φ.hom.toLinearMap hi
  simp only [Representation.norm, LinearMap.sum_apply] at hη
  change (∑ g : G, B.ρ g ∘ₗ η ∘ₗ M.ρ g⁻¹) = φ.hom.toLinearMap at hη
  refine ⟨η, fun x => ?_⟩
  change φ.hom.toLinearMap x = _
  rw [← hη, LinearMap.sum_apply]
  rfl

end
end Dubon2026
