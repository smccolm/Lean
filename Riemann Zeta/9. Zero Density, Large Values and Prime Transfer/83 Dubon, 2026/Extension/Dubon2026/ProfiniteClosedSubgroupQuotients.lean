import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-! # Actual finite quotients detect proper closed subgroups of the original profinite group -/

namespace Dubon2026

noncomputable section
open Set

/-- An original proper closed subgroup has proper image in one genuine original finite quotient. -/
theorem profinite_closed_subgroup_proper_quotient (G : ProfiniteGrp)
    (K : Subgroup G) (hclosed : IsClosed (K : Set G)) (hK : K ≠ ⊤) :
    ∃ U : OpenNormalSubgroup G,
      K.map (QuotientGroup.mk' U.toSubgroup) ≠ ⊤ := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ K := by
    by_contra! hall
    exact hK (eq_top_iff.mpr (fun g _ => hall g))
  have hc : IsCompact ((fun x : G => x⁻¹ * g) '' (K : Set G)) :=
    hclosed.isCompact.image (continuous_inv.mul continuous_const)
  have hone : (1 : G) ∈ ((fun x : G => x⁻¹ * g) '' (K : Set G))ᶜ := by
    rintro ⟨x, hx, heq⟩
    have hxg : x = g := inv_mul_eq_one.mp heq
    exact hg (hxg ▸ hx)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := G) hc.isClosed.isOpen_compl hone
  refine ⟨U, ?_⟩
  intro htop
  have hmem : QuotientGroup.mk' U.toSubgroup g ∈
      K.map (QuotientGroup.mk' U.toSubgroup) := by rw [htop]; trivial
  obtain ⟨k, hk, heq⟩ := hmem
  have hkg : k⁻¹ * g ∈ U := by
    apply (QuotientGroup.eq_one_iff (k⁻¹ * g)).mp
    change QuotientGroup.mk' U.toSubgroup (k⁻¹ * g) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  exact (hU hkg) ⟨k, hk, rfl⟩

end
end Dubon2026
