import Dubon2026.RestrictedTwoCocycleDescent

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Descending through the image of a surjection gives a cocycle on the
original target group, with the same values at every original group element. -/
theorem originalTwoCocycle_surjective_range
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π) (A : Rep R H)
    (d : groupCohomology.cocycles₂ (Rep.res π.range.subtype A)) :
    ∃ c : groupCohomology.cocycles₂ A,
      ∀ g h, c (π g, π h) = d (π.rangeRestrict g, π.rangeRestrict h) := by
  let e : π.range ≃* H := MulEquiv.ofBijective π.range.subtype
    ⟨Subtype.val_injective, fun σ => by
      obtain ⟨g, hg⟩ := hπ σ
      exact ⟨π.rangeRestrict g, hg⟩⟩
  have he (σ : H) : (e.symm σ).val = σ := e.apply_symm_apply σ
  let c : groupCohomology.cocycles₂ A := ⟨fun z => d (e.symm z.1, e.symm z.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h k
    have hh := (groupCohomology.mem_cocycles₂_iff _).mp d.property
      (e.symm g) (e.symm h) (e.symm k)
    change d (e.symm g * e.symm h, e.symm k) + d (e.symm g, e.symm h) =
      A.ρ (e.symm g).val (d (e.symm h, e.symm k)) + d (e.symm g, e.symm h * e.symm k) at hh
    simpa only [map_mul, he] using hh⟩
  have hs (g : G) : e.symm (π g) = π.rangeRestrict g := by
    apply e.injective
    exact e.apply_symm_apply _
  refine ⟨c, fun g h => ?_⟩
  change d (e.symm (π g), e.symm (π h)) = _
  rw [hs, hs]

end
end Dubon2026
