import Dubon2026.ContinuousRepresentationRestriction

/-! # Literal two-cocycle descent through the actual finite image

The original two-cocycle identity descends along a surjective group map
once both coordinate fibers have the proved common periods. This supplies
finite-stage class H2 representatives for DUB-17's invariant-map input.
-/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  (A : Rep.{0} R H) (φ : G →* H) (hφ : Function.Surjective φ)

include hφ

/-- An original restricted two-cocycle constant on both actual fibers descends with unchanged values. -/
theorem restrictedTwoCocycle_exists_descent
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A φ))
    (hc : ∀ g h g' h', φ g = φ g' → φ h = φ h' → c (g, h) = c (g', h')) :
    ∃ d : groupCohomology.cocycles₂ A, ∀ g h, d (φ g, φ h) = c (g, h) := by
  let d : H × H → A := fun z => c (Function.surjInv hφ z.1, Function.surjInv hφ z.2)
  have hd (g h : G) : d (φ g, φ h) = c (g, h) :=
    hc _ _ g h (Function.surjInv_eq hφ (φ g)) (Function.surjInv_eq hφ (φ h))
  refine ⟨⟨d, ?_⟩, hd⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  obtain ⟨g, rfl⟩ := hφ g
  obtain ⟨h, rfl⟩ := hφ h
  obtain ⟨k, rfl⟩ := hφ k
  rw [← map_mul φ, ← map_mul φ, hd, hd, hd, hd]
  exact (groupCohomology.mem_cocycles₂_iff _).mp c.property g h k

end
end Dubon2026
