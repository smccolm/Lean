import Dubon2026.RestrictedTwoCocycleDescent

/-! # The actual finite-image boundary gives the original target H2 zero

This transports the concrete finite cochain produced by arithmetic
coboundary descent to the surjective finite Galois target. It is the
quotient step needed for equality of the source-induced finite class and
the enlarged scalar obstruction in DUB-17's local pairing comparison.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

/-- The specified boundary on the actual image of a surjective group map
supplies a boundary on its original target, so the same target H2 class is zero. -/
theorem originalTwoCocycle_H2_zero_of_surjective_range_boundary
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π) (A : Rep.{0} R H)
    (c : groupCohomology.cocycles₂ A) (d : π.range → A)
    (hd : ∀ g h, c (π g, π h) = A.ρ (π g) (d (π.rangeRestrict h)) -
      d (π.rangeRestrict (g * h)) + d (π.rangeRestrict g)) :
    groupCohomology.H2π A c = 0 := by
  let b : H → A := fun σ => d (π.rangeRestrict (Function.surjInv hπ σ))
  have hb (g : G) : b (π g) = d (π.rangeRestrict g) :=
    congrArg d (Subtype.ext (Function.surjInv_eq hπ (π g)))
  apply (groupCohomology.H2π_eq_zero_iff c).mpr
  refine ⟨b, ?_⟩
  funext z
  obtain ⟨g, hg⟩ := hπ z.1
  obtain ⟨h, hh⟩ := hπ z.2
  rcases z with ⟨σ, τ⟩
  dsimp only at hg hh
  subst σ
  subst τ
  change A.ρ (π g) (b (π h)) - b (π g * π h) + b (π g) = c (π g, π h)
  rw [← map_mul π, hb, hb, hb]
  exact (hd g h).symm

end
end Dubon2026
