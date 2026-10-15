import Dubon2026.ContinuousRepresentationRestriction

/-! # Literal one-cocycle descent through the original restriction map

The cocycle identity descends through a surjective group map when the
original values have the proved periods. This is the final algebraic
step before finite class H1 vanishing supplies an arithmetic coboundary.
-/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  (A : Rep.{0} R H) (φ : G →* H) (hφ : Function.Surjective φ)

include hφ

/-- An original restricted cocycle constant on the actual fibers descends with unchanged values and action. -/
theorem restrictedOneCocycle_exists_descent
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A φ))
    (hc : ∀ g h, φ g = φ h → c g = c h) :
    ∃ d : groupCohomology.cocycles₁ A, ∀ g, d (φ g) = c g := by
  let d : H → A := fun h => c (Function.surjInv hφ h)
  have hd (g : G) : d (φ g) = c g :=
    hc _ _ (Function.surjInv_eq hφ (φ g))
  refine ⟨⟨d, ?_⟩, hd⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro h k
  obtain ⟨g, rfl⟩ := hφ h
  obtain ⟨u, rfl⟩ := hφ k
  rw [← map_mul φ, hd, hd, hd]
  exact (groupCohomology.mem_cocycles₁_iff _).mp c.property g u

end
end Dubon2026
