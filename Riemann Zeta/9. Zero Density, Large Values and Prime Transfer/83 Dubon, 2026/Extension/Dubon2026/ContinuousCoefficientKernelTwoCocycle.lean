import Dubon2026.ContinuousCohomologyCoefficientMap
import Dubon2026.ContinuousExactCoefficientLifts

/-! # Original continuous two-cocycles valued in an actual coefficient kernel -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hExact : LinearMap.range φ = LinearMap.ker ψ)

/-- Pull an original continuous kernel-valued two-cocycle through the actual
injective coefficient inclusion. The original two-cocycle law and continuity
are derived by its genuine coefficient inverse, not postulated. -/
def coefficientKernelTwoCocycle (b : continuousRepresentationCocyclesTwo B)
    (hb : ∀ z, ψ (b.val z) = 0) : continuousRepresentationCocyclesTwo A := by
  let f : G × G → A := fun z => exactCoefficientPreimage φ hφ (b.val z)
  have hi : ∀ z, φ (f z) = b.val z := by
    intro z
    apply exactCoefficientPreimage_map φ hφ
    rw [hExact]
    exact hb z
  refine ⟨⟨f, ?_⟩, (exactCoefficientPreimage_continuous φ hφ).comp b.property⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h t
  apply hφ
  change φ (f (g * h, t) + f (g, h)) = φ (A.ρ g (f (h, t)) + f (g, h * t))
  rw [map_add, map_add, hφρ, hi, hi, hi, hi]
  exact (groupCohomology.mem_cocycles₂_iff _).mp b.val.property g h t

/-- The original inclusion recovers each original kernel-valued cocycle value. -/
theorem coefficientKernelTwoCocycle_map (b : continuousRepresentationCocyclesTwo B)
    (hb : ∀ z, ψ (b.val z) = 0) (z : G × G) :
    φ ((coefficientKernelTwoCocycle A B C φ hφ hφρ ψ hExact b hb).val z) = b.val z := by
  apply exactCoefficientPreimage_map φ hφ
  rw [hExact]
  exact hb z

/-- The genuine original continuous coefficient map carries the constructed
cocycle to the exact original kernel-valued cocycle, including its original function. -/
theorem coefficientKernelTwoCocycle_coefficient_map (hcφ : Continuous φ)
    (b : continuousRepresentationCocyclesTwo B) (hb : ∀ z, ψ (b.val z) = 0) :
    continuousCoefficientCocycleTwoMap A B φ hcφ hφρ
      (coefficientKernelTwoCocycle A B C φ hφ hφρ ψ hExact b hb) = b := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  exact coefficientKernelTwoCocycle_map A B C φ hφ hφρ ψ hExact b hb z

end
end Dubon2026
