import Dubon2026.ContinuousExactCoefficientLifts
import Dubon2026.ContinuousRepresentationCohomology

/-! # The actual continuous connecting cocycle of an invariant coefficient

This is the degree-zero connecting input needed for the cup/connecting-map
adjunction in the finite-module local duality route for DUB-17. The original
coefficient sequence, action, invariant and continuous lift are retained.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  (A B C : Rep.{0} R G)
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)

include hψρ hExact in
/-- The difference of a genuine lift of an invariant lies in the exact original
coefficient image, so its preimage is derived from exactness. -/
theorem coefficientInvariantLiftDifference_mem_range (c : C.ρ.invariants) (g : G) :
    B.ρ g (exactCoefficientSection ψ hψ c.val) - exactCoefficientSection ψ hψ c.val ∈
      LinearMap.range φ := by
  rw [hExact]
  change ψ (B.ρ g (exactCoefficientSection ψ hψ c.val) -
    exactCoefficientSection ψ hψ c.val) = 0
  rw [map_sub, hψρ, exactCoefficientSection_rightInverse]
  exact sub_eq_zero.mpr (c.property g)

variable [TopologicalSpace R] [TopologicalSpace G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B]
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The actual continuous cocycle obtained by lifting an original invariant and
pulling its original degree-zero differential back through the inclusion. -/
def coefficientInvariantConnectingCocycle (c : C.ρ.invariants) :
    continuousRepresentationCocyclesOne A := by
  let b := exactCoefficientSection ψ hψ c.val
  let f : G → A := fun g => exactCoefficientPreimage φ hφ (B.ρ g b - b)
  have hf : ∀ g, φ (f g) = B.ρ g b - b := fun g =>
    exactCoefficientPreimage_map φ hφ _
      (coefficientInvariantLiftDifference_mem_range A B C φ ψ hψ hψρ hExact c g)
  refine ⟨⟨f, (groupCohomology.mem_cocycles₁_iff _).mpr ?_⟩, ?_⟩
  · intro g h
    apply hφ
    rw [map_add, hφρ, hf, hf, hf, map_sub, map_mul]
    change B.ρ g (B.ρ h b) - b =
      B.ρ g (B.ρ h b) - B.ρ g b + (B.ρ g b - b)
    abel
  · exact (exactCoefficientPreimage_continuous φ hφ).comp
      ((hB.comp (continuous_id.prodMk continuous_const)).sub continuous_const)

/-- The original inclusion takes the constructed cocycle to the actual
degree-zero differential of the same chosen lift. -/
theorem coefficientInvariantConnectingCocycle_map (c : C.ρ.invariants) (g : G) :
    φ ((coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val g) =
      B.ρ g (exactCoefficientSection ψ hψ c.val) - exactCoefficientSection ψ hψ c.val :=
  exactCoefficientPreimage_map φ hφ _
    (coefficientInvariantLiftDifference_mem_range A B C φ ψ hψ hψρ hExact c g)

end
end Dubon2026
