import Dubon2026.ContinuousCohomologyCoefficientMap
import Dubon2026.ContinuousExactCoefficientLifts

/-! # Original continuous lifts and actual kernel-valued connecting boundaries -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Lift the actual original continuous one-cocycle through the normalized
section of the original surjective coefficient map. The lift is a continuous
one-cochain, and is not falsely asserted to be a cocycle. -/
def coefficientConnectingOneLift (c : continuousRepresentationCocyclesOne C) : C(G, B) :=
  ⟨fun g => exactCoefficientSection ψ hψ (c.val g),
    (exactCoefficientSection_continuous ψ hψ).comp c.property⟩

omit [IsTopologicalGroup G] [DiscreteTopology B] [ContinuousSMul R B] in
/-- The lifted cochain projects to the exact original cocycle function. -/
theorem coefficientConnectingOneLift_project
    (c : continuousRepresentationCocyclesOne C) (g : G) :
    ψ (coefficientConnectingOneLift B C ψ hψ c g) = c.val g := by
  exact exactCoefficientSection_rightInverse ψ hψ (c.val g)

include hψρ in
/-- The original degree-one boundary of the actual lift is killed by the
original quotient coefficient map, by equivariance and the original cocycle law. -/
theorem coefficientConnectingBoundary_project_zero
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    ψ ((continuousRepresentationCoboundaryTwo B hB
      (coefficientConnectingOneLift B C ψ hψ c)).val z) = 0 := by
  change ψ (B.ρ z.1 (exactCoefficientSection ψ hψ (c.val z.2)) -
    exactCoefficientSection ψ hψ (c.val (z.1 * z.2)) +
    exactCoefficientSection ψ hψ (c.val z.1)) = 0
  rw [map_add, map_sub, hψρ, exactCoefficientSection_rightInverse,
    exactCoefficientSection_rightInverse, exactCoefficientSection_rightInverse]
  have hc : c.val (z.1 * z.2) = C.ρ z.1 (c.val z.2) + c.val z.1 :=
    (groupCohomology.mem_cocycles₁_iff _).mp c.val.property z.1 z.2
  rw [hc]
  abel

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A] in
include hψρ hExact in
/-- Exactness of the original coefficient sequence puts the same original
lift boundary in the actual inclusion range, without assuming any cohomological
exactness or connecting-map conclusion. -/
theorem coefficientConnectingBoundary_mem_range
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    (continuousRepresentationCoboundaryTwo B hB
      (coefficientConnectingOneLift B C ψ hψ c)).val z ∈ LinearMap.range φ := by
  rw [hExact]
  exact coefficientConnectingBoundary_project_zero B C ψ hψ hψρ hB c z

end
end Dubon2026
