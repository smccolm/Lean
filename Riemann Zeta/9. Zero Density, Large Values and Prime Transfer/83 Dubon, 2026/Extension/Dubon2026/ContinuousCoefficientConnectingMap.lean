import Dubon2026.ContinuousConnectingCocycleClass

/-! # The actual connecting map from continuous H1 to continuous H2 -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- The actual connecting class kills every original degree-zero coboundary.
Lift its original coefficient and take its original degree-zero differential;
this is an actual continuous lift with zero degree-one boundary. -/
theorem continuousConnectingCocycleClass_coboundary (u : C) :
    continuousConnectingCocycleClass A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (continuousRepresentationCoboundaryOne C hC u) = 0 := by
  let v := exactCoefficientSection ψ hψ u
  let b := continuousRepresentationCoboundaryOne B hB v
  change (Submodule.Quotient.mk
    (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB
      (continuousRepresentationCoboundaryOne C hC u)) : ContinuousRepresentationH2 A hA) = 0
  rw [← Submodule.Quotient.mk_zero]
  apply coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
    (continuousRepresentationCoboundaryOne C hC u) 0 ⟨b.val, b.property⟩
  · intro g
    change ψ (B.ρ g v - v) = C.ρ g u - u
    rw [map_sub, hψρ, exactCoefficientSection_rightInverse]
  · intro z
    change φ 0 = (groupCohomology.d₁₂ B b.val) z
    rw [map_zero, groupCohomology.cocycles₁.d₁₂_apply]
    rfl

/-- The original continuous coefficient sequence induces its genuine connecting
linear map on H1. Both linearity and disappearance of actual coboundaries have
been proved using original continuous cochain witnesses. -/
def continuousCoefficientConnectingMap :
    ContinuousRepresentationH1 C hC →ₗ[R] ContinuousRepresentationH2 A hA :=
  (continuousRepresentationCoboundariesOne C hC).liftQ
    (continuousConnectingCocycleClass A B C φ hφ hφρ ψ hψ hψρ hExact hA hB)
    (by
      rintro _ ⟨u, rfl⟩
      exact continuousConnectingCocycleClass_coboundary A B C φ hφ hφρ ψ hψ hψρ
        hExact hA hB hC u)

/-- On every original H1 representative, the connecting map is the class of
the actual boundary of its continuous lift, pulled back through the inclusion. -/
theorem continuousCoefficientConnectingMap_mk (c : continuousRepresentationCocyclesOne C) :
    continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC
      (Submodule.Quotient.mk c) =
        (Submodule.Quotient.mk
          (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
          ContinuousRepresentationH2 A hA) := by
  rfl

/-- The image of the actual connecting map is killed by the actual coefficient
H2 map, with the original chosen continuous lift as coboundary witness. -/
theorem continuousCoefficientConnectingMap_image_zero (hcφ : Continuous φ)
    (x : ContinuousRepresentationH1 C hC) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    exact coefficientConnectingTwoCocycle_image_class_zero A B C φ hφ hφρ ψ hψ hψρ
      hExact hB hA hcφ c

end
end Dubon2026
