import Dubon2026.ContinuousConnectingLiftIndependence

/-! # Linearity of the original continuous connecting class on cocycles -/

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

/-- The original connecting cocycle class is linear, even though its chosen
coefficient section need not be linear. Actual sums and scalar multiples of
continuous lifts, together with proved lift independence, give the two laws. -/
def continuousConnectingCocycleClass :
    continuousRepresentationCocyclesOne C →ₗ[R] ContinuousRepresentationH2 A hA where
  toFun c := Submodule.Quotient.mk
    (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)
  map_add' c d := by
    rw [← Submodule.Quotient.mk_add]
    apply coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (c + d) _
      (coefficientConnectingOneLift B C ψ hψ c + coefficientConnectingOneLift B C ψ hψ d)
    · intro g
      change ψ (coefficientConnectingOneLift B C ψ hψ c g +
        coefficientConnectingOneLift B C ψ hψ d g) = c.val g + d.val g
      rw [map_add, coefficientConnectingOneLift_project, coefficientConnectingOneLift_project]
    · intro z
      change φ ((coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val z +
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB d).val z) = _
      rw [map_add, coefficientConnectingTwoCocycle_map, coefficientConnectingTwoCocycle_map,
        map_add]
      rfl
  map_smul' r c := by
    rw [← Submodule.Quotient.mk_smul]
    apply coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (r • c) _ (r • coefficientConnectingOneLift B C ψ hψ c)
    · intro g
      change ψ (r • coefficientConnectingOneLift B C ψ hψ c g) = r • c.val g
      rw [map_smul, coefficientConnectingOneLift_project]
    · intro z
      change φ (r •
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val z) = _
      rw [map_smul, coefficientConnectingTwoCocycle_map, map_smul]
      rfl

/-- The linear connecting class evaluates to the original continuous
coefficient-preimage construction, with no assumed linear section. -/
theorem continuousConnectingCocycleClass_apply (c : continuousRepresentationCocyclesOne C) :
    continuousConnectingCocycleClass A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c =
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH2 A hA) := by
  rfl

end
end Dubon2026
