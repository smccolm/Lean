import Dubon2026.ContinuousCoefficientConnectingCocycle

/-! # The actual continuous connecting class is independent of its original lift -/

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

/-- Any actual continuous lift and actual preimage of its boundary determine
the same original continuous H2 class. The difference witness is constructed in
the original continuous cochain space from the coefficient sequence itself. -/
theorem coefficientConnectingClass_eq_of_lift
    (c : continuousRepresentationCocyclesOne C)
    (a : continuousRepresentationCocyclesTwo A) (b : C(G, B))
    (hb : ∀ g, ψ (b g) = c.val g)
    (ha : ∀ z, φ (a.val z) = (continuousRepresentationCoboundaryTwo B hB b).val z) :
    (Submodule.Quotient.mk
      (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
      ContinuousRepresentationH2 A hA) = Submodule.Quotient.mk a := by
  let s := coefficientConnectingOneLift B C ψ hψ c
  let w : C(G, A) := ⟨fun g => exactCoefficientPreimage φ hφ (s g - b g),
    (exactCoefficientPreimage_continuous φ hφ).comp (s.continuous.sub b.continuous)⟩
  have hw : ∀ g, φ (w g) = s g - b g := by
    intro g
    apply exactCoefficientPreimage_map φ hφ
    rw [hExact]
    change ψ (s g - b g) = 0
    rw [map_sub, hb, coefficientConnectingOneLift_project]
    exact sub_self _
  apply (continuousRepresentationH2_eq_iff A hA _ _).mpr
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext z
  apply hφ
  change φ (A.ρ z.1 (w z.2) - w (z.1 * z.2) + w z.1) =
    φ ((coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val z -
      a.val z)
  simp only [map_add, map_sub, hφρ, hw,
    coefficientConnectingTwoCocycle_map, ha]
  change (B.ρ z.1 (s z.2) - B.ρ z.1 (b z.2)) - (s (z.1 * z.2) - b (z.1 * z.2)) +
      (s z.1 - b z.1) =
    (B.ρ z.1 (s z.2) - s (z.1 * z.2) + s z.1) -
      (B.ρ z.1 (b z.2) - b (z.1 * z.2) + b z.1)
  abel

end
end Dubon2026
