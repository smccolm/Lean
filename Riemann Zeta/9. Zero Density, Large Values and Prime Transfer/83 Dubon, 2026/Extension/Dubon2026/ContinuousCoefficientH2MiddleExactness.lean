import Dubon2026.ContinuousCoefficientKernelTwoCocycle

/-! # Actual middle exactness of the original continuous H2 coefficient sequence -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

include hExact in
/-- The composite of the actual two coefficient H2 maps is zero because the
original coefficient composite is zero, on each original cocycle value. -/
theorem continuousCoefficientH2_composite_zero (x : ContinuousRepresentationH2 A hA) :
    continuousCoefficientH2Map B C ψ continuous_of_discreteTopology hψρ hB hC
      (continuousCoefficientH2Map A B φ hcφ hφρ hA hB x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    rw [continuousCoefficientH2Map_mk, continuousCoefficientH2Map_mk]
    have hm : continuousCoefficientCocycleTwoMap B C ψ continuous_of_discreteTopology hψρ
        (continuousCoefficientCocycleTwoMap A B φ hcφ hφρ a) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change ψ (φ (a.val z)) = 0
      have hv := LinearMap.mem_range_self φ (a.val z)
      rw [hExact] at hv
      exact hv
    rw [hm, Submodule.Quotient.mk_zero]

include hφ hψ hExact in
/-- If the actual quotient-coefficient H2 image is zero, lift its genuine
continuous coboundary witness and subtract its original boundary. The resulting
original cocycle is kernel-valued and therefore has an actual inclusion preimage. -/
theorem continuousCoefficientH2_middle_mem_range_iff (x : ContinuousRepresentationH2 B hB) :
    x ∈ LinearMap.range (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) ↔
      continuousCoefficientH2Map B C ψ continuous_of_discreteTopology hψρ hB hC x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact continuousCoefficientH2_composite_zero A B C φ hcφ hφρ ψ hψρ hExact hA hB hC y
  · induction x using Submodule.Quotient.induction_on with
    | _ b =>
      intro hx
      rw [continuousCoefficientH2Map_mk] at hx
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      let lift : C(G, B) := ⟨fun g => exactCoefficientSection ψ hψ (w g),
        (exactCoefficientSection_continuous ψ hψ).comp w.continuous⟩
      have hproj : (⟨fun g => ψ (lift g),
          (continuous_of_discreteTopology (f := ψ)).comp lift.continuous⟩ : C(G, C)) = w := by
        apply ContinuousMap.ext
        intro g
        exact exactCoefficientSection_rightInverse ψ hψ (w g)
      have hlift : continuousCoefficientCocycleTwoMap B C ψ continuous_of_discreteTopology hψρ
          (continuousRepresentationCoboundaryTwo B hB lift) =
            continuousRepresentationCoboundaryTwo C hC w := by
        rw [continuousCoefficientCocycleTwoMap_coboundary B C ψ continuous_of_discreteTopology
          hψρ hB hC lift, hproj]
      let d := b - continuousRepresentationCoboundaryTwo B hB lift
      have hd : continuousCoefficientCocycleTwoMap B C ψ continuous_of_discreteTopology hψρ d = 0 := by
        change continuousCoefficientCocycleTwoMap B C ψ continuous_of_discreteTopology hψρ
          (b - continuousRepresentationCoboundaryTwo B hB lift) = 0
        rw [map_sub, hlift, hw, sub_self]
      have hker : ∀ z, ψ (d.val z) = 0 := by
        intro z
        exact congrArg (fun c : continuousRepresentationCocyclesTwo C => c.val z) hd
      have hclass : (Submodule.Quotient.mk d : ContinuousRepresentationH2 B hB) =
          Submodule.Quotient.mk b := by
        apply (continuousRepresentationH2_eq_iff B hB d b).mpr
        refine ⟨-lift, ?_⟩
        rw [map_neg]
        dsimp only [d]
        abel
      refine ⟨Submodule.Quotient.mk (coefficientKernelTwoCocycle A B C φ hφ hφρ ψ hExact d hker), ?_⟩
      rw [continuousCoefficientH2Map_mk,
        coefficientKernelTwoCocycle_coefficient_map A B C φ hφ hφρ ψ hExact hcφ d hker]
      exact hclass

include hφ hψ hExact in
/-- The original inclusion H2 map has precisely the actual quotient-coefficient
H2 kernel as its range; no cohomological exactness is assumed. -/
theorem continuousCoefficientH2_middle_range_eq_ker :
    LinearMap.range (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) =
      LinearMap.ker (continuousCoefficientH2Map B C ψ continuous_of_discreteTopology hψρ hB hC) := by
  ext x
  exact continuousCoefficientH2_middle_mem_range_iff A B C φ hφ hcφ hφρ ψ hψ hψρ
    hExact hA hB hC x

end
end Dubon2026
