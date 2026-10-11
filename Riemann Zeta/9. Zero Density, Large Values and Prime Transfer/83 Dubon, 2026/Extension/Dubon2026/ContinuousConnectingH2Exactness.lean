import Dubon2026.ContinuousCoefficientConnectingMap

/-! # Actual exactness at continuous H2 for the coefficient connecting map -/

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

/-- An original continuous H2 class lies in the connecting-map image exactly
when its image under the original inclusion vanishes. A genuine continuous
coboundary witness in the middle coefficients produces the source H1 cocycle. -/
theorem continuousConnectingH2_mem_range_iff (x : ContinuousRepresentationH2 A hA) :
    x ∈ LinearMap.range
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) ↔
        continuousCoefficientH2Map A B φ hcφ hφρ hA hB x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact continuousCoefficientConnectingMap_image_zero A B C φ hφ hφρ ψ hψ hψρ
      hExact hA hB hC hcφ y
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
      intro hx
      rw [continuousCoefficientH2Map_mk] at hx
      obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      have hbz : ∀ z, (continuousRepresentationCoboundaryTwo B hB b).val z = φ (a.val z) := by
        intro z
        exact congrArg (fun d : continuousRepresentationCocyclesTwo B => d.val z) hb
      have hzero : ∀ v : A, ψ (φ v) = 0 := by
        intro v
        have hv := LinearMap.mem_range_self φ v
        rw [hExact] at hv
        exact hv
      let c : continuousRepresentationCocyclesOne C :=
        ⟨⟨fun g => ψ (b g), by
          apply (groupCohomology.mem_cocycles₁_def _).mpr
          intro g h
          change C.ρ g (ψ (b h)) - ψ (b (g * h)) + ψ (b g) = 0
          rw [← hψρ, ← map_sub, ← map_add]
          change ψ ((continuousRepresentationCoboundaryTwo B hB b).val (g, h)) = 0
          rw [hbz]
          exact hzero _⟩, (continuous_of_discreteTopology (f := ψ)).comp b.continuous⟩
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      rw [continuousCoefficientConnectingMap_mk]
      apply coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
        c a b
      · intro g
        rfl
      · intro z
        exact (hbz z).symm

/-- Exactness is proved for the original continuous H1-to-H2 connecting map
and original coefficient H2 map; it is not an assumed cohomological interface. -/
theorem continuousConnectingH2_range_eq_ker :
    LinearMap.range
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) =
        LinearMap.ker (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) := by
  ext x
  exact continuousConnectingH2_mem_range_iff A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC x

end
end Dubon2026
