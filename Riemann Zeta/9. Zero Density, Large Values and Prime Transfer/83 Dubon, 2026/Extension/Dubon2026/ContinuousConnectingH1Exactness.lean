import Dubon2026.ContinuousConnectingH2Exactness

/-! # Actual exactness at continuous H1 for the coefficient connecting map -/

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

/-- An actual middle-coefficient H1 class maps to zero under the original
connecting map: its original cocycle is already a continuous lift with zero boundary. -/
theorem continuousConnectingH1_coefficient_image_zero
    (y : ContinuousRepresentationH1 B hB) :
    continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC
      (continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC y) = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | _ b =>
    rw [continuousCoefficientH1Map_mk, continuousCoefficientConnectingMap_mk,
      ← Submodule.Quotient.mk_zero]
    apply coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (continuousCoefficientCocycleOneMap B C ψ continuous_of_discreteTopology hψρ b)
      0 ⟨b.val, b.property⟩
    · intro g
      rfl
    · intro z
      change φ 0 = (groupCohomology.d₁₂ B b.val) z
      rw [map_zero, groupCohomology.cocycles₁.d₁₂_apply]
      rfl

include hcφ in
/-- Vanishing of the original connecting class gives an actual middle-coefficient
cocycle lift. Subtract the image of its genuine continuous coboundary witness
from the chosen lift; the new lift has zero original differential. -/
theorem continuousConnectingH1_mem_range_iff (x : ContinuousRepresentationH1 C hC) :
    x ∈ LinearMap.range
      (continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC) ↔
        continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact continuousConnectingH1_coefficient_image_zero A B C φ hφ hφρ ψ hψ hψρ
      hExact hA hB hC y
  · induction x using Submodule.Quotient.induction_on with
    | _ c =>
      intro hx
      rw [continuousCoefficientConnectingMap_mk] at hx
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      let s := coefficientConnectingOneLift B C ψ hψ c
      let t : C(G, B) := ⟨fun g => φ (w g), hcφ.comp w.continuous⟩
      have hs : continuousRepresentationCoboundaryTwo B hB s =
          continuousCoefficientCocycleTwoMap A B φ hcφ hφρ
            (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) := by
        apply Subtype.ext
        apply Subtype.ext
        funext z
        exact (coefficientConnectingTwoCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c z).symm
      have ht : continuousRepresentationCoboundaryTwo B hB t =
          continuousCoefficientCocycleTwoMap A B φ hcφ hφρ
            (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) := by
        rw [← continuousCoefficientCocycleTwoMap_coboundary A B φ hcφ hφρ hA hB w, hw]
      have hdb : continuousRepresentationCoboundaryTwo B hB (s - t) = 0 := by
        rw [map_sub, hs, ht, sub_self]
      let b : continuousRepresentationCocyclesOne B :=
        ⟨⟨s - t, by
          apply (groupCohomology.mem_cocycles₁_def _).mpr
          intro g h
          exact congrArg (fun d : continuousRepresentationCocyclesTwo B => d.val (g, h)) hdb⟩,
          (s - t).continuous⟩
      have hzero : ∀ v : A, ψ (φ v) = 0 := by
        intro v
        have hv := LinearMap.mem_range_self φ v
        rw [hExact] at hv
        exact hv
      have hb : continuousCoefficientCocycleOneMap B C ψ continuous_of_discreteTopology hψρ b = c := by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change ψ (s g - φ (w g)) = c.val g
        rw [map_sub, hzero, sub_zero, coefficientConnectingOneLift_project]
      refine ⟨Submodule.Quotient.mk b, ?_⟩
      rw [continuousCoefficientH1Map_mk, hb]

include hcφ in
/-- The actual quotient-coefficient H1 map has precisely the kernel of the
original continuous connecting map as its range. -/
theorem continuousConnectingH1_range_eq_ker :
    LinearMap.range (continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC) =
      LinearMap.ker
        (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) := by
  ext x
  exact continuousConnectingH1_mem_range_iff A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC x

end
end Dubon2026
