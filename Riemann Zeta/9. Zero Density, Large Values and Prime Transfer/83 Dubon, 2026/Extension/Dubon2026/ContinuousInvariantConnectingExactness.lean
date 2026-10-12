import Dubon2026.ContinuousInvariantConnectingMap
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Exactness of the original continuous H0-to-H1 sequence

These actual lift and coboundary arguments discharge exactness at the two
low-degree terms used by cup adjunction in DUB-17's local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [ContinuousSMul R B] in
/-- The original connecting class vanishes exactly when the actual invariant
coefficient has an invariant lift through the original quotient. -/
theorem continuousInvariantConnecting_eq_zero_iff (c : C.ρ.invariants) :
    continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c = 0 ↔
      ∃ b : B.ρ.invariants, ψ b.val = c.val := by
  constructor
  · intro hc
    rw [continuousCoefficientInvariantConnectingMap_apply] at hc
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
    let b₀ := exactCoefficientSection ψ hψ c.val
    have hz : ψ (φ v) = 0 := by
      have hr := LinearMap.mem_range_self φ v
      rw [hExact] at hr
      exact hr
    have hb : ∀ g, B.ρ g (b₀ - φ v) = b₀ - φ v := by
      intro g
      have hh := congrArg (fun f : continuousRepresentationCocyclesOne A => φ (f.val g)) hv
      change φ (A.ρ g v - v) =
        φ ((coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val g) at hh
      rw [map_sub, hφρ, coefficientInvariantConnectingCocycle_map] at hh
      change B.ρ g (φ v) - φ v = B.ρ g b₀ - b₀ at hh
      rw [map_sub]
      calc
        B.ρ g b₀ - B.ρ g (φ v) =
            b₀ - φ v + ((B.ρ g b₀ - b₀) - (B.ρ g (φ v) - φ v)) := by abel
        _ = b₀ - φ v := by rw [hh, sub_self, add_zero]
    refine ⟨⟨b₀ - φ v, hb⟩, ?_⟩
    rw [map_sub, hz, sub_zero, exactCoefficientSection_rightInverse]
  · rintro ⟨b, hb⟩
    rw [continuousCoefficientInvariantConnectingMap_apply, ← Submodule.Quotient.mk_zero]
    apply coefficientInvariantConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      c 0 b.val hb
    intro g
    change φ 0 = B.ρ g b.val - b.val
    rw [map_zero, b.property g, sub_self]

/-- Inclusion sends the original invariant connecting class to the coboundary
of its original chosen lift, so its actual middle-coefficient H1 class is zero. -/
theorem continuousInvariantConnecting_image_zero (hcφ : Continuous φ) (c : C.ρ.invariants) :
    continuousCoefficientH1Map A B φ hcφ hφρ hA hB
      (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c) = 0 := by
  rw [continuousCoefficientInvariantConnectingMap_apply, continuousCoefficientH1Map_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨exactCoefficientSection ψ hψ c.val, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact (coefficientInvariantConnectingCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c g).symm

/-- Every original H1 class killed by inclusion is the connecting class of an
actual invariant quotient coefficient, derived from its coboundary witness. -/
theorem continuousInvariantConnecting_mem_range_iff (hcφ : Continuous φ)
    (x : ContinuousRepresentationH1 A hA) :
    x ∈ LinearMap.range
      (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB) ↔
        continuousCoefficientH1Map A B φ hcφ hφρ hA hB x = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    exact continuousInvariantConnecting_image_zero A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hcφ c
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
      intro hx
      rw [continuousCoefficientH1Map_mk] at hx
      obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      have ha : ∀ g, φ (a.val g) = B.ρ g b - b := fun g =>
        (congrArg (fun f : continuousRepresentationCocyclesOne B => f.val g) hb).symm
      have hi : ∀ g, C.ρ g (ψ b) = ψ b := by
        intro g
        have hz : ψ (φ (a.val g)) = 0 := by
          have hr := LinearMap.mem_range_self φ (a.val g)
          rw [hExact] at hr
          exact hr
        rw [ha, map_sub, hψρ] at hz
        exact sub_eq_zero.mp hz
      let c : C.ρ.invariants := ⟨ψ b, hi⟩
      refine ⟨c, ?_⟩
      rw [continuousCoefficientInvariantConnectingMap_apply]
      exact coefficientInvariantConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
        c a b rfl ha

end
end Dubon2026
