import Dubon2026.ContinuousInvariantConnectingMap
import Dubon2026.ContinuousCohomologyRestriction

/-! Restrict the actual continuous invariant connecting class. The native
cocycle uses the same linear section and preimage before and after group
restriction. This is the restriction compatibility needed to compare the
constructed global S-unit dual class with the prescribed local Cartier
classes in DUB-17; no general derived-functor framework is introduced. -/
namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  (A B C : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

/-- The genuine H1 restriction of the invariant connecting class equals
the connecting class of the same invariant in the restricted sequence. -/
theorem continuousInvariantConnecting_restriction (c : C.ρ.invariants) :
    let cH : (restrictedCoefficientRep C j).ρ.invariants := ⟨c.val, fun h => c.property (j h)⟩
    continuousRepresentationH1Restriction A hA j hj
      (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c) =
    continuousCoefficientInvariantConnectingMap
      (restrictedCoefficientRep A j) (restrictedCoefficientRep B j) (restrictedCoefficientRep C j)
      φ hφ (fun h a => hφρ (j h) a) ψ hψ (fun h b => hψρ (j h) b) hExact
      (restrictedCoefficientAction_continuous A j hj hA)
      (restrictedCoefficientAction_continuous B j hj hB) cH := by
  rfl

end
end Dubon2026
