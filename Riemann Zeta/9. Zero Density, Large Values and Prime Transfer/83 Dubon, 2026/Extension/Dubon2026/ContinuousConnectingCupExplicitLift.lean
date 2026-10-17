import Dubon2026.ConnectingCupAdjunctionBoundary
import Dubon2026.ContinuousInvariantH2Pairing

/-! # Continuous cup adjunction from the actual explicit lift

Use the already proved cochain boundary with one specified lift. This
removes unnecessary dual-sequence exactness from the source-class comparison
needed for DUB-17 reverse localization, while retaining the continuous H2
quotient and its actual boundary witness.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C U V W D : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul R U]
  [TopologicalSpace V]
  [TopologicalSpace W]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (ι : U →ₗ[R] V)
  (hιρ : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
  (π : V →ₗ[R] W)
  (hπρ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
  (α : A →ₗ[R] W →ₗ[R] D) (β : B →ₗ[R] V →ₗ[R] D)
  (γ : C →ₗ[R] U →ₗ[R] D)
  (hα : ∀ g a w, α (A.ρ g a) (W.ρ g w) = D.ρ g (α a w))
  (hβ : ∀ g b v, β (B.ρ g b) (V.ρ g v) = D.ρ g (β b v))
  (hγ : ∀ g c u, γ (C.ρ g c) (U.ρ g u) = D.ρ g (γ c u))
  (hαβ : ∀ a v, β (φ a) v = α a (π v))
  (hγβ : ∀ b u, β b (ι u) = γ (ψ b) u)
  (hcα : Continuous (fun z : A × W => α z.1 z.2))
  (hcβ : Continuous (fun z : B × V => β z.1 z.2))
  (hcγ : Continuous (fun z : C × U => γ z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (hU : Continuous (fun z : G × U => U.ρ z.1 z.2))
  (hV : Continuous (fun z : G × V => V.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

include hβ hαβ hγβ hcβ hιρ hπρ hV in
/-- A specified continuous cocycle and its actual lift give cup adjunction
in the original continuous H2 quotient. No exactness of the dual sequence
is required for this identity. -/
theorem continuousConnectingCup_explicit_lift
    (x : ContinuousRepresentationH1 C hC) (w : W.ρ.invariants)
    (u : continuousRepresentationCocyclesOne U) (v : V)
    (hu : ∀ g, ι (u.val g) = V.ρ g v - v) (hv : π v = w.val) :
    continuousInvariantRightH2Map A W D α hα hcα hA hD w
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) =
      continuousH1Cup C U D γ hγ hcγ hC hU hD x
        (Submodule.Quotient.mk u) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let b := coefficientConnectingOneLift B C ψ hψ c
    let a := coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c
    let z : C(G, D) := ⟨fun g => β (b g) (V.ρ g v),
      hcβ.comp (b.continuous.prodMk (hV.comp (continuous_id.prodMk continuous_const)))⟩
    rw [continuousCoefficientConnectingMap_mk, continuousInvariantRightH2Map_mk,
      continuousH1Cup_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext gh
    rcases gh with ⟨g, h⟩
    change groupCohomology.d₁₂ D (fun t => β (b t) (V.ρ t v)) (g, h) =
      α (a.val (g, h)) w.val - γ (c.val g) (U.ρ g (u.val h))
    exact connectingCupAdjunction_boundary A B C U V W D φ ψ ι π hιρ hπρ α β γ
      hβ hαβ hγβ b a.val c.val u.val v w
      (coefficientConnectingOneLift_project B C ψ hψ c)
      (fun g h => coefficientConnectingTwoCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c (g, h))
      hu hv g h

end
end Dubon2026
