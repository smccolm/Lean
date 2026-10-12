import Dubon2026.ConnectingCupAdjunctionBoundary
import Dubon2026.ContinuousInvariantH2Pairing

/-! # Cup adjunction for the original continuous connecting maps

The actual H1-to-H2 connecting map is adjoint to the actual H0-to-H1 map of a
dual coefficient sequence, with the original continuous cup and explicit
coboundary witness. This is a necessary exact-sequence compatibility for the
finite-module local duality used by DUB-17's trace-zero Selmer pairing.
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
  [TopologicalSpace V] [DiscreteTopology V]
  [TopologicalSpace W]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (ι : U →ₗ[R] V) (hι : Function.Injective ι)
  (hιρ : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
  (π : V →ₗ[R] W) (hπ : Function.Surjective π)
  (hπρ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
  (hDualExact : LinearMap.range ι = LinearMap.ker π)
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

include hβ hαβ hγβ hcβ in
/-- The actual continuous connecting maps of dual exact coefficient sequences
are adjoint for the original cup. The equality is in the original continuous
H2 quotient and uses a proved continuous boundary, not an algebraic-only one. -/
theorem continuousConnectingCup_adjunction
    (x : ContinuousRepresentationH1 C hC) (w : W.ρ.invariants) :
    continuousInvariantRightH2Map A W D α hα hcα hA hD w
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) =
      continuousH1Cup C U D γ hγ hcγ hC hU hD x
        (continuousCoefficientInvariantConnectingMap U V W ι hι hιρ π hπ hπρ hDualExact hU hV w) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let b := coefficientConnectingOneLift B C ψ hψ c
    let a := coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c
    let v := exactCoefficientSection π hπ w.val
    let u := coefficientInvariantConnectingCocycle U V W ι hι hιρ π hπ hπρ hDualExact hV w
    let z : C(G, D) := ⟨fun g => β (b g) (V.ρ g v),
      hcβ.comp (b.continuous.prodMk (hV.comp (continuous_id.prodMk continuous_const)))⟩
    rw [continuousCoefficientConnectingMap_mk, continuousInvariantRightH2Map_mk,
      continuousCoefficientInvariantConnectingMap_apply, continuousH1Cup_mk]
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
      (coefficientInvariantConnectingCocycle_map U V W ι hι hιρ π hπ hπρ hDualExact hV w)
      (exactCoefficientSection_rightInverse π hπ w.val) g h

end
end Dubon2026
